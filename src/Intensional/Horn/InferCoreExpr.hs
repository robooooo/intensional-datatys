{-# LANGUAGE TupleSections #-}
module Intensional.Horn.InferCoreExpr
    ( inferProg
    ) where

import           Control.Monad.Extra
import           Control.Monad.RWS.Strict
import           CoreArity                      ( exprBotStrictness_maybe )
import qualified CoreSyn                       as Core
import           Data.Bifunctor                 ( Bifunctor(bimap) )
import qualified Data.IntSet                   as I
import qualified Data.IntSet                   as IS
import qualified Data.List                     as List
import qualified Data.Map                      as Map
import qualified Data.Set                      as Set
import           GhcPlugins              hiding ( (<>)
                                                , Type
                                                )
import           Intensional.Constraints        ( CInfo(..) )
import           Intensional.FromCore
import           Intensional.Horn.Clause
import           Intensional.Horn.Constraints
import           Intensional.Horn.InferCoreSub
import           Intensional.Horn.Monad
import           Intensional.InferM             ( InferEnv(..)
                                                , MonadInferState(..)
                                                , _errs
                                                , getExternalName
                                                )
import           Intensional.Scheme            as Scheme
import           Intensional.Types
import           Intensional.Ubiq
import           Lens.Micro
import           Lens.Micro.Extras
import           Pair

-- | Saturate and restrict every element of the @Writer@ environment.
saturateRestrict :: Refined a => InferM a -> InferM a
saturateRestrict ma = pass $ do
    a   <- ma
    env <- asks varEnv
    m   <- asks modName
    src <- asks inferLoc
    let interface = domain a <> domain env
    -- noteI (IntSet.size interface)
    return (a, satRes (CInfo m src) interface)
  where
    satRes ci iface cs =
        Set.filter (\hc -> domain hc `IS.isSubsetOf` iface) (saturateCons ci cs)

-- Infer constraints for a module
inferProg :: CoreProgram -> InferM HornContext
inferProg []       = return Map.empty
inferProg (r : rs) = do
    let bs = map occName $ bindersOf r
    ctx  <- if any isDerivedOccName bs then return mempty else associate r
    ctxs <- putVars ctx (inferProg rs)
    return (ctxs <> ctx)

triviallyUnsat :: HornSet -> HornSet
triviallyUnsat = Set.filter $ (== Horn Nothing Set.empty) . view _horn

-- Infer a set of constraints and associate them to qualified type scheme
associate :: CoreBind -> InferM HornContext
associate r = setLoc
    (UnhelpfulSpan (mkFastString ("Top level " ++ bindingNames)))
    doAssoc
  where
    bindingNames :: String
    bindingNames = show $ map (occNameString . occName) (bindersOf r)

    doAssoc :: InferM HornContext
    doAssoc = do
        debugTrace ("Begin inferring: " ++ bindingNames)
        env       <- asks varEnv
        (ctx, cs) <- listen $ inferRec r
        debugTrace $ "cs is " ++ traceRefined cs

        -- add constraints to every type in the recursive group
        ctx' <- mapM (satAction cs env) ctx
        debugTrace $ "ctx' is " ++ traceRefined ctx'

        -- note down any counterexamples
        let es = triviallyUnsat $ Set.unions (constraints <$> Map.elems ctx')
        debugTrace $ "es is " ++ traceRefined es
        modify $ over _errs (Set.union es)

        debugTrace ("End inferring: " ++ bindingNames)
        incrN
        return ctx'

    satAction :: HornSet -> HornContext -> HornScheme -> InferM HornScheme
    satAction cs env s = do
        -- Attempt to build a model and record counterexamples
        cs' <- snd <$> listen (saturateRestrict (tell cs >> return s))
        debugTrace $ "cs' is " ++ showSDocUnsafe (prpr int cs')
        return $ s { boundvs = (domain cs' <> domain s) I.\\ domain env
                   , Scheme.constraints = cs'
                   }

-- Infer constraints for a mutually recursive binders
inferRec :: CoreBind -> InferM HornContext
inferRec (NonRec x e) = Map.singleton (getName x) <$> infer e
inferRec (Rec xes   ) = do
    binds <- sequence $ Map.fromList $ bimap getName getScheme <$> xes

    -- Add binds for recursive calls
    putVars (fmap snd binds) $ forM binds $ \(e, rec_scheme) -> do
        scheme <- infer e
        -- Bound recursive calls
        -- Must be bidirectional for mututally recursive groups
        inferSubType (body scheme)     (body rec_scheme)
        inferSubType (body rec_scheme) (body scheme)
        return scheme
    where getScheme e = (e, ) <$> freshCoreScheme (exprType e)



-- Infer constraints for a program expression
infer :: CoreExpr -> InferM HornScheme
-- Check if identifier is a constructor
infer (Core.Var v) = case isDataConId_maybe v of
    -- Ignore typeclass evidence
    Just k | isClassTyCon (dataConTyCon k) -> return (Forall [] Ambiguous)
           | otherwise                     -> fromCoreCons k
    Nothing -> getVar v

infer l@(Core.Lit _                ) = freshCoreScheme $ exprType l

infer (  Core.App e1 (Core.Type e2)) = do
    t      <- freshCoreType e2
    scheme <- infer e1
    case scheme of
        Forall (a : as) b -> return $ Forall as (subTyVar a t b) -- Type application
        Forall [] Ambiguous -> return (Forall [] Ambiguous)
        _ -> pprPanic "Type application to monotype!" (ppr (scheme, e2))

infer (Core.App e1 e2) = saturateRestrict
    (infer e1 >>= \case
        Forall as Ambiguous   -> Forall as Ambiguous <$ infer e2
        -- See FromCore 88 for the case when as /= []
        Forall as (t3 :=> t4) -> do
            t2 <- mono <$> infer e2
            inferSubType t2 t3
            return $ Forall as t4
        _ -> pprPanic "The expression has been given too many arguments!"
            $ ppr (exprType e1, exprType e2)
    )

infer (Core.Lam x e)
    | isTyVar x = do
        a <- getExternalName x
        infer e >>= \case
            Forall as t -> return $ Forall (a : as) t
    | -- Type abstraction
      otherwise = do
        t1 <- freshCoreType (varType x)
        putVar (getName x) (Forall [] t1) (infer e) >>= \case
            Forall as t2 -> return $ Forall as (t1 :=> t2)

infer (Core.Let b e) = saturateRestrict $ do
    ts <- associate b
    putVars ts $ infer e

infer (Core.Case e bind_e core_ret alts) = saturateRestrict $ do
    -- Fresh return type
    ret <- freshCoreType core_ret
    -- Infer expression on which to pattern match
    t0  <- mono <$> infer e
    -- Add the variable under scrutinee to scope
    putVar (getName bind_e) (Forall [] t0) $ case t0 of
        Data dt as -> do
            ks <- mapMaybeM
                (\case
                    (Core.DataAlt k, xs, rhs) | not (isBottoming rhs) -> do
                        -- Add constructor arguments introduced by the pattern
                        y  <- fresh -- only used in Base case of ts
                        ts <- case dt of
                            Inj x _ ->
                                Map.fromList
                                    .   zip (fmap getName xs)
                                    <$> (map (Forall []) <$> consInstArgs x as k
                                        )
                            Base _ ->
                                Map.fromList
                                    .   zip (fmap getName xs)
                                    <$> (map (Forall []) <$> consInstArgs y as k
                                        )
                        branchAny [k] dt $ do
                            -- Ensure return type is valid
                            ret_i <- mono <$> putVars ts (infer rhs)
                            inferSubType ret_i ret
                        -- Record constructorsc
                        return (Just k)
                    (Core.LitAlt _, _, rhs) | not (isBottoming rhs) -> do
                        -- Ensure return type is valid
                        ret_i <- mono <$> infer rhs
                        inferSubType ret_i ret
                        -- Record constructors
                        return Nothing
                    _ -> return Nothing -- Skip defaults until all constructors have been seen
                )
                alts
            case findDefault alts of
                (_, Just rhs) | not (isBottoming rhs) ->
                    -- Guard by unseen constructors
                    branchAny (tyConDataCons (tyconOf dt) List.\\ ks) dt $ do
                        -- Ensure return type is valid
                        ret_i <- mono <$> infer rhs
                        inferSubType ret_i ret
                _ | (Inj x d) <- dt -> do
                    -- Ensure destructor is total if not nested
                    l <- asks inferLoc
                    emitDK (Inj x d) ks l
                _ -> return ()
        _ -> forM_ alts $ \(_, xs, rhs) -> do
            -- Add constructor arguments introduced by the pattern
            ts <- sequence $ Map.fromList $ zip
                (fmap getName xs)
                (fmap (freshCoreScheme . varType) xs)
            -- Ensure return type is valid
            ret_i <- mono <$> putVars ts (infer rhs)
            inferSubType ret_i ret

    return (Forall [] ret)

infer (Core.Cast e g) = do
    _ <- infer e
    freshCoreScheme (pSnd $ coercionKind g)

infer (Core.Tick SourceNote { sourceSpan = s } e) =
    setLoc (RealSrcSpan s) $ infer e -- Track location in source text
infer (Core.Tick _ e  ) = infer e -- Ignore other ticks
infer (Core.Coercion g) = freshCoreScheme (pSnd $ coercionKind g)
infer (Core.Type     t) = pprPanic "Unexpected type" (ppr t)

isBottoming :: CoreExpr -> Bool
isBottoming e = case exprBotStrictness_maybe e of
    Nothing     -> exprIsBottom e
    Just (_, _) -> True

