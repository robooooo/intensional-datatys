{-# LANGUAGE MultiParamTypeClasses, TemplateHaskell #-}
module Intensional.InferM where

import           Control.Monad.RWS.Strict
                                         hiding ( guard )
import qualified Data.IntSet                   as IntSet
import qualified Data.Map                      as M
import           GhcPlugins              hiding ( (<>)
                                                , singleton
                                                )
import           Intensional.Constraints       as Constraints
import           Intensional.Constructors
import           Intensional.Guard
import           Intensional.Scheme
import           Intensional.Types
import           Intensional.Ubiq
import           Lens.Micro
import           Lens.Micro.Extras
import           Lens.Micro.TH                  ( makeLensesFor )


data Stats = Stats
    { maxK :: Int
    , maxD :: Int
    , maxI :: Int
    , cntN :: Int
    , rVar :: Int
    }

makeLensesFor
    [ ("maxK", "_k")
    , ("maxD", "_d")
    , ("maxI", "_i")
    , ("cntN", "_n")
    , ("rVar", "_rv")]
    ''Stats

data InferState con = InferState
    { stats :: Stats
    , errs  :: con
    }

makeLensesFor
    [("stats", "_stats"), ("errs", "_errs")]
    ''InferState

type InferM
    = RWS (InferEnv ConstraintSet) ConstraintSet (InferState ConstraintSet)

class Monad m => MonadInferState m where
    mfresh :: m RVar
    noteK  :: Int -> m ()
    noteD  :: Int -> m ()
    noteI  :: Int -> m ()
    incrN  :: m ()

-- | State component of @MonadInfer@. Because the two use differently shaped
-- state types, this represents the common intersection of them.
-- (Namely, creating fresh refinement variables).
-- Should probably include debugging in future too?
instance MonadInferState InferM where
    mfresh = fresh
    noteK x = modify $ over (_stats . _k) (max x)
    noteD x = modify $ over (_stats . _d) (max x)
    noteI x = modify $ over (_stats . _i) (max x)
    incrN = modify $ over (_stats . _n) (+ 1)

-- | Generalise over both types of inference monads.
class (MonadWriter con m, MonadReader (InferEnv con) m, MonadInferState m)
        => MonadInfer con m where
    memitDD :: DataType TyCon -> DataType TyCon -> m ()
    memitKD :: DataCon -> SrcSpan -> DataType TyCon -> m ()
    memitDK :: DataType TyCon -> [DataCon] -> SrcSpan -> m ()

instance (MonadInfer ConstraintSet) InferM where
    memitDD = emitDD
    memitKD = emitKD
    memitDK = emitDK

-- | The type of contexts where type schemes have constraints of type @con@.
type BaseContext con = M.Map Name (SchemeGen con TyCon)
type Context = BaseContext ConstraintSet

-- | Constraint types of type @con@.
data InferEnv con = InferEnv
    { modName  :: Module
    -- The current module
    , varEnv   :: BaseContext con
    -- The current location in the source text
    , inferLoc :: SrcSpan
    }

initState :: InferState ConstraintSet
initState = InferState (Stats 0 0 0 0 0) mempty

{-|
  Given a set of trivially unsatisfiable constraints @es@,
  @noteErrs es@ is the action that records them
  in the accumulating set in the inference state.
-}
noteErrs :: ConstraintSet -> InferM ()
noteErrs es = modify (\s -> s { errs = es <> errs s })

runInferM :: InferM a -> Module -> Context -> (a, [Atomic], Stats)
runInferM run mod_name init_env =
    let (a, s, _) = runRWS
            run
            (InferEnv mod_name init_env (UnhelpfulSpan (mkFastString "Nowhere"))
            )
            initState
        stat = stats s
    in  ( a
        , Constraints.toList (errs s)
        , Stats (maxK stat) (maxD stat) (rVar stat) (maxI stat) (cntN stat)
        )

-- Transitively remove local constraints
saturate :: Refined a => InferM a -> InferM a
saturate ma = pass $ do
    a   <- ma
    env <- asks varEnv
    m   <- asks modName
    src <- asks inferLoc
    let interface = domain a <> domain env
    noteI (IntSet.size interface)
    let fn cs =
            let ds = Constraints.saturate (CInfo m src) interface cs
            in  if debugging then debugBracket a env src cs ds else ds
    return (a, fn)
  where
    debugBracket a env src cs ds =
        let
            asz = "type: " ++ show (IntSet.size $ domain a)
            esz = "env: " ++ show (IntSet.size $ domain env)
            csz = show (size cs)
            spn = traceSpan src
            tmsg =
                "#interface = ("
                    ++ asz
                    ++ " + "
                    ++ esz
                    ++ "), #constraints = "
                    ++ csz
            ds' =
                trace ("[TRACE] BEGIN saturate at " ++ spn ++ ": " ++ tmsg) ds
        in
            ds'
                `seq` trace
                          (  "[TRACE] END saturate at "
                          ++ spn
                          ++ " saturated size: "
                          ++ show (size ds)
                          )
                          ds

{-|
    Given a constraint set @cs@, @cexs cs@ is the inference action that
    attempts to build a model of @cs@ and returns the set of counterexamples.
-}
cexs :: ConstraintSet -> InferM ConstraintSet
cexs cs = do
    m   <- asks modName
    src <- asks inferLoc
    return $ Constraints.cexs (CInfo m src) cs

-- Check if a core datatype is ineligible for refinement
isIneligible :: MonadInfer con m => TyCon -> m Bool
isIneligible tc = do
    m <- asks modName
    return (not (homeOrBase m (getName tc)) || null (tyConDataCons tc))
    where homeOrBase m n = nameIsHomePackage m n

        -- Previously we tried to include as much of base as possible by asking for specific modules
        -- but this is a little too coarse grain (e.g. GHC.Types will include Bool, but also Int):
        --
        -- vc|| ( not (nameIsFromExternalPackage baseUnitId n && nameIsFromExternalPackage primUnitId n)
        --        && case nameModule_maybe n of
        --          Nothing -> False
        --          Just (Module _ m) ->
        --            List.isPrefixOf "Prelude" (moduleNameString m)
        --              || List.isPrefixOf "Data" (moduleNameString m)
        --              || List.isPrefixOf "GHC.Base" (moduleNameString m)
        --              || List.isPrefixOf "GHC.Types" (moduleNameString m)
        --    )
        --
        -- a better approach would be, simply:
        --  strName = occNameString (getOccName tc)
        --  ...
        --  || strName == "Bool"
        --  || strName == "Maybe"

isTrivial :: TyCon -> Bool
isTrivial tc = length (tyConDataCons tc) == 1



{- 
  Given a list of data constructors @ks@, a datatype @Inj x d@ and an 
  inference action @m@, @branchAny ks (Inj x d) m@ is the inference action
  that consists of doing @m@ then guarding all emitted constraints
  by the requirement that @ks in x(d)@.
-}
branchAny :: [DataCon] -> DataType TyCon -> InferM a -> InferM a
branchAny _  (Base _ ) m = m
branchAny ks (Inj x d) m = if isTrivial d then m else censor guardWithAll m
  where
    dn = getName d
    guardWithAll cs =
        foldMap (\k -> Constraints.guardWith (singleton [getName k] x dn) cs) ks

mkConFromCtx :: ConL -> ConR -> InferM Atomic
mkConFromCtx l r = do
    m <- asks modName
    s <- asks inferLoc
    return (Constraint l r mempty (CInfo m s))

emitDD :: DataType TyCon -> DataType TyCon -> InferM ()
emitDD (Inj x d) (Inj y _) = unless (isTrivial d) $ do
    a <- mkConFromCtx (Dom (Inj x dn)) (Dom (Inj y dn))
    tell (Constraints.fromList [a])
    where dn = getName d
emitDD _ _ = return ()

emitKD :: DataCon -> SrcSpan -> DataType TyCon -> InferM ()
emitKD k s (Inj x d) = unless (isTrivial d) $ do
    a <- mkConFromCtx (Con kn s) (Dom (Inj x dn))
    tell (Constraints.fromList [a])
  where
    dn = getName d
    kn = getName k
emitKD _ _ _ = return ()

emitDK :: DataType TyCon -> [DataCon] -> SrcSpan -> InferM ()
emitDK (Inj x d) ks s =
    unless (isTrivial d || length (tyConDataCons d) == length ks) $ do
        a <- mkConFromCtx (Dom (Inj x dn)) (Set ksn s)
        tell (Constraints.fromList [a])
  where
    dn  = getName d
    ksn = mkUniqSet (map getName ks)
emitDK _ _ _ = return ()


-- A fresh refinement variable
fresh :: InferM RVar
fresh = do
    i <- gets $ view (_stats . _rv)
    modify $ over (_stats . _rv) (+ 1)
    return i

-- Insert variables into environment
putVar :: Name -> Scheme -> InferM a -> InferM a
putVar n s = local (\env -> env { varEnv = M.insert n s (varEnv env) })

putVars :: Context -> InferM a -> InferM a
putVars ctx = local (\env -> env { varEnv = M.union ctx (varEnv env) })

-- Add source text lo dcation tick
setLoc :: SrcSpan -> InferM a -> InferM a
setLoc l = local (\env -> env { inferLoc = l })

-- Prepare name for interface
-- Should be used before all type variables
getExternalName :: (MonadInfer con m, NamedThing a) => a -> m Name
getExternalName a = do
    let n = getName a
    mn <- asks modName
    return $ mkExternalName (nameUnique n) mn (nameOccName n) (nameSrcSpan n)
