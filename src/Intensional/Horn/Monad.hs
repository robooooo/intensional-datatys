{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Intensional.Horn.Monad where

import           Control.Monad.RWS.Strict
import qualified Data.Map                      as Map
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set
import           DataCon                        ( dataConName )
import           GHC
import           GhcPlugins                     ( mkFastString )
import           Intensional.Constraints hiding ( guardWith )
import           Intensional.Guard              ( singleton )
import           Intensional.Horn.Clause
import           Intensional.Horn.Constraint
import           Intensional.InferM             ( BaseContext
                                                , InferEnv(..)
                                                , Stats(..)
                                                , MonadInfer(..)
                                                , MonadInferState(..)
                                                , Stats(..)
                                                , _d
                                                , _i
                                                , _k
                                                , _n
                                                , _rv
                                                )
import           Intensional.Scheme
import           Intensional.Types
import           Lens.Micro



type InferM = RWS (InferEnv HornSet) HornSet Stats

instance MonadInferState InferM where
    mfresh = fresh
    noteK x = modify $ over _k (max x)
    noteD x = modify $ over _d (max x)
    noteI x = modify $ over _i (max x)
    incrN = modify $ over _n (+ 1)

instance (MonadInfer HornSet) InferM where
    memitDD = emitDD
    memitDK = emitDK
    memitKD = emitKD

type HornContext = BaseContext HornSet

runInferM :: InferM a -> Module -> HornContext -> (a, HornSet, Stats)
runInferM run mod_name init_env =
    let (a, s, w) = runRWS
            run
            (InferEnv mod_name init_env (UnhelpfulSpan (mkFastString "Nowhere"))
            )
            (Stats 0 0 0 0 0)
    in  (a, Set.empty, s)

-- | Create a fresh refinement variable.
fresh :: InferM RVar
fresh = do
    i <- gets rVar
    modify $ over _rv (+ 1)
    return i

-- | Insert a variable into environment.
putVar :: Name -> HornScheme -> InferM a -> InferM a
putVar n s = local (\env -> env { varEnv = Map.insert n s (varEnv env) })

-- | Insert variables into environment.
putVars :: HornContext -> InferM a -> InferM a
putVars ctx = local (\env -> env { varEnv = Map.union ctx (varEnv env) })

-- Add source text location tick
setLoc :: SrcSpan -> InferM a -> InferM a
setLoc l = local (\env -> env { inferLoc = l })


-- |Given a list of data constructors @ks@, a datatype @Inj x d@ and an 
-- inference action @m@, @branchAny ks (Inj x d) m@ is the inference action
-- that consists of doing @m@ then guarding all emitted constraints by the
-- requirement that @ks in x(d)@.
branchAny :: [DataCon] -> DataType TyCon -> InferM a -> InferM a
branchAny _ (Base _) m = m
branchAny ks (Inj x d) m | typeIsTrivial d = m
                         | otherwise       = censor guardWithAll m
  where
    dn = getName d
    guardWithAll cs =
        foldMap (\k -> guardHornWith (singleton [getName k] x dn) cs) ks

typeIsTrivial :: TyCon -> Bool
typeIsTrivial tc = length (tyConDataCons tc) == 1

addLabel :: Horn Atom -> InferM HornConstraint
addLabel horn =
    HornConstraint <$> (CInfo <$> asks modName <*> asks inferLoc) <*> pure horn

addLabels :: Set (Horn Atom) -> InferM HornSet
addLabels horns = do
    m <- asks modName
    s <- asks inferLoc
    return $ Set.map (HornConstraint (CInfo m s)) horns

emitDD :: DataType TyCon -> DataType TyCon -> InferM ()
emitDD (Inj x d) (Inj y _) = unless (typeIsTrivial d) $ do
    let ks = getName <$> tyConDataCons d
        dn = getName d
-- a <- mkConFromCtx (Dom (Inj x dn)) (Dom (Inj y dn))
        con =
            toHorn (Set.fromList ks) $ Set.empty ? (Refined x dn, Refined y dn)
    (addLabels >=> tell) con
emitDD _ _ = return ()

emitKD :: DataCon -> SrcSpan -> DataType TyCon -> InferM ()
emitKD k s (Inj x d) = unless (typeIsTrivial d) $ do
    let ks = getName <$> tyConDataCons d
        dn = getName d
        kn = getName k
-- a <- mkConFromCtx (Con kn s) (Dom (Inj x dn))
        con =
            toHorn (Set.fromList ks)
                $ Set.empty
                ? (Constructors $ Set.singleton kn, Refined x dn)
    (addLabels >=> tell) con
emitKD _ _ _ = return ()

emitDK :: DataType TyCon -> [DataCon] -> SrcSpan -> InferM ()
emitDK (Inj x d) ks s =
    unless (typeIsTrivial d || length (tyConDataCons d) == length ks) $ do
        let ksFull = dataConName <$> tyConDataCons d
            ksSubs = Set.fromList $ fmap getName ks
            dn     = getName d
-- a <- mkConFromCtx (Dom (Inj x dn)) (Set ksn s)
            con =
                toHorn (Set.fromList ksFull)
                    $ Set.empty
                    ? (Refined x dn, Constructors ksSubs)
        (addLabels >=> tell) con
emitDK _ _ _ = return ()
