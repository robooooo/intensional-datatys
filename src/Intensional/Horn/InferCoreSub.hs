module Intensional.Horn.InferCoreSub
    ( inferSubType
    ) where

import           Control.Monad.Extra
import           Control.Monad.RWS.Strict
import           Control.Monad.State            ( StateT )
import qualified Control.Monad.State           as State
import           Data.List                      ( nub )
import qualified Data.Set                      as Set
import           Debug.Trace
import           GhcPlugins              hiding ( (<>)
                                                , Type
                                                )
import           Intensional.FromCore           ( consInstArgs )
import           Intensional.Guard
import qualified Intensional.Guard             as Guard
import           Intensional.Horn.Constraint    ( guardHornWith )
import           Intensional.Horn.Monad
import           Intensional.InferM             ( InferEnv(..)
                                                , MonadInferState(..)
                                                )
import           Intensional.Types
import           Intensional.Ubiq

{- |
    The type of subtype inference constraints that are accumulated
    during the subtype inference fixpoint algorithm.

    There is a 1-1 correspondence between this type and the type of
    atomic constraints, but the former contain more information
    (though this information could be determined by the context at
    great expense).
-}
type SubTyAtom = (Guard, RVar, RVar, TyCon)

{- |
    The type of elements of the frontier in the subtype inference fixpoint
    algorithm.  There is an injection from this type into the typ of atomic
    constraints, but the inhabitants of this type additionally track the
    types used to instantiate the constructors of the datatype involved in
    the constraint.  This additional information is needed to unfold the
    frontier and look for successors.
-}
type SubTyFrontierAtom = (Guard, RVar, RVar, TyCon, [Type], [Type])

{- |
    The type of the subtype inference algorithm, i.e. a stateful fixed
    point computation that must additionally draw upon the services of
    the inference monad to deal with GHC types.
-}
type SubTyComputation = StateT ([SubTyFrontierAtom], [SubTyAtom]) InferM ()

{- |
    Given a pair of types @t1@ and @t2@, @inferSubType t1 t2@ is the action
    that emits constraints characterising @t1 <= t2@.

    Also emits statistics on the size of the input parameters to do with slices.
-}
inferSubType :: Type -> Type -> InferM ()
inferSubType t1 t2 = do
    let ts = inferSubTypeStep t1 t2
    (_, cs) <- listen $ forM_ ts $ \(x, y, d, as, as') -> do
            -- Entering a slice
        ds <- snd <$> State.execStateT
            inferSubTypeFix
            ([(mempty, x, y, d, as, as')], [(mempty, x, y, d)])
        -- Note how big it was for statistics
        noteD $ length (nub $ map (\(_, _, _, d') -> getName d') ds)
        -- Emit a constraint for each one
        forM_ ds $ \(gs, x', y', d') ->
            censor (guardHornWith gs) (emitDD (Inj x' d') (Inj y' d'))

    when debugging $ do
        src <- asks inferLoc
        traceM ("[TRACE] Starting subtype inference at " ++ traceSpan src)
        let sz = Set.size cs
        traceM
            (  "[TRACE] The subtype proof at "
            ++ traceSpan src
            ++ " contributed "
            ++ show sz
            ++ " constraints."
            )
  where
    leq :: SubTyAtom -> SubTyAtom -> Bool
    leq (gs, x, y, d) (gs', x', y', d') =
        -- getName here is probably unnecessary, should look it up
        x
            ==                x'
            &&                y
            ==                y'
            &&                getName d
            ==                getName d'
            &&                gs'
            `Guard.impliedBy` gs

    inferSubTypeFix :: SubTyComputation
    inferSubTypeFix = do
        (frontier, acc) <- get
        unless (null frontier) $ do
            put ([], acc)
            forM_ frontier $ \(gs, x, y, d, as, as') -> do
                let dataCons = tyConDataCons d
                lift $ noteK (length dataCons)
                forM_ dataCons $ \k -> do
                    xtys <- lift $ consInstArgs x as k
                    ytys <- lift $ consInstArgs y as' k
                    let gs' = if typeIsTrivial d
                            then gs
                            else Guard.singleton [getName k] x (getName d) <> gs
                    let ts = concat $ zipWith inferSubTypeStep xtys ytys
                    forM_ ts $ \(x', y', d', bs, bs') -> do
                        let new  = (gs', x', y', d')
                        let newF = (gs', x', y', d', bs, bs')
                        (fr, ac) <- get
                        unless (any (`leq` new) ac) $ put (newF : fr, new : ac)
            inferSubTypeFix

    inferSubTypeStep :: Type -> Type -> [(RVar, RVar, TyCon, [Type], [Type])]
    inferSubTypeStep (Data (Inj x d) as) (Data (Inj y _) as') =
        [(x, y, d, as, as')]
    inferSubTypeStep (t11 :=> t12) (t21 :=> t22) =
        let ds1 = inferSubTypeStep t21 t11
            ds2 = inferSubTypeStep t12 t22
        in  ds1 ++ ds2
    inferSubTypeStep (Data (Base _) as) (Data (Base _) as') =
        concat $ zipWith inferSubTypeStep as as'
    inferSubTypeStep _ _ = []
