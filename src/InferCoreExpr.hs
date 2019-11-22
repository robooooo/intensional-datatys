{-# LANGUAGE FlexibleInstances, BangPatterns #-}

module InferCoreExpr
    (
      inferProg
    ) where

import Control.Arrow
import Control.Monad.RWS hiding (Sum)

import Data.Time
import Data.Functor.Identity
import Data.Maybe
import qualified Data.List as L

import Kind
import ToIface
import qualified GhcPlugins as Core
import qualified PrimOp as Prim
import qualified TyCoRep as Tcr
import qualified TyCon as Tc

import Types
import InferM
import ConGraph

-- Add restricted constraints to an unquantifed type scheme
quantifyWith :: ConGraph -> [TypeScheme] -> InferM [TypeScheme]
quantifyWith cg@ConGraph{subs = sb} ts = do

  -- Rewrite ts using equivalence class representations
  let ts' = [Forall as [] [] (subRefinementMap sb u) | Forall as _ [] u <- ts]

  -- Stems which occur in the interface
  let interfaceStems = [s | (Forall _ _ _ u) <- ts', s <- stems u]
  -- !() <- Core.pprTraceM "Stems of: " (Core.ppr (interfaceStems, ts'))

  -- Intermediate nodes
  let intermediateStems = L.nub ([s | (_, t1, _) <- toList cg, s <- stems t1, s `notElem` interfaceStems] 
                              ++ [s | (_, _, t1) <- toList cg, s <- stems t1, s `notElem` interfaceStems])

  -- Take the full transitive closure of the graph using rewriting rules
  (m, lcg) <- saturate interfaceStems intermediateStems cg

  -- Quantify over all refinement variables that have stems from the inferface
  let nodes = L.nub ([x1 | (_, Var x1, _) <- lcg] 
                  ++ [x2 | (_, _, Var x2) <- lcg] 
                  ++ catMaybes [subTypesRVar m v | Forall _ _ _ u <- ts', v <- vars u])

  -- Quantify over all type variables appearing in the constraint graph
  let tyvars = [v | n <- nodes, v <- tvarsR n]

  return [Forall (L.nub (as ++ tyvars)) nodes lcg (subTypesType m u) | Forall as _ _ u <- ts']





-- List all free variables in an expression
freeVars :: Core.Expr Core.Var -> [Core.Name]
freeVars (Core.Var i)         = [Core.getName i]
freeVars (Core.Lit _)         = []
freeVars (Core.App e1 e2)     = freeVars e1 ++ freeVars e2
freeVars (Core.Lam x e)       = freeVars e L.\\ [Core.getName x]
freeVars (Core.Let b e)       = (freeVars e ++ concatMap freeVars (Core.rhssOfBind b)) L.\\ (Core.getName <$> Core.bindersOf b)
freeVars (Core.Case e x _ as) = freeVars e ++ (concat [freeVars ae L.\\ (Core.getName <$> bs) | (_, bs, ae) <- as] L.\\ [Core.getName x])
freeVars (Core.Cast e _)      = freeVars e
freeVars (Core.Tick _ e)      = freeVars e
freeVars (Core.Type _)        = []
freeVars (Core.Coercion _)    = []

-- Used to compare groups
instance Eq Core.CoreBind where
  b == b' = Core.bindersOf b == Core.bindersOf b'

-- Sort a program in order of dependancies
-- Optimise this!
dependancySort :: Core.CoreProgram -> Core.CoreProgram
dependancySort p = foldl go [] depGraph
  where
    -- Pair binder groups with their dependancies
    depGraph = [(b, [group | rhs <- Core.rhssOfBind b, fv <- freeVars rhs, group <- findGroup p fv, group /= b]) | b <- p]

    go p' (b, deps) = L.nub $
      case L.elemIndex b p' of
        Just i -> uncurry (++) $ first (++ deps) $ splitAt i p' -- Insert dependencies before binder
        _      -> p' ++ deps ++ [b]                             -- Concatenate dependencies and binder to the end of the program
    
    -- Find the group in which the variable is contained
    findGroup [] _ = []
    findGroup (b:bs) x
      | x `elem` (Core.getName <$> Core.bindersOf b) = [b]
      | otherwise = findGroup bs x




      
-- Infer program
inferProg :: Core.CoreProgram -> InferM [(Core.Name, TypeScheme)]
inferProg p = do

  -- Reorder program with dependancies
  let p' = dependancySort p

  -- Mut rec groups
  z <- foldr (\b r -> do
    -- start <- liftIO getCurrentTime

    -- Filter evidence binds
    let xs   = Core.getName <$> filter (not . Core.isPredTy . Core.varType) (Core.bindersOf b)
    let rhss = filter (not . Core.isPredTy . Core.exprType) $ Core.rhssOfBind b

    -- Fresh typescheme for each binder in the group
    ts <- mapM (freshScheme . toSortScheme . Core.exprType) rhss

    -- Infer constraints for the rhs of each bind
    binds <- mapM (local (insertMany xs ts) . infer) rhss
    let (ts', cgs) = unzip binds

    -- Combine constraint graphs
    bcg <- foldM (\cg' (rhs, cg) -> union cg cg' `inExpr` rhs) empty $ zip rhss cgs 

    -- Insure fresh types are quantified by infered constraint (t' < t) for recursion
    -- Type/refinement variables bound in match those bound in t'
    bcg' <- foldM (\bcg' (rhs, t', Forall _ _ _ t) -> insert Eps t' t bcg' `inExpr` rhs) bcg (zip3 rhss ts' ts)

    -- Restrict constraints to the interface
    ts'' <- quantifyWith bcg' ts

    -- Add infered typescheme to the environment
    r' <- local (insertMany xs ts'') r
    
    -- !stop <- liftIO getCurrentTime
    -- !() <- liftIO $ putStr "Dep time: "
    -- !() <- liftIO $ print (Core.nameStableString <$> xs, diffUTCTime stop start)

    return $ (xs, ts''):r'
    ) (return []) p'
  return $ concatMap (uncurry zip) z





-- Extend constructors arguments with default type variables, i.e. Empty :: forall a. [a]
merge :: [Sort] -> [Core.Name] -> [Sort]
merge [] [] = []
merge [] as = map SVar as
merge (t:ts) (a:as) = t : merge ts as

inferVar :: Core.Var -> [Sort] -> Core.Expr Core.Var -> InferM (Type, ConGraph)
inferVar x ts e =
  case Core.isDataConId_maybe x of
    Just k -> do 
      (d, as, args) <- safeCon k
      let ts' = merge ts as
      if refinable k
        then do
          -- Infer refinable constructor
          args' <- mapM (fresh . subTypeVars as ts) args
          x     <- fresh $ SData d ts'
          cg    <- insert Eps (Con (Left e) d (toDataCon k) ts' args') x empty `inExpr` e
          return (foldr (:=>) x args', cg)
          
        else do
          -- Infer unrefinable constructor
          let args' = map (toType . subTypeVars as ts) args
          return (foldr (:=>) (Base d ts) args', empty)

    Nothing -> do  
      -- Infer polymorphic variable at type(s)
      (Forall as xs cs u) <- safeVar x
      let ds = fmap (\(RVar (_, d, ss)) -> SData d ss) xs

      -- Import variables constraints
      cg  <- fromList cs `inExpr` e
      ys  <- mapM fresh ds
      ts' <- mapM fresh ts
            
      -- Instantiate typescheme
      let xs' =  subTypeVars as ts' <$> xs
      ys      <- mapM (fresh . \(RVar (_, d, ss)) -> SData d ss) xs'
      
      -- Instantiate types
      let u' =  subTypeVars as ts' $ subRefinementVars xs' ys u
      v      <- fresh $ toSort $ Core.exprType e

      -- Import variables constraints at type
      cg' <- substituteMany xs' ys (subTypeVars as ts' cg) `inExpr` e

      cg'' <- insert Eps u' v cg' `inExpr` e

      return (v, cg'')





infer :: Core.Expr Core.Var -> InferM (Type, ConGraph)
infer e@(Core.Var x) = inferVar x [] e -- Infer monomorphic variable

infer l@(Core.Lit _) = do
  -- Infer literal expression
  t' <- fresh $ toSort $ Core.exprType l
  return (t', empty)

infer e@(Core.App e1 e2) =
  case fromPolyVar e of
    Just (x, ts) ->
      -- Infer polymorphic variable
      inferVar x ts e
    Nothing -> do
      -- Infer application
      (t1, c1) <- infer e1
      (t2, c2) <- infer e2
      case t1 of
        t3 :=> t4 -> do
          cg  <- union c1 c2 `inExpr` e
          cg' <- insert Eps t2 t3 cg `inExpr` e
          return (t4, cg')
        _ -> Core.pprPanic "Application to a non-function expression!" (Core.ppr (t1, e1))
  where
    -- Process a core type/evidence application
    fromPolyVar (Core.Var i) = Just (i, [])
    fromPolyVar (Core.App e1 (Core.Type t)) = do
      (i, ts) <- fromPolyVar e1
      return (i, ts ++ [toSort t])
    fromPolyVar (Core.App e1 e2) | Core.isPredTy (Core.exprType e2) = fromPolyVar e1 --For typeclass evidence
    fromPolyVar _ = Nothing

infer (Core.Lam x e) = do
  let t = Core.varType x
  if Core.isDictId x || isKind t -- Ignore typeclass evidence and type variable abstractions
    then infer e
    else do
      -- Variable abstraction
      t1 <- fresh $ toSort t
      (t2, cg) <- local (insertVar (Core.getName x) $ Forall [] [] [] t1) (infer e)
      return (t1 :=> t2, cg)
    where
      -- Does the type eventually return a lifted type kind
      isKind (Tcr.ForAllTy _ t) = isKind t
      isKind (Tcr.FunTy    _ t) = isKind t
      isKind (Tcr.AppTy t _)    = isKind t
      isKind (Tcr.TyConApp t _) = Tc.isKindTyCon t
      isKind t                  = isLiftedTypeKind t

infer e'@(Core.Let b e) = do
  -- Infer local module (i.e. let expression)
  let xs   = Core.getName <$> Core.bindersOf b
  let rhss = Core.rhssOfBind b

  -- Add each binds within the group to context with a fresh type (t) and no constraints
  ts <- mapM (freshScheme . toSortScheme . Core.exprType) rhss
  let withBinds = local (insertMany xs ts)

  (ts', cg) <- foldM (\(ts, cg) rhs -> do
    -- Infer each bind within the group, compiling constraints
    (t, cg') <- withBinds (infer rhs)
    cg''     <- union cg cg' `inExpr` rhs
    return (ts ++ [t], cg'')
    ) ([], empty) rhss

  --  Insure fresh types are quantified by infered constraint (t' < t)
  cg' <- foldM (\cg (rhs, t', Forall _ _ _ t) -> insert Eps t' t cg `inExpr` rhs) cg (zip3 rhss ts' ts)

  -- Restrict constraints to the interface
  ts'' <- quantifyWith cg' ts

  -- Infer in body with infered typescheme to the environment
  (t, icg) <- local (insertMany xs ts'') (infer e)
  cg''     <- union cg' icg `inExpr` e
  
  return (t, cg'')

  -- Infer top-level case expession
infer e'@(Core.Case e b rt as) = do
  -- Fresh return type
  t  <- fresh $ toSort rt

  -- Infer expression to pattern match on
  (t0, c0) <- infer e

  -- b @ e
  let es = toSort $ Core.exprType e
  et <- fresh es
  c0' <- insert Eps et t0 c0 `inExpr` e

  (caseType, cg) <- local (insertVar (Core.getName b) $ Forall [] [] [] et) (pushCase e >> foldM (\(caseType, cg) (a, bs, rhs) ->
    if Core.exprIsBottom rhs
      then return (caseType, cg) -- If rhs is bottom it is not a valid case
      else do
        -- Add variables introduced by the pattern
        ts <- mapM (fresh . toSort . Core.varType) bs

        -- Ensure return type is valid
        (ti', cgi) <- local (insertMany (Core.getName <$> bs) $ fmap (Forall [] [] []) ts) (infer rhs)
        cgi'       <- insert Eps ti' t cgi`inExpr` e'

        -- Track the occurance of a constructors/default case
        let (cgi'', caseType') = case a of {
          Core.DataAlt d -> (guardWith (Core.getName d) t0 cgi', do
              let SData _ ss' = es
              let tc' = toIfaceTyCon $ Core.dataConTyCon d
              (_, _, s) <- caseType
              return (Just tc', Just ss', (toDataCon d, ts):s))
            ;
          -- Default/literal cases
          _ -> (cgi', Nothing)
          }
        
        cg' <- union cg cgi' `inExpr` e'
        return (caseType', cg')
    ) (Just (Nothing, Nothing, []), c0') as)

  popCase

  tl <- topLevel e

  -- Ensure destructor is total, GHC will conservatively insert defaults
  cg <- case caseType of
    Nothing  -> return cg -- Literal cases must have a default
    Just (Just tc, Just ss, cs) -> if tl then insert Eps t0 (Sum (Left e') tc ss cs) cg `inExpr` e' else return cg
    _ -> Core.pprPanic "Inconsistent data constructors arguments!" (Core.ppr ())

  return (t, cg)

-- Remove core ticks
infer (Core.Tick _ e) = infer e

-- Maintain constraints but give trivial type (Dot - a sub/super-type of everything) to expression - effectively ignore casts
-- GHC already requires the prog to well typed
infer (Core.Cast e _) = do
  (_, cg) <- infer e
  return (Dot, cg)

-- Cannot infer a coercion expression.
-- For most programs these will never occur outside casts.
infer _ = error "Unimplemented"