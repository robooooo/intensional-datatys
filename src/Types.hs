{-# LANGUAGE PatternSynonyms, FlexibleInstances #-}

module Types
    (
      Sort (SVar, SArrow, SData, SBase, SApp, SConApp),
      SortScheme (SForall),
      UType (TVar, TData, TArrow, TBase, TLit, TApp, TConApp),
      PType,
      RVar (RVar),
      Type,
      TypeScheme (Forall),
      SExpr (V, K, B, (:=>)),
      ConGraph,
      upArrow,
      polarise,
      subTypeVars,
      subSortVars,
      sub,
      stems,
      toSort,
      toSortScheme,
      fromPolyVar,
      isPrim,
      disp
    ) where

import Prelude hiding ((<>))
import Data.List
import GenericConGraph
import qualified GhcPlugins as Core
import Debug.Trace
import Data.Bifunctor (second)
import qualified TyCoRep as T
import qualified Data.Map as M
import Control.Monad.RWS hiding (Sum, Alt, (<>))
import Outputable

newtype RVar = RVar (Int, Bool, Core.TyCon) deriving Eq

instance Ord RVar where
  RVar (x, _, _) <= RVar (x', _, _) = x <= x'

data Sort = SVar Core.Var | SBase Core.TyCon | SData Core.TyCon | SArrow Sort Sort | SApp Sort Sort | SConApp Core.TyCon [Sort] deriving Show
data UType = 
    TVar Core.Var 
  | TBase Core.TyCon
  | TData Core.DataCon
  | TArrow 
  | TLit Core.Literal -- Sums can contain literals

  | TApp Sort Sort    -- Unrefinable & externally defined
  | TConApp Core.TyCon [Sort]

data PType = PVar Core.Var | PBase Core.TyCon | PData Bool Core.TyCon | PArrow PType PType | PApp Sort Sort | PConApp Core.TyCon [Sort]
type Type = SExpr RVar UType
data TypeScheme = Forall [Core.Var] [RVar] [(Type, Type)] Type
data SortScheme = SForall [Core.Var] Sort deriving Show

isPrim :: Core.NamedThing t => t -> Bool
isPrim t = isPrefixOf "$ghc-prim$" $ name t

isConstructor :: Core.Var -> Maybe Core.DataCon
isConstructor = Core.isDataConId_maybe

name :: Core.NamedThing a => a -> String
name = Core.nameStableString . Core.getName

fromPolyVar :: Core.CoreExpr -> Maybe (Core.Var, [Sort])
fromPolyVar (Core.Var i) = Just (i :: Core.Var, [])
fromPolyVar (Core.App e1 (Core.Type t)) = do
  (i, ts) <- fromPolyVar e1
  return (i, toSort t:ts)
fromPolyVar _ = Nothing

toSort :: Core.Type -> Sort
toSort (T.TyVarTy v) = SVar v
toSort (T.FunTy t1 t2) =
  let s1 = toSort t1
      s2 = toSort t2
  in SArrow s1 s2
toSort (T.TyConApp t []) -- Monomorphic constructors (refinable)
  | isPrim t = SBase t
  | otherwise = SData t

-- From external (unrefined modules)
toSort (T.AppTy t1 t2) =
  let s1 = toSort t1
      s2 = toSort t2
  in SApp s1 s2
toSort (T.TyConApp t args) = SConApp t $ fmap toSort args

toSort _ =  error "Core type is not a valid sort." -- Lit, cast and coercion

toSortScheme :: Core.Type -> SortScheme
toSortScheme (T.TyVarTy v) = SForall [] (SVar v)
toSortScheme (T.FunTy t1 t2) =
  let s1 = toSort t1
      s2 = toSort t2
  in SForall [] (SArrow s1 s2)
toSortScheme (T.ForAllTy b t) =
  let (SForall as st) = toSortScheme t
      a = Core.binderVar b
  in SForall (a:as) st
toSortScheme (T.TyConApp c args)
  | isPrim c = SForall [] $ SBase c
  | otherwise = SForall [] $ SData c
toSortScheme _ = error "Core type is not a valid sort scheme."

instance Core.Outputable UType where
  ppr (TVar v) = ppr v
  ppr (TBase b) = ppr b
  ppr (TData dc) = ppr dc
  ppr (TApp t1 t2) = text "(" <> (text . show) t1 <> (text . show) t2 <> text ")"
  ppr (TConApp tc t2) = text "(" <> ppr tc <> (text . show) t2 <> text ")"

instance Show UType where
  show (TVar v) = show v
  show (TBase b) = show b
  show (TData dc) = show dc
  show (TApp s1 s2) = "(" ++ show s1 ++ show s2 ++ ")"
  show (TConApp tc args) = "(" ++ show tc ++ show args ++ ")"

instance Core.Outputable RVar where
  ppr (RVar (x, p, d)) = text "[" <> ppr x <> (if p then text"+" else text "-") <> ppr d <> text "]"

instance Show RVar where
  show (RVar (x, p, d)) = "[" ++ show x ++ (if p then "+" else "-") ++ show d ++ "]"

instance Core.Outputable Type where
  ppr (V x p d) = text "[" <> ppr x <> if p then text "+" else text "-" <> ppr d <>  text "]"
  ppr (t1 :=> t2) =  text "(" <> ppr t1 <>  text "->" <> (ppr t2) <>  text ")"
  ppr (K v ts) = ppr v <>  text "(" <> interpp'SP ts <>  text ")"
  ppr (Sum cs) = pprWithBars (\(c, cargs) -> ppr c <>  text "(" <> interpp'SP cargs <> text ")") cs

instance Show Type where
  show (V x p d) = "[" ++ show x ++ (if p then "+" else "-") ++ show d ++ "]"
  show (t1 :=> t2) =  "(" ++ show t1 ++  "->" ++ show t2 ++  ")"
  show (K v ts) = show v ++  "(" ++ intercalate "," (fmap show ts) ++ ")"
  show (Sum cs) = intercalate " | " (fmap (\(c, cargs) -> show c ++ "(" ++ intercalate "," (fmap show cargs) ++ ")") cs)

-- instance Core.Outputable TypeScheme where
--   ppr (Forall as xs cg t) = text "∀" <> interppSP as <> text ".∀"  <> interppSP xs <> text "." <> ppr t <> text "where:" <> interppSP (toList cg)

disp as xs cs t = "∀" ++ intercalate ", " (fmap show as) ++ ".∀" ++ intercalate ", " (fmap show xs) ++ "." ++ show t ++ "\nwhere:\n" ++ intercalate ";\n" (fmap f cs)
  where
    f (t1, t2) = show t1 ++ " < " ++ show t2

instance Eq UType where
  TVar x == TVar y = name x == name y
  TBase b == TBase b' = Core.getName b == Core.getName b'
  TData d == TData d' = Core.getName d == Core.getName d'
  TLit l == TLit l' = l == l'
  TArrow == TArrow = True
  TApp s1 s2 == TApp s1' s2' = s1 == s1' && s2 == s2'
  TConApp tc args == TConApp tc' args' = tc == tc' && args == args'
  _ == _ = False

instance Eq Sort where
  SVar x == SVar y = name x == name y
  SBase b == SBase b' = Core.getName b == Core.getName b'
  SData d == SData d' = Core.getName d == Core.getName d'
  SArrow s1 s2 == SArrow s1' s2' = s1 == s1' && s2 == s2'
  SApp s1 s2 == SApp s1' s2' = s1 == s1' && s2 == s2'
  SConApp tc args == SConApp tc' args' = tc == tc' && args == args'
  _ == _ = False

type ConGraph = ConGraphGen RVar UType

instance Core.Outputable ConGraph where
  ppr ConGraph{succs = s, preds = p, subs =sb} = ppr s <> text "\n" <> ppr p <> text "\n" -- <> (text $ show sb)

split :: String -> [String]
split [] = [""]
split (c:cs) | c == '$'  = "" : rest
             | otherwise = (c : head rest) : tail rest
    where rest = split cs

-- assume everything is coming from the same module
instance Show Core.Var where
  show n = last $ split (Core.nameStableString $ Core.getName n)

instance Show Core.Name where
  show n = last $ split (Core.nameStableString $ Core.getName n)

instance Show Core.TyCon where
  show n = last $ split (Core.nameStableString $ Core.getName n)

instance Show Core.DataCon where
  show n = last $ split (Core.nameStableString $ Core.getName n)

instance Constructor UType where
  variance TArrow = [False, True]
  variance _ = repeat True

pattern (:=>) :: Type -> Type -> Type
pattern t1 :=> t2 = Con TArrow [t1, t2]

pattern K :: Core.DataCon -> [Type] -> Type
pattern K v ts = Con (TData v) ts

pattern V :: Int -> Bool -> Core.TyCon -> Type
pattern V x p d = Var (RVar (x, p, d))

pattern B :: Core.TyCon -> Type
pattern B b = Con (TBase b) []

stems :: Type -> [Int]
stems (V x _ _) = [x]
stems (Sum cs) = concatMap (\(_, cargs) -> concatMap stems cargs) cs
stems _ = []

upArrow :: Int -> [PType] -> [Type]
upArrow x = fmap upArrow'
  where
    upArrow' (PData p d)     = Var $ RVar (x, p, d)
    upArrow' (PArrow t1 t2)  = upArrow' t1 :=> upArrow' t2
    upArrow' (PVar a)        = Con (TVar a) []
    upArrow' (PBase b)       = Con (TBase b) []
    upArrow' (PApp s1 s2)    = Con (TApp s1 s2) [] -- Unrefinable
    upArrow' (PConApp t args)= Con (TConApp t args) [] -- Unrefinable

polarise :: Bool -> Sort -> PType
polarise p (SVar a) = PVar a
polarise p (SBase b) = PBase b
polarise p (SData d) = PData p d
polarise p (SArrow s1 s2) = PArrow (polarise (not p) s1) (polarise p s2)
polarise _ (SApp s1 s2) = PApp s1 s2
polarise _ (SConApp t args) = PConApp t args

sub :: [RVar] -> [Type] -> Type -> Type
sub [] [] t = t
sub (x:xs) (y:ys) (Var x')
  | x == x' = y
  | otherwise = sub xs ys (Var x')
sub xs ys (Sum cs) = Sum $ fmap (second $ fmap (sub xs ys)) cs
sub _ _ _ = error "Substitution vectors have different lengths"

subSortVars :: [Core.Var] -> [Sort] -> Sort -> Sort
subSortVars [] [] u = u
subSortVars (a:as) (t:ts) (SVar a')
  | a == a' = subSortVars as ts t
  | otherwise = subSortVars as ts (SVar a')
subSortVars as ts (SArrow s1 s2) = SArrow (subSortVars as ts s1) (subSortVars as ts s2)
subSortVars as ts (SApp s1 s2) = SApp (subSortVars as ts s1) (subSortVars as ts s2)
subSortVars as ts (SConApp tc args) = SConApp tc (subSortVars as ts <$> args)
subSortVars _ _ s = s

-- If the type is a lifted sort return the sort, otherwise fail i.e. has the type undergone some refinement
isSort :: Type -> Maybe Sort
isSort (Var _) = Nothing
isSort (Con (TVar a) []) = Just $ SVar a
isSort (B b) = Just $ SBase b
isSort (Con (TApp s1 s2) []) = Just $ SApp s1 s2
isSort (Con (TConApp ty args) []) = Just $ SConApp ty args
isSort (t1 :=> t2) = do 
  s1 <- isSort t1
  s2 <- isSort t2
  return (SArrow s1 s2)
isSort (K v ts) = Nothing -- Constructors only as refinements of data types
isSort (Con (TLit _) _) = Nothing -- TLit only occurs as a result of case analysis

subTypeVars :: [Core.Var] -> [Type] -> Type -> Type
subTypeVars [] [] u = u
subTypeVars (a:as) (t:ts) (Con (TVar a') [])
  | a == a' = subTypeVars as ts t
  | otherwise = subTypeVars as ts $ Con (TVar a') []

subTypeVars as ts (Con (TApp s1 s2) []) = case mapM isSort ts of
  Just ss -> Con (TApp (subSortVars as ss s1) (subSortVars as ss s2)) []
  _ -> error "Cannot sub refinement variables into type application"
subTypeVars as ts (Con (TConApp tc args) []) = case mapM isSort ts of
  Just ss -> Con (TConApp tc (subSortVars as ss <$> args)) []
  _ -> error "Cannot sub refinement variables into polymorphic type constructor"

subTypeVars as ts (Sum ((c, cargs):cs)) = let -- Type variables don't appear in sums
  Sum cs' = subTypeVars as ts (Sum cs)
  in Sum $ (c, fmap (subTypeVars as ts) cargs):cs'
subTypeVars as ts (Var v) = Var v -- Type and refinement variables are orthogonal
subTypeVars as ts One = One
subTypeVars as ts Zero = Zero
