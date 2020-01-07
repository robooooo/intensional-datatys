{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Types (
  Extended(..),
  Type(..),
  shape,
  slice,
  Refined(..),
  FromCore(..),
  fromCore,
  subTyVar,
) where

import Control.Monad 

import BasicTypes
import Outputable
import qualified TyCoRep as Tcr
import qualified GhcPlugins as Core

data Extended where
  S :: Extended -- Unrefined
  T :: Extended -- Refined

data Type (e :: Extended) where
  Var    :: Core.Name -> Type e
  App    :: Type S -> Type S -> Type e
  Base   :: Core.TyCon -> Type e
  Data   :: Core.TyCon -> Type S
  Inj    :: Int -> Core.TyCon -> Type T
  (:=>)  :: Type e -> Type e -> Type e
  Lit    :: Tcr.TyLit -> Type e
  Forall :: Core.Name -> Type e -> Type e

deriving instance Eq (Type e)

-- Clone of a Outputable (Core.Type)
instance Outputable (Type e) where
  ppr = pprTy topPrec
    where
      pprTy :: PprPrec -> Type e -> SDoc
      pprTy _ (Var a)        = ppr a
      pprTy prec (App t1 t2) = hang (pprTy prec t1)
                                  2 (pprTy appPrec t2)
      pprTy _ (Base b)       = ppr b
      pprTy _ (Data d)       = ppr d
      pprTy prec (Inj x d)   = maybeParen prec funPrec $
                              sep [text "inj", ppr x, ppr d]
      pprTy prec (t1 :=> t2) = maybeParen prec funPrec $
                              sep [pprTy funPrec t1, arrow <+> pprTy prec t2]
      pprTy _ (Lit l)        = ppr l
      pprTy prec ty@Forall{} 
        | (tvs, body) <- split ty
        = maybeParen prec funPrec $
          hang (text "forall" <+> fsep (map ppr tvs) Core.<> dot)
            2 (ppr body)
        where
          split ty | Forall tv ty' <- ty
                    , (tvs, body) <- split ty'
                    = (tv:tvs, body)
                    | otherwise
                    = ([], ty)

-- The underlying shape
shape :: Type e -> Type S
shape (Var a)       = Var a
shape (App a b)     = App a b
shape (Base b)      = Base b
shape (Data d)      = Base d
shape (Inj _ d)     = Base d
shape (a :=> b)     = shape a :=> shape b
shape (Lit l)       = Lit l
shape (Forall as t) = Forall as (shape t)

-- Decides whether a datatypes only occurs positively
refinable :: Core.TyCon -> Bool
refinable tc = (length (Core.tyConDataCons tc) > 1) && all pos (concatMap Core.dataConOrigArgTys $ Core.tyConDataCons tc)
  where
    pos :: Core.Type -> Bool
    pos (Tcr.FunTy t1 t2) = neg t1 && pos t2
    pos _                 = True

    neg :: Core.Type -> Bool
    -- Check this with Steven!
    neg (Tcr.TyConApp tc' _)               | tc == tc' = False
    neg (Tcr.AppTy (Tcr.TyConApp tc' _) _) | tc == tc' = False 
    neg (Tcr.TyVarTy _)   = False -- Type variables may be substituted with the type itself
                                  -- Perhaps it is possible to record whether a type variable occurs +/-
    neg (Tcr.FunTy t1 t2) = pos t1 && neg t2
    neg _                 = True

-- Take the slice of a datatype
slice :: [Core.TyCon] -> [Core.TyCon]
slice tcs
  | tcs' == tcs = tcs
  | otherwise   = slice tcs'
  where
    tcs' = [tc' | tc <- tcs, dc <- Core.tyConDataCons tc, (Tcr.TyConApp tc' _) <- Core.dataConOrigArgTys dc, tc' `notElem` tcs, refinable tc']

-- Objects which are parameterised by refinement variables
class Refined t where
  domain :: t -> [Int]
  rename :: Int -> Int -> t -> t

instance Refined (Type e) where
  domain (App a b)    = domain a ++ domain b
  domain (Inj x d)    = [x]
  domain (a :=> b)    = domain a ++ domain b
  domain (Forall _ t) = domain t
  domain _            = []

  rename x y (App a b)     = App (rename x y a) (rename x y b)
  rename x y (Inj x' d)
    | x == x'              = Inj y d
    | otherwise            = Inj x' d
  rename x y (a :=> b)     = rename x y a :=> rename x y b
  rename x y (Forall as t) = Forall as (rename x y t)
  rename _ _ t             = t

-- Convert from a core type
class Monad m => FromCore m (e :: Extended) where
  dataType :: Core.TyCon -> m (Type e)

instance Monad m => FromCore m S where
  dataType t = return $ Data t

fromCore :: FromCore m e => Core.Type -> m (Type e)
fromCore (Tcr.TyVarTy a) = return $ Var $ Core.getName a
fromCore (Tcr.AppTy t1 t2) = do
  s1 <- fromCore t1
  s2 <- fromCore t2
  return $ App s1 s2
fromCore (Tcr.TyConApp t args)
  | Core.isTypeSynonymTyCon t
  , Just (as, u) <- Core.synTyConDefn_maybe t
  = fromCore (Core.substTy (Core.extendTvSubstList Core.emptySubst (zip as args)) u)
 
  | refinable t 
  = dataType t

  | otherwise
  = foldM (\b a -> App (shape b) <$> fromCore a) (Base t) args
fromCore (Tcr.FunTy t1 t2) = do
  s1 <- fromCore t1
  s2 <- fromCore t2
  return (s1 :=> s2)
fromCore (Tcr.LitTy l) = return $ Lit l
fromCore (Tcr.ForAllTy b t) = do
  let a = Core.getName $ Core.binderVar b
  t' <- fromCore t
  return $ Forall a t'
fromCore t = Core.pprPanic "Unexpected Cast or Coercion type" (Core.ppr t)

-- Substitute type variable
subTyVar :: FromCore m e => Core.Name -> Type e -> Core.Type -> m (Type e)
subTyVar a (Var a') t 
  | a == a'    = fromCore t
  | otherwise  = return (Var a')
subTyVar a (App x y) t = do
  x' <- subTyVar a x t
  y' <- subTyVar a y t
  return $ App x' y' 
subTyVar a (x :=> y) t = do
  x' <- subTyVar a x t
  y' <- subTyVar a y t
  return (x' :=> y')
subTyVar a (Forall a' u) t
  | a == a' = return (Forall a' u)
  | otherwise = do
    u' <- subTyVar a u t
    return $ Forall a' u'
subTyVar _ t _ = return t