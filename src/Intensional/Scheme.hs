{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Intensional.Scheme
    ( Scheme
    , HornScheme
    , HornSet
    , SchemeGen(..)
    , pattern Forall
    , mono
    , Intensional.Scheme.unsats
    , AtomF
    , Atom
    , HornConstraint(..)
    , _cinfo
    , _horn
    ) where

import           Binary
import qualified Data.IntMap                   as IntMap
import qualified Data.IntSet                   as I
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set
import qualified GHC
import           GhcPlugins
import           Intensional.Constraints       as Constraints
import           Intensional.Horn.Clause        ( Horn(hornBody, hornHead)
                                                , _body
                                                , _head
                                                )
import           Intensional.Types
import           Lens.Micro              hiding ( _head )
import           Lens.Micro.Extras              ( view )
import           Lens.Micro.TH                  ( makeLensesFor )



-- | The type of propositional atoms.
-- Pair of a constructor and a refinement variable.
type AtomF a = (a, RVar)

type Atom = AtomF GHC.Name

data HornConstraint = HornConstraint
    { hornConInfo  :: CInfo
    , hornConInner :: Horn Atom
    }
    deriving (Eq, Ord)
makeLensesFor
    [("hornConInfo", "_cinfo"), ("hornConInner", "_horn")]
    ''HornConstraint

type HornSet = Set HornConstraint
type HornScheme = SchemeGen HornSet TyCon

-- Constrained polymorphic types with type constructors of type @d@.
-- Underlying constraints are parameterised by a type @con@.
data SchemeGen con d = Scheme
    { tyvars      :: [Name]
    , boundvs     :: Domain
    , body        :: TypeGen d
    , constraints :: con
    }
    deriving (Functor, Foldable, Traversable)

type Scheme = SchemeGen ConstraintSet TyCon

{-# COMPLETE Forall #-}
pattern Forall :: Monoid con => [Name] -> TypeGen d -> SchemeGen con d
pattern Forall as t <- Scheme as _ t _ where
    Forall as t = Scheme as mempty t mempty

instance Outputable d => Outputable (SchemeGen ConstraintSet d) where
    ppr = prpr ppr

instance (Binary con, Binary d) => Binary (SchemeGen con d) where
    put_ bh (Scheme as bs t cs) =
        put_ bh as >> put_ bh (I.toList bs) >> put_ bh t >> put_ bh cs

    get bh =
        Scheme <$> get bh <*> (I.fromList <$> get bh) <*> get bh <*> get bh

instance (Refined con, Eq con, Monoid con, Outputable d)
        => Refined (SchemeGen con d) where

    domain s =
        (domain (body s) Prelude.<> domain (constraints s)) I.\\ boundvs s

    rename x y s
        | I.member x (boundvs s)
        = s
        | I.member y (boundvs s)
        = pprPanic "Alpha renaming of polymorphic types is not implemented!"
            $ ppr (x, y)
        | otherwise
        = Scheme { tyvars      = tyvars s
                 , boundvs     = boundvs s
                 , body        = rename x y (body s)
                 , constraints = rename x y (constraints s)
                 }

    prpr _ scheme
        | constraints scheme /= mempty = hang
            (hcat [pprTyQuant, pprConQuant, prpr varMap (body scheme)])
            2
            (hang (text "where") 2 (prpr varMap (constraints scheme)))
        | otherwise = hcat [pprTyQuant, pprConQuant, prpr varMap (body scheme)]
      where
        numVars  = I.size (boundvs scheme)
        varNames = if numVars > 3
            then [ char 'X' GhcPlugins.<> int n | n <- [1 .. numVars] ]
            else [ char c | c <- ['X', 'Y', 'Z'] ]
        varMap = (m IntMap.!)
          where
            m = IntMap.fromList $ zip (I.toAscList (boundvs scheme)) varNames
        pprTyQuant
            | null (tyvars scheme) = empty
            | otherwise = hcat
                [forAllLit <+> fsep (map ppr $ tyvars scheme), dot]
        pprConQuant
            | I.null (boundvs scheme)
            = empty
            | otherwise
            = hcat
                [ forAllLit <+> fsep (map varMap $ I.toList (boundvs scheme))
                , dot
                ]
instance (Ord a, Refined a) => Refined (Set a) where
    domain = Set.foldr I.union I.empty . Set.map domain
    rename x y = Set.map (rename x y)
    prpr m xs =
        hcat ["set ", brackets (fsep (punctuate comma (prpr m <$> toList xs)))]

instance Refined Atom where
    domain (_, x) = I.singleton x
    rename x y (k, rv) | rv == x   = (k, y)
                       | otherwise = (k, rv)
    prpr m (k, x) = hcat [m x, "_", ppr k]

instance (Ord a, Refined a) => Refined (Horn a) where
    domain = foldMap domain
    rename x y = over (_head . _Just) (rename x y) . over _body (rename x y)
    prpr m horn =
        let implHead = maybe "False" (prpr m) (view _head horn)
            implBodies =
                punctuate "&" $ (fmap $ prpr m) (toList $ view _body horn)
        in  hcat $ implBodies ++ ["=>", implHead]

instance Refined HornConstraint where
    domain = domain . view _horn
    rename x y = over _horn (rename x y)
    prpr m = prpr m . view _horn

-- Demand a monomorphic type
mono :: Monoid con => SchemeGen con d -> TypeGen d
mono (Forall [] t) = t
mono _             = Ambiguous

{-|
    Given a scheme @s@, @unsats s@ is the constraint set containing
    just the trivially unsatisfiable constraints associated with @s@.
-}
unsats :: Scheme -> ConstraintSet
unsats s = Constraints.unsats (constraints s)
