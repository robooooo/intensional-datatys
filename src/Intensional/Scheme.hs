{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Intensional.Scheme
    ( Scheme
    , SchemeGen(..)
    , pattern Forall
    , mono
    , Intensional.Scheme.unsats
    ) where

import           Binary
import qualified Data.IntSet                   as I
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set
import           GhcPlugins
import           Intensional.Constraints       as Constraints
import           Intensional.Horn.Clause        ( Horn(..)
                                                , _body
                                                , _head
                                                , variables
                                                )
import           Intensional.Types
import           Lens.Micro              hiding ( _head )
import           Lens.Micro.Extras              ( view )


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

instance (Refined con, Eq con, Monoid con, Outputable d)
        => Outputable (SchemeGen con d) where
    ppr = prpr ppr

instance (Binary con, Binary d) => Binary (SchemeGen con d) where
    put_ bh (Scheme as bs t cs) =
        put_ bh as >> put_ bh (I.toList bs) >> put_ bh t >> put_ bh cs

    get bh =
        Scheme <$> get bh <*> (I.fromList <$> get bh) <*> get bh <*> get bh

instance (Binary a, Ord a) => Binary (Set a) where
    put_ bh = put_ bh . toList
    get bh = Set.fromList <$> get bh

instance (Binary a, Ord a) => Binary (Horn a) where
    put_ bh (Horn hhead body) = put_ bh (hhead, body)
    get bh = uncurry Horn <$> get bh

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

    prpr disp scheme
        | constraints scheme /= mempty = hang
            (hcat [pprTyQuant, pprConQuant, prpr disp (body scheme)])
            2
            (hang (text "where") 2 (prpr disp (constraints scheme)))
        | otherwise = hcat [pprTyQuant, pprConQuant, prpr disp (body scheme)]
      where
        -- numVars  = I.size (boundvs scheme)
        -- varNames = if numVars > 3
        --     then [ char 'X' GhcPlugins.<> int n | n <- [1 .. numVars] ]
        --     else [ char c | c <- ['X', 'Y', 'Z'] ]
        -- varMap = (m IntMap.!)
        --   where
        --     m = IntMap.fromList $ zip (I.toAscList (boundvs scheme)) varNames
        pprTyQuant
            | null (tyvars scheme) = empty
            | otherwise = hcat
                [forAllLit <+> fsep (map ppr $ tyvars scheme), dot]
        pprConQuant
            | I.null (boundvs scheme)
            = empty
            | otherwise
            = hcat
                [forAllLit <+> fsep (map disp $ I.toList (boundvs scheme)), dot]
instance (Ord a, Refined a) => Refined (Set a) where
    domain = I.unions . Set.map domain
    rename x y = Set.map (rename x y)
    prpr m xs = hcat
        [ "Set.fromList ("
        , int (Set.size xs)
        , ") "
        , brackets (fsep (punctuate comma (prpr m <$> toList xs)))
        ]

instance Refined a => Refined [a] where
    domain = I.unions . fmap domain
    rename x y = fmap (rename x y)
    prpr m xs = hcat
        [ "("
        , int (length xs)
        , ") "
        , brackets (fsep (punctuate comma (prpr m <$> toList xs)))
        ]



instance (Ord a, Refined a) => Refined (Horn a) where
    domain = I.unions . Set.map domain . variables
    rename x y = over (_head . _Just) (rename x y) . over _body (rename x y)
    prpr m horn =
        let
            implHead   = maybe "False" (prpr m) (view _head horn)
            body       = view _body horn

            implBodies = if (not . null) body
                then punctuate " & "
                    $ (fmap $ prpr m) (toList $ view _body horn)
                else [text "True"]
        in
            hcat $ implBodies ++ [" => ", implHead]
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
