{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Intensional.Horn.ToHorn where
import qualified Data.IntSet                   as IS
import qualified Data.Map.Strict               as Map
import qualified Data.Set                      as Set
import           Data.Set                       ( Set )
import qualified GhcPlugins                    as GHC
import           GhcPlugins
import           Intensional.Constraints
import           Intensional.Guard              ( Guard(groups) )
import           Intensional.Horn.Clause
import           Intensional.Types
import           Lens.Micro
import Intensional.Horn.Constraints

-- | Intermediate representation of set expressions, used for @toHorn@.
data SetExpr a
    = Constructors SrcSpan (Set a)
    | Refined Int a
    deriving (Eq, Ord, Show)

-- | Intermediate representation of set constraints, used for @toHorn@.
type Constr = (Set Atom, SetExpr GHC.Name, SetExpr GHC.Name)

instance Outputable a => Refined (SetExpr a) where
    domain (Refined rv _) = IS.singleton rv
    domain _              = IS.empty

    rename x y (Refined rv k) | rv == x = Refined y k
    rename _ _ other                    = other

    prpr _ (Constructors _ ks) =
        let kns = fmap ppr (toList ks)
        in  hcat ["{", fsep (punctuate ", " kns), "}"]
    prpr m (Refined rv k) = hcat [m rv, "(", ppr k, ")"]

instance Refined Constr where
    domain (g, l, r) = IS.unions [domain g, domain l, domain r]
    rename x y (g, l, r) = (rename x y g, rename x y l, rename x y r)
    prpr m (g, l, r) = hcat [prpr m g, " ? ", prpr m l, " <= ", prpr m r]


-- | Combinator for constructing intermediate constraints.
(?) :: Set (GHC.Name, Int) -> (SetExpr GHC.Name, SetExpr GHC.Name) -> Constr
g ? (l, r) = (Set.map (uncurry Atom) g, l, r)

-- | Translate a single constraint to a set of horn clauses, given a set of
-- constructors for the underlying type @d@.
toHorn :: Set GHC.Name -> Constr -> Set (Horn Atom)
toHorn constructors (guards, lefts, rights) = case (lefts, rights) of
    -- Singleton T/F constructors, I think?
    (Constructors _ l1, Constructors _ l2)
        | l1 `Set.isSubsetOf` l2 -> Set.empty
        | otherwise              -> Set.singleton (Horn Nothing Set.empty)

    (Refined x d1, Refined y d2)
        | d1 == d2 -> Set.map
            (\k -> mkHornImpl (Atom k y) $ Atom k x : toList guards)
            constructors
        | otherwise -> error "Ill-defined constraint!"

    -- Could check if l <= constructorsOf d?
    (Constructors _span ks, Refined x _d) ->
        Set.map (\kn -> Horn (Just $ Atom kn x) Set.empty) ks

    (Refined x _d, Constructors _span ks) ->
        let complement = constructors Set.\\ ks
        in  Set.map (Horn Nothing . Set.singleton . flip Atom x) complement

  where

    mkHornImpl :: Atom -> [Atom] -> Horn Atom
    mkHornImpl head body = Horn (Just head) (Set.fromList body)

guardHornWith :: Guard -> HornSet -> HornSet
guardHornWith (groups -> g) = Set.map addConstraint
  where
    addConstraint :: HornConstraint -> HornConstraint
    addConstraint = over _horn (addGuards guardProps)

    guardProps :: Set Atom
    guardProps = Map.foldlWithKey'
        (\acc (x, _) ks -> Set.union (makeProp x ks) acc)
        Set.empty
        g

    makeProp :: RVar -> UniqSet GHC.Name -> Set Atom
    makeProp x ks = Set.map (`Atom` x) (Set.fromList $ nonDetEltsUniqSet ks)

-- | Restrict a set of horn clauses to those containing only certain variables.  
restrict :: Ord a => Set a -> Set (Horn a) -> Set (Horn a)
restrict domain = Set.filter isContained
    where isContained clause = all (`Set.member` domain) (variables clause)
