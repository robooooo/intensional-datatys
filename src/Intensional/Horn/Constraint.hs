{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE TupleSections #-}
module Intensional.Horn.Constraint where
import qualified Data.Map.Strict               as Map
import           Data.Map.Strict                ( Map )
import qualified Data.Set                      as Set
import           Data.Set                       ( Set )
import qualified GhcPlugins                    as GHC
import           GhcPlugins                     ( nonDetEltsUniqSet )
import           Intensional.Constraints
import           Intensional.Constructors       ( K(..) )
import           Intensional.Guard              ( Guard(groups) )
import           Intensional.Horn.Clause
import           Intensional.Types

-- | The type of propositional atoms.
-- Pair of a constructor and a refinement variable.
type AtomF a = (a, Int)

type Atom = AtomF GHC.Name

type Atom' = AtomF String

-- | Intermediate representation of set expressions, used for @toHorn@.
data SetExpr a
    = Constructors (Set a)
    | Refined Int a
    deriving (Eq, Ord, Show)

type Constr = (Set (String, Int), SetExpr String, SetExpr String)

toHorn' :: Map String (Set String) -> Set Constr -> Set (Horn Atom')
toHorn' context = Set.unions . Set.map translate
  where
    translate :: Constr -> Set (Horn Atom')
    translate (guards, lefts, rights) = case (lefts, rights) of
        -- Singleton T/F constructors, I think?
        (Constructors l1, Constructors l2)
            | l1 `Set.isSubsetOf` l2 -> Set.empty
            | otherwise              -> Set.singleton (Horn Nothing Set.empty)

        (Refined x d1, Refined y d2)
            | d1 == d2 -> Set.map
                (\k -> mkHornImpl (k, y) $ (k, x) : toList guards)
                (constructorsOf d1)
            | otherwise -> error "Ill-defined constraint!"

        -- Could check if l <= constructorsOf d?
        (Constructors l, Refined x _d) ->
            Set.singleton $ Horn Nothing $ Set.union (Set.map (, x) l) guards

        (Refined x d, Constructors l) ->
            let complement = constructorsOf d Set.\\ l
            in  Set.singleton $ Horn Nothing $ Set.union
                    (Set.map (, x) complement)
                    guards

    constructorsOf :: String -> Set String
    constructorsOf = (context Map.!)

    mkHornImpl :: Atom' -> [Atom'] -> Horn Atom'
    mkHornImpl head body = Horn (Just head) (Set.fromList body)

-- | Translate a set constraint set to a set of conjunctive horn clauses.
-- Requires a context to lookup the datatype of constructors.
toHorn :: Map GHC.Name (Set GHC.Name) -> ConstraintSet -> Set (Horn Atom)
toHorn context = Set.unions . fmap translate . toList
  where
    translate :: Atomic -> Set (Horn Atom)
    translate Constraint { left, right, guard } =
        let lefts  = intoSet left
            rights = intoSet right
            guards = translateGuards guard
        in  case (lefts, rights) of
                -- Singleton T/F constructors, I think?
                (Constructors l1, Constructors l2)
                    | l1 `Set.isSubsetOf` l2 -> Set.empty
                    | otherwise -> Set.singleton (Horn Nothing Set.empty)

                (Refined x d1, Refined y d2)
                    | d1 == d2 -> Set.map
                        (\k -> mkHornImpl (k, y) $ (k, x) : toList guards)
                        (constructorsOf d1)
                    | otherwise -> error "Ill-defined constraint!"

                -- Could check if l <= constructorsOf d?
                (Constructors l, Refined x _d) ->
                    Set.singleton $ Horn Nothing $ Set.union
                        (Set.map (, x) l)
                        guards

                (Refined x d, Constructors l) ->
                    let complement = constructorsOf d Set.\\ l
                    in  Set.singleton $ Horn Nothing $ Set.union
                            (Set.map (, x) complement)
                            guards

    constructorsOf :: GHC.Name -> Set GHC.Name
    constructorsOf = (context Map.!)

    translateGuards :: Guard -> Set Atom
    translateGuards (groups -> guards) = Map.foldrWithKey
        (\(x, _) k acc -> Set.insert (head $ nonDetEltsUniqSet k, x) acc)
        Set.empty
        guards

    intoSet :: K r -> SetExpr GHC.Name
    intoSet (Set ks _     ) = Constructors (Set.fromList $ nonDetEltsUniqSet ks)
    intoSet (Con k  _     ) = Constructors (Set.singleton k)
    -- Base datatypes can't be refined, so what to do about this?
    intoSet (Dom (Base _ )) = error "not sure yet"
    intoSet (Dom (Inj x d)) = Refined x d

    mkHornImpl :: Atom -> [Atom] -> Horn Atom
    mkHornImpl head body = Horn (Just head) (Set.fromList body)


-- | Restrict a set of horn clauses to those containing only certain variables.  
restrict :: Ord a => Set a -> Set (Horn a) -> Set (Horn a)
restrict domain = Set.filter isContained
    where isContained clause = all (`Set.member` domain) (variables clause)
