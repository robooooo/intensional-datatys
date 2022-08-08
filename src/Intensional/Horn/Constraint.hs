{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE TupleSections #-}
module Intensional.Horn.Constraint where
import qualified Data.Map.Strict               as Map
import qualified Data.Set                      as Set
import           Data.Set                       ( Set )
import qualified GhcPlugins                    as GHC
import           GhcPlugins                     ( SrcSpan
                                                , UniqSet
                                                , nonDetEltsUniqSet
                                                )
import           Intensional.Constraints
import           Intensional.Guard              ( Guard(groups) )
import           Intensional.Horn.Clause
import           Intensional.Scheme
import           Intensional.Types
import           Lens.Micro

-- | Intermediate representation of set expressions, used for @toHorn@.
data SetExpr a
    = Constructors SrcSpan (Set a)
    | Refined Int a
    deriving (Eq, Ord, Show)

-- | Intermediate representation of set constraints, used for @toHorn@.
type Constr = (Set Atom, SetExpr GHC.Name, SetExpr GHC.Name)

-- | Combinator for constructing intermediate constraints.
(?) :: Set (GHC.Name, Int) -> (SetExpr GHC.Name, SetExpr GHC.Name) -> Constr
g ? (l, r) = (Set.map (uncurry $ Atom Nothing) g, l, r)

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
            (\k -> mkHornImpl (atomRef k y) $ atomRef k x : toList guards)
            constructors
        | otherwise -> error "Ill-defined constraint!"

    -- Could check if l <= constructorsOf d?
    (Constructors s l, Refined x _d) ->
        Set.singleton $ Horn Nothing $ Set.union (Set.map (atomCon s x) l)
                                                 guards

    (Refined x _, Constructors s l) ->
        let complement = constructors Set.\\ l
        in  Set.singleton $ Horn Nothing $ Set.union
                (Set.map (atomCon s x) complement)
                guards

  where
    atomCon :: SrcSpan -> RVar -> GHC.Name -> Atom
    atomCon s x kn = Atom (Just s) kn x

    atomRef :: GHC.Name -> RVar -> Atom
    atomRef = Atom Nothing

    mkHornImpl :: Atom -> [Atom] -> Horn Atom
    mkHornImpl head body = Horn (Just head) (Set.fromList body)

-- | Translate a set constraint set to a set of conjunctive horn clauses.
-- Requires a context to lookup the datatype of constructors.
-- toHorn :: Map GHC.Name (Set GHC.Name) -> ConstraintSet -> Set (Horn Atom)
-- toHorn context = Set.unions . fmap translate . toList
--   where
--     translate :: Atomic -> Set (Horn Atom)
--     translate Constraint { left, right, guard } =
--         let lefts  = intoSet left
--             rights = intoSet right
--             guards = translateGuards guard
--         in  case (lefts, rights) of
--                 -- Singleton T/F constructors, I think?
--                 (Constructors l1, Constructors l2)
--                     | l1 `Set.isSubsetOf` l2 -> Set.empty
--                     | otherwise -> Set.singleton (Horn Nothing Set.empty)

--                 (Refined x d1, Refined y d2)
--                     | d1 == d2 -> Set.map
--                         (\k -> mkHornImpl (k, y) $ (k, x) : toList guards)
--                         (constructorsOf d1)
--                     | otherwise -> error "Ill-defined constraint!"

--                 -- Could check if l <= constructorsOf d?
--                 (Constructors l, Refined x _d) ->
--                     Set.singleton $ Horn Nothing $ Set.union
--                         (Set.map (, x) l)
--                         guards

--                 (Refined x d, Constructors l) ->
--                     let complement = constructorsOf d Set.\\ l
--                     in  Set.singleton $ Horn Nothing $ Set.union
--                             (Set.map (, x) complement)
--                             guards

--     constructorsOf :: GHC.Name -> Set GHC.Name
--     constructorsOf = (context Map.!)

--     translateGuards :: Guard -> Set Atom
--     translateGuards (groups -> guards) = Map.foldrWithKey
--         (\(x, _) k acc -> Set.insert (head $ nonDetEltsUniqSet k, x) acc)
--         Set.empty
--         guards

--     intoSet :: K r -> SetExpr GHC.Name
--     intoSet (Set ks _     ) = Constructors (Set.fromList $ nonDetEltsUniqSet ks)
--     intoSet (Con k  _     ) = Constructors (Set.singleton k)
--     -- Base datatypes can't be refined, so what to do about this?
--     intoSet (Dom (Base _ )) = error "not sure yet"
--     intoSet (Dom (Inj x d)) = Refined x d

--     mkHornImpl :: Atom -> [Atom] -> Horn Atom
--     mkHornImpl head body = Horn (Just head) (Set.fromList body)

guardHornWith :: Guard -> HornSet -> HornSet
guardHornWith (groups -> g) = Set.map addConstraint
  where
    addConstraint :: HornConstraint -> HornConstraint
    addConstraint = over _horn (addGuard guardProps)

    guardProps :: Set Atom
    guardProps = Map.foldlWithKey'
        (\acc (x, _) ks -> Set.union (makeProp x ks) acc)
        Set.empty
        g

    makeProp :: RVar -> UniqSet GHC.Name -> Set Atom
    makeProp x ks = Set.map (\kn -> Atom Nothing kn x)
                            (Set.fromList $ nonDetEltsUniqSet ks)

-- | Restrict a set of horn clauses to those containing only certain variables.  
restrict :: Ord a => Set a -> Set (Horn a) -> Set (Horn a)
restrict domain = Set.filter isContained
    where isContained clause = all (`Set.member` domain) (variables clause)
