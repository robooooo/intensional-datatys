{-# LANGUAGE TemplateHaskell, PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant if" #-}
module Intensional.Horn.Clause where

import           Data.Foldable                  ( find )
import qualified Data.List                     as List
import           Data.Maybe                     ( isJust
                                                , isNothing
                                                )
import           Data.Set                hiding ( valid )
import           Intensional.Ubiq               ( satTrace )
import           Lens.Micro              hiding ( _head
                                                , filtered
                                                )
import           Lens.Micro.TH                  ( makeLensesFor )
import           Maybes                         ( fromJust )
import           Prelude                 hiding ( filter
                                                , foldr
                                                , head
                                                , map
                                                , null
                                                )

-- | @mapMaybe@ for sets.
mapMaybe :: Ord u => (t -> Maybe u) -> Set t -> Set u
mapMaybe g = map fromJust . filter isJust . map g

-- | The type of horn clauses over variables of type a.
data Horn a = Horn
    { hornHead :: Maybe a
    , hornBody :: Set a
    }
    deriving (Eq, Ord, Foldable)
makeLensesFor
    [("hornHead", "_head"), ("hornBody", "_body")]
    ''Horn

instance Show a => Show (Horn a) where
    show (Horn head body) =
        let showHead = maybe "False" show head
            showBody = if (not . null) body
                then List.intercalate " & " (show <$> toList body)
                else "True" :: [Char]
        in  showBody ++ " => " ++ showHead

variables :: Ord a => Horn a -> Set a
variables horn = case horn of
    (Horn (Just head) body) -> insert head body
    (Horn Nothing     body) -> body

-- | Determine if a horn clause is trivial, i.e. contains @x v ~x@.
isTrivial :: Ord a => Horn a -> Bool
isTrivial (Horn (Just head) body) = head `elem` body
isTrivial _                       = False

-- | Determine if a horn clause is a contradiction, i.e. is T => F.
isContra :: Horn a -> Bool
isContra (Horn head body) = isNothing head && null body

-- | Determine if a horn clause is a unit clause.
-- If it is, this returns the unit variable.
getUnit :: Horn a -> Maybe a
getUnit (Horn (Just head) body) | null body = Just head
getUnit _ = Nothing

-- | Remove trivial clauses from a set of horn clauses.
canonicize :: Ord a => Set (Horn a) -> Set (Horn a)
canonicize = filter (not . isTrivial)

-- | Add a set of propositions to the body of a horn clause.
-- In implication form, this corresponds to adding extra premises.
addGuards :: Ord a => Set a -> Horn a -> Horn a
addGuards extra = over _body (`union` extra)

-- | Resolution with the first head @x@ as the resolvent. The second clause must 
-- contain @x@ in the body.
resolve :: Ord a => Horn a -> Horn a -> Maybe (Horn a)
resolve (Horn (Just x) body1) (Horn mayHead body2)
    | Just x == mayHead = Nothing
    | x `elem` body2    = find (not . isTrivial) (Just resolvent)
    | otherwise         = Nothing
  where
    body      = delete x (body1 `union` body2)
    resolvent = Horn mayHead body
resolve _ _ = Nothing

-- | SLD solution with the first head @x@ as the resolvent. The second clause 
-- must contain @x@ in the body.
sld :: Ord a => Horn a -> Horn a -> Maybe (Horn a)
sld (Horn (Just x) body1) (Horn Nothing body2)
    | x `elem` body2 = Just (Horn Nothing body)
    | otherwise      = Nothing
    where body = delete x (body1 `union` body2)
sld _ _ = Nothing


saturateUnder :: forall a . Ord a => (a -> a -> Maybe a) -> Set a -> Set a
saturateUnder f initial = go initial initial initial
  where
    -- | Perform one 'round' of saturation over every pair of variables between
    -- two sets, then recurse by finding any new resolvents that can be
    -- generated from pairs where at least one of the elements is new.
    go :: Set a -> Set a -> Set a -> Set a
    go aub a b =
        let
            -- Force the products to fix a space leak.
            !prods =
                [ cartesianProduct a b
                , cartesianProduct b a
                , cartesianProduct b b
                ]
            !pairs    = unions prods
            !boundary = mapMaybe (uncurry f) pairs
            -- !boundary = filter (not . isTrivial) boundary'
            !next     = union aub boundary
        in
            if aub == next
                then satTrace "Finish." next
                else satTrace
                    ("Boundary of size " ++ show (size boundary) ++ ".")
                    (go next aub boundary)


-- | Saturate a conjunctive set of horn clauses under resolution.
saturate :: forall a . Ord a => Set (Horn a) -> Set (Horn a)
saturate = saturateUnder resolve

-- | Enumerate the set of all clauses whose elements are drawn from a set of
-- interface variables.
allClauses :: forall a . Ord a => Set a -> Set (Horn a)
allClauses iface =
    let someHead = unions (map headIs iface)
        noneHead = map (Horn Nothing) (powerSet iface)
    in  noneHead `union` someHead
  where
    headIs :: a -> Set (Horn a)
    headIs i = map (Horn $ Just i) (powerSet $ delete i iface)

-- | Determine if a given clause is consistent with a conjunctive set of known
-- clauses.
consistent :: Ord a => Set (Horn a) -> Horn a -> Bool
consistent kb hc = (not . satisfiable) kb || satisfiable (insert hc kb)


-- | Determine if a set of conjunctive horn clauses can be satisfied.
-- Uses unit propagation.
satisfiable :: forall a . Ord a => Set (Horn a) -> Bool
satisfiable (canonicize -> hc) = go hc empty
  where
    -- | Keeps track of which units have been seen to ensure termination.
    go :: Set (Horn a) -> Set a -> Bool
    go kb seen = case propagate seen kb of
        _ | any isContra kb -> False
        Just (unit, next)   -> go next (insert unit seen)
        Nothing             -> True

    -- | Remove an arbitrary unit clause from a set of horn clauses.
    propagate :: Set a -> Set (Horn a) -> Maybe (a, Set (Horn a))
    propagate seen kb = do
        -- Find an arbitrary literal in a unit clause.
        unit <- lookupMax (filter (`notElem` seen) $ mapMaybe getUnit kb)
        -- Remove all clauses with the unit clause as the head.
        -- This should be except the unit clause itself, so add it back in.
        let filtered = filter (\(Horn head _) -> head /= Just unit) kb
            removed  = insert (Horn (Just unit) empty) filtered
        -- Remove any instances of the literal in any other clauses' bodies.
        return (unit, map (over _body $ delete unit) removed)
