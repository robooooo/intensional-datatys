{-# LANGUAGE TemplateHaskell, PatternSynonyms #-}
module Intensional.Horn.Clause where

import qualified Data.List                     as List
import           Data.Maybe                     ( isJust )
import           Data.Set                hiding ( valid )
import           Lens.Micro
import           Lens.Micro.TH                  ( makeLensesFor )
import           Maybes                         ( fromJust )
import           Prelude                 hiding ( filter
                                                , foldr
                                                , head
                                                , map
                                                , null
                                                )



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

-- | Remove trivial clauses from a set of horn clauses.
canonicize :: Ord a => Set (Horn a) -> Set (Horn a)
canonicize = filter (not . isTrivial)

-- | Add a set of propositions to the body of a horn clause.
-- In implication form, this corresponds to adding extra premises.
addGuards :: Ord a => Set a -> Horn a -> Horn a
addGuards extra = over _body (`union` extra)

-- Resolution with the first head @x@ as the resolvent. The second clause must 
-- contain @x@ in the body.
resolve :: Ord a => Horn a -> Horn a -> Maybe (Horn a)
resolve (Horn (Just x) body1) (Horn mayHead body2)
    | Just x == mayHead = Nothing
    | x `elem` body2    = (Just . Horn Nothing . delete x) (body1 `union` body2)
    | otherwise         = Nothing
resolve _ _ = Nothing

-- | Saturate a conjunctive set of horn clauses under resolution.
saturate :: forall a . Ord a => Set (Horn a) -> Set (Horn a)
saturate clauses = go clauses clauses clauses
  where
    -- | Perform one 'round' of saturation over every pair of variables between
    -- two sets, then recurse by finding any new resolvents that can be
    -- generated from pairs where at least one of the elements is new.
    go :: Set (Horn a) -> Set (Horn a) -> Set (Horn a) -> Set (Horn a)
    go prev a b =
        let pairs =
                unions
                    [ cartesianProduct a b
                    , cartesianProduct b a
                    , cartesianProduct b b
                    ]
            boundary = mapMaybe (uncurry resolve) pairs
            next     = union prev boundary
        in  if prev == next then next else go next prev boundary

    mapMaybe :: Ord u => (t -> Maybe u) -> Set t -> Set u
    mapMaybe f = map fromJust . filter isJust . map f

-- | Use the generalised resolution rule to remove a variable @x@ from a 
-- conjunctive set of horn clauses.
-- remove :: Ord a => a -> Set (Horn a) -> Set (Horn a)
-- remove x (canonicize -> clauses) =
--     let
--         -- Then we partition into groups based on the membership of @x@.
--         inHead = filter isInHead clauses
--         inBody = filter isInBody clauses
--         inNone = filter (liftA2 (&&) (not . isInHead) (not . isInBody)) clauses
--     in  union inNone . fromList $ do
--             bases <- over _body (x `delete`) <$> toList inBody
--             extra <- view _body <$> toList inHead
--             return $ bases & _body %~ (`union` extra)
--   where
--     isInHead (Horn head _) = Just x == head
--     isInBody (Horn _ body) = x `elem` body

-- | Saturate a conjunctive set of horn clauses under resolution.
-- saturate :: Ord a => Set (Horn a) -> Set (Horn a)
-- saturate clauses = go (layer clauses) clauses
--   where
--     go curr prev | curr == prev = prev
--                  | otherwise    = go (layer curr) curr

--     layer clauses' =
--         let vars = unions (map variables clauses')
--             next = unions $ map (`remove` clauses') vars
--         in  clauses' `union` next


-- | Determine if a conjunctive set of horn clauses is unsatisfiable.
-- TODO: This is done naively, not really utilising the special form of horn
-- clauses, for which satisfiability can be done much more efficently(?).
-- A non-demo version should probably change this, or use an external solver.
-- unsat :: Ord a => Set (Horn a) -> Bool
-- unsat (canonicize -> clauses) =
--     let noFreeVars = foldr (\x acc -> canonicize $ remove x acc)
--                            clauses
--                            (unions $ map variables clauses)
--     -- If clauses is @{}@ (which is @T@) then the expression is sat.
--     in  (not . null) noFreeVars
