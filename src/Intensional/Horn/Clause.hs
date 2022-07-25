module Intensional.Horn.Clause where

import           Control.Applicative            ( (<|>)
                                                , Applicative(liftA2)
                                                )
import           Data.Set                hiding ( valid )
import           Lens.Micro
import           Lens.Micro.Extras
import           Prelude                 hiding ( filter
                                                , foldr
                                                , head
                                                , map
                                                , null
                                                )

-- | The type of horn clauses over variables of type a.
data Horn a = Horn (Maybe a) (Set a)
    deriving (Eq, Ord, Show)

headL :: Lens (Horn a) (Horn a) (Maybe a) (Maybe a)
headL = lens (\(Horn head _) -> head) (\(Horn _ body) new -> Horn new body)

bodyL :: Lens (Horn a) (Horn a) (Set a) (Set a)
bodyL = lens (\(Horn _ body) -> body) (\(Horn head _) new -> Horn head new)

variables :: Ord a => Horn a -> Set a
variables (Horn (Just guard) body) = guard `insert` body
variables (Horn Nothing      body) = body

-- | Determine if a horn clause is trivial, i.e. contains @x v ~x@.
isTrivial :: Ord a => Horn a -> Bool
isTrivial (Horn (Just head) body) = head `elem` body
isTrivial _                       = False

-- | Remove trivial clauses from a set of horn clauses.
canonicize :: Ord a => Set (Horn a) -> Set (Horn a)
canonicize = filter (not . isTrivial)

-- | Resolve two horn clauses over a given variable @x@.
-- Will return @Nothing@ if there can be no resolution over these clauses, e.g. 
-- if @x@ does not appear negated in one and clause and non-negated in another.
resolve :: forall a . Ord a => a -> Horn a -> Horn a -> Maybe (Horn a)
resolve x a b = resolveInner a b <|> resolveInner b a
  where
    -- Resolve with the first head as the resolvent, ensuring that it is @x@.
    -- If this doesn't work in @resolve@, we swap the order and try again.
    resolveInner :: Horn a -> Horn a -> Maybe (Horn a)
    resolveInner (Horn Nothing _) _ = Nothing
    resolveInner (Horn (Just head1) body1) (Horn mayHead2 body2)
        | head1 /= x             = Nothing
        | head1 `notElem` body2  = Nothing
        | Just head1 == mayHead2 = Nothing
        | otherwise = Just (Horn mayHead2 $ delete x $ body1 `union` body2)


-- | Use the resolution rule to remove a variable @x@ from a conjunctive set
-- of horn clauses, i.e. @resolve@ generalised to sets of clauses.
remove :: Ord a => a -> Set (Horn a) -> Set (Horn a)
remove x (canonicize -> clauses) =
    let
        -- Then we partition into groups based on the membership of @x@.
        inHead = filter isInHead clauses
        inBody = filter isInBody clauses
        inNone = filter (liftA2 (&&) (not . isInHead) (not . isInBody)) clauses
    in  union inNone . fromList $ do
            bases <- over bodyL (x `delete`) <$> toList inBody
            extra <- view bodyL <$> toList inHead
            return $ bases & bodyL %~ (`union` extra)
  where
    isInHead (Horn head _) = Just x == head
    isInBody (Horn _ body) = x `elem` body


-- | Saturate a conjunctive set of horn clauses under resolution.
saturate :: Ord a => Set (Horn a) -> Set (Horn a)
saturate clauses = go (saturate clauses) clauses
  where
    go curr prev | curr == prev = prev
                 | otherwise    = go (layer curr) curr

    layer clauses' =
        let vars = unions (map variables clauses')
        in  unions $ map (`remove` clauses') vars


-- | Determine if a conjunctive set of horn clauses is unsatisfiable.
-- TODO: This is done naively, not really utilising the special form of horn
-- clauses, for which satisfiability can be done much more efficently(?).
-- A non-demo version should probably change this, or use an external solver.
unsat :: Ord a => Set (Horn a) -> Bool
unsat (canonicize -> clauses) =
    let noFreeVars = foldr (\x acc -> canonicize $ remove x acc)
                           clauses
                           (unions $ map variables clauses)
    -- If clauses is @{}@ (which is @T@) then the expression is sat.
    in  (not . null) noFreeVars