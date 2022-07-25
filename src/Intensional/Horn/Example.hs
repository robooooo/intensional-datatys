module Intensional.Horn.Example where

import qualified Data.Map.Strict               as Map
import qualified Data.Set                      as Set
import           Data.Set                       ( Set )
import           Intensional.Horn.Clause
import           Intensional.Horn.Constraint

example :: Set Constr
example = Set.fromList
    [ (Set.empty, Constructors (Set.singleton "Lam"), Refined 1 "Lam")
    , (Set.singleton ("FVr", 2), Refined 2 "Lam", Refined 3 "Lam")
    , (Set.empty, Refined 1 "Lam", Refined 2 "Lam")
    , (Set.empty, Refined 3 "Lam", Constructors (Set.fromList ["FVr", "Cst"]))
    -- , (Set.empty, Refined 1 "Lam", Constructors Set.empty)
    -- , (Set.empty, Constructors Set.empty, Refined 1 "Lam")
    ]

exampleProp :: Set (Horn Atom')
exampleProp = toHorn' env example
  where
    env = Map.fromList
        [ ("Arith", Set.fromList ["Lit", "Add"])
        , ("Lam"  , Set.fromList ["Cst", "App"])
        ]
