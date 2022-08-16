module Display where

import           Data.Aeson
import qualified Data.Map                      as Map
import           GHC.Generics                   ( Generic )
import           GhcPlugins
import           Intensional.Constraints
import           Intensional.Constructors
import           Intensional.InferM
import           Intensional.Scheme
import           PprColour
import           System.Directory

data Benchmark = Benchmark
    { times :: [Integer]
    , avg   :: Integer
    , bigN  :: Int
    , bigK  :: Int
    , bigD  :: Int
    , bigV  :: Int
    , bigI  :: Int
    }
    deriving Generic

instance ToJSON Benchmark
instance FromJSON Benchmark


{-|
    Given the name of a benchmark @n@ and a beginning @t0@ and end 
    time @t1@ and statistics @ss@ on the run, @recordBenchmarks n (t0, t1) ss@
    is the IO action that writes the benchmark data to a JSON file.
-}
recordBenchmarks :: String -> (Integer, Integer) -> Stats -> IO ()
recordBenchmarks name (t0, t1) stats = do
    exist <- doesFileExist "benchmark.json"
    if exist
        then decodeFileStrict "benchmark.json" >>= \case
            Nothing -> encodeFile "benchmark.json" (Map.singleton name new)
            Just bs -> case Map.lookup name bs of
                Nothing -> encodeFile "benchmark.json" (Map.insert name new bs)
                Just bench -> do
                    let
                        bench' = updateAverage
                            $ bench { times = (t1 - t0) : times bench }
                    encodeFile "benchmark.json" (Map.insert name bench' bs)
        else encodeFile "benchmark.json" (Map.singleton name new)
  where
    updateAverage b =
        b { avg = sum (times b) `div` toInteger (length (times b)) }
    new = Benchmark { bigN  = cntN stats
                    , bigD  = maxD stats
                    , bigV  = rVar stats
                    , bigK  = maxK stats
                    , bigI  = maxI stats
                    , times = [t1 - t0]
                    , avg   = t1 - t0
                    }

-- | @SDoc@ does not implement @Eq@/@Ord@ for unknown reasons.
-- I wanted to filter duplicate errors, so this has to be polymorphic over the
-- type of names.
data TypeError name = TypeError
    { constructorName :: name
    , mainLoc         :: SrcSpan
    , leftLoc         :: SrcSpan
    , rightLoc        :: SrcSpan
    , mName           :: Module
    }
    deriving (Eq, Ord)

makeSetErrors :: [Atomic] -> [TypeError SDoc]
makeSetErrors = fmap mkErr
  where
    mkErr a = TypeError { constructorName = (ppr . left) a
                        , rightLoc        = (getLocation . right) a
                        , leftLoc         = (getLocation . left) a
                        , mainLoc         = spanInfo a
                        , mName           = modInfo a
                        }

makeHornErrors :: HornSet -> [TypeError SDoc]
makeHornErrors _ = trace "Displaying horn errors is not implemented!" []
    -- mkErr hc = do
    --     hornHead <- view (_horn . _head) hc
    --     headSpan <- atomSpan hornHead
    --     -- The body of this horn clause should have one atom with a @SrcSpan@.
    --     -- This is the left side, whereas the others are any guards.
    --     let hornBody = view (_horn . _body . to toList) hc
    --         withSpan = catMaybes
    --             (hornBody <&> \atom -> case atomSpan atom of
    --                 Just loc -> Just (loc, atomName atom)
    --                 Nothing  -> Nothing
    --             )
    --     Monad.guard $ (not . List.null) withSpan
    --     let (leftSpan, leftName) = case withSpan of
    --             [(ls, ln)] -> (ls, ln)
    --             _          -> error "More than one atom is has a span!"

    --     return $ TypeError { mName           = view (_cinfo . to prov) hc
    --                        , mainLoc         = view (_cinfo . to sspn) hc
    --                        , constructorName = leftName
    --                        , rightLoc        = headSpan
    --                        , leftLoc         = leftSpan
    --                        }

    -- pprName err = err { constructorName = (ppr . constructorName) err }


-- instance ShowTypeError Atomic where
--     mainLoc   = spanInfo
--     leftLoc   = getLocation . left
--     rightLoc  = getLocation . right
--     printLeft = ppr . left

-- instance ShowTypeError HornConstraint where
--     mainLoc   = view (_cinfo . to sspn)
--     leftLoc   = const $ UnhelpfulSpan "Nowhere"
--     rightLoc  = const $ UnhelpfulSpan "Nowhere"
--     printLeft = const "Placeholder"

{-|
  Given a trivially unsat constraint @a@, @showTypeError a@ is the 
  message that we will print out to the user as an SDoc.
-}
showTypeError :: TypeError SDoc -> SDoc
showTypeError a =
    blankLine
        $+$ coloured (colBold Prelude.<> colWhiteFg)
                     (hang topLine 2 (hang msgLine1 2 msgLine2))
        $+$ blankLine
  where
    topLine =
        ppr (mainLoc a)
            GhcPlugins.<> colon
            <+>           coloured (sWarning defaultScheme) (text "warning:")
            <+>           lbrack
            GhcPlugins.<> coloured (sWarning defaultScheme) (text "Intensional")
            GhcPlugins.<> rbrack
    msgLine1 =
        text "Could not verify that"
            <+> quotes (constructorName a)
            <+> text "from"
            <+> ppr (leftLoc a)
    msgLine2 = text "cannot reach the incomplete match at" <+> ppr (rightLoc a)
