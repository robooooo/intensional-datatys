module Display where

import           Data.Aeson
import qualified Data.Map                      as Map
import           GHC.Generics                   ( Generic )
import           GhcPlugins
import           Intensional.Constraints
import           Intensional.Constructors
import           Intensional.InferM
import           Intensional.Scheme
import           Lens.Micro
import           Lens.Micro.Extras
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

class ShowTypeError ty where
    mainLoc   :: ty -> SrcSpan
    leftLoc   :: ty -> SrcSpan
    rightLoc  :: ty -> SrcSpan
    printLeft :: ty -> SDoc

instance ShowTypeError Atomic where
    mainLoc   = spanInfo
    leftLoc   = getLocation . left
    rightLoc  = getLocation . right
    printLeft = ppr . left

instance ShowTypeError HornConstraint where
    mainLoc   = view (_cinfo . to sspn)
    leftLoc   = const $ UnhelpfulSpan "Placeholder"
    rightLoc  = const $ UnhelpfulSpan "Placeholder"
    printLeft = const "PlaceHolder"

{-|
  Given a trivially unsat constraint @a@, @showTypeError a@ is the 
  message that we will print out to the user as an SDoc.
-}
showTypeError :: ShowTypeError a => a -> SDoc
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
            <+> quotes (printLeft a)
            <+> text "from"
            <+> ppr (leftLoc a)
    msgLine2 = text "cannot reach the incomplete match at" <+> ppr (rightLoc a)
