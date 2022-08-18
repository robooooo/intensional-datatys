{-# LANGUAGE CPP #-}

module Intensional.Ubiq where

import qualified GhcPlugins as GHC
import Control.Monad (when)
import Debug.Trace (traceM, trace)

-- Ubiquitous functions, they're found everywhere

debugging :: Bool
debugging = 
#ifdef DEBUG
  True
#else
  False
#endif

debugTrace :: Applicative f => String -> f ()
debugTrace what = when debugging $ traceM ("[TRACE] " <> what) 

-- | Used to log the saturation/restriction process.
saturationLogging :: Bool
saturationLogging = 
#if SATLOG
    True
#else
    False
#endif

-- satTrace :: Applicative f => String -> f ()
satTrace :: String -> p -> p
satTrace what ret = 
    if saturationLogging 
    then trace ("[SAT  ] " ++ what) ret 
    else ret 

traceSpan :: GHC.SrcSpan -> String
traceSpan s = GHC.showSDocUnsafe (GHC.ppr s)