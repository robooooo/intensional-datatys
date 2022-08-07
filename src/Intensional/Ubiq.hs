{-# LANGUAGE CPP #-}

module Intensional.Ubiq where

import qualified GhcPlugins as GHC
import Control.Monad (when)
import Debug.Trace (traceM)

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

traceSpan :: GHC.SrcSpan -> String
traceSpan s = GHC.showSDocUnsafe (GHC.ppr s)