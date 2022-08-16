{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Intensional.Horn.Constraints where


import           Binary
import           Control.Applicative            ( Alternative((<|>)) )
import           Control.Monad                  ( liftM2 )
import qualified Data.IntSet                   as I
import           Data.Set                       ( Set )
import qualified GHC
import           GhcPlugins
import           Intensional.Constraints       as Constraints
import           Intensional.Horn.Clause        ( Horn(..)
                                                , resolve
                                                , saturateUnder
                                                )
import           Intensional.Scheme
import           Intensional.Types
import           Lens.Micro              hiding ( _head )
import           Lens.Micro.Extras              ( view )
import           Lens.Micro.TH                  ( makeLensesFor )

-- | The type of propositional atoms.
-- Pair of a constructor and a refinement variable.
-- May also include a @SrcSpan@.
data Atom = Atom
    { atomName :: GHC.Name
    , atomRVar :: RVar
    }
makeLensesFor
    [("atomName", "_name"), ("atomRVar", "_rvar")]
    ''Atom

type HornSet = Set HornConstraint
type HornScheme = SchemeGen HornSet TyCon

instance Eq Atom where
    a == b = atomName a == atomName b && atomRVar a == atomRVar b
deriving instance Ord Atom


data HornConstraint = HornConstraint
    { hornConLeftSpan  :: Maybe SrcSpan
    , hornConRightSpan :: Maybe SrcSpan
    , hornConInfo      :: CInfo
    , hornConInner     :: Horn Atom
    }
    deriving (Eq, Ord)
makeLensesFor
    [ ("hornConLeftSpan", "_lspan")
    , ("hornConRightSpan", "_rspan")
    , ("hornConInfo", "_cinfo")
    , ("hornConInner", "_horn")]
    ''HornConstraint

-- | @resolve@ that propagates @SrcSpan@ and naming information.
resolveCons
    :: CInfo -> HornConstraint -> HornConstraint -> Maybe HornConstraint
resolveCons ci left right = addInfo
    <$> resolve (view _horn left) (view _horn right)
  where
    addInfo horn = HornConstraint
        { hornConLeftSpan  = liftM2 combineSrcSpans
                                    (view _lspan left)
                                    (view _lspan right)
        , hornConRightSpan = view _rspan right <|> view _rspan left
        , hornConInner     = horn
        , hornConInfo      = ci
        }

saturateCons :: CInfo -> HornSet -> HornSet
saturateCons ci = saturateUnder (resolveCons ci)

instance Binary Atom where
    put_ bh (Atom k rv) = put_ bh (k, rv)
    get bh = uncurry Atom <$> get bh

instance Binary HornConstraint where
    put_ bh (HornConstraint sl sr ci horn) = put_ bh (sl, sr, ci, horn)
    get bh = HornConstraint <$> get bh <*> get bh <*> get bh <*> get bh

instance Refined Atom where
    domain (Atom _ x) = I.singleton x
    rename x y (Atom k rv) | rv == x   = Atom k y
                           | otherwise = Atom k rv
    prpr m (Atom k x) = hcat [m x, "_", ppr k]

instance Refined HornConstraint where
    domain = domain . view _horn
    rename x y = over _horn (rename x y)
    prpr m hc =
        let HornConstraint _ _ (CInfo prov sspn) horn = hc
        in  hcat
                [ "HornConstraint("
                , hcat ["CInfo(", ppr prov, ", ", ppr sspn, ")"]
                , ", "
                , prpr m horn
                , ")"
                ]
