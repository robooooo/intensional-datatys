{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Intensional.Horn.Constraints where


import           Binary
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
    deriving (Eq, Ord)
makeLensesFor
    [("atomName", "_name"), ("atomRVar", "_rvar")]
    ''Atom

type HornSet = Set HornConstraint
type HornScheme = SchemeGen HornSet TyCon

data HornConstraint = HornConstraint
    { hornConLeftSpan  :: Maybe SrcSpan
    , hornConRightSpan :: Maybe SrcSpan
    , hornConKName     :: Maybe Name
    , hornConInfo      :: CInfo
    , hornConInner     :: Horn Atom
    }
makeLensesFor
    [ ("hornConLeftSpan", "_lspan")
    , ("hornConRightSpan", "_rspan")
    , ("hornConKName", "_kname")
    , ("hornConInfo", "_cinfo")
    , ("hornConInner", "_horn")]
    ''HornConstraint

-- | Used for instances on HornConstraint, to select which fields should be
-- ignored in @Eq@ and @Ord@ instances.
hcProj :: HornConstraint -> (Maybe Name, Horn Atom)
hcProj (HornConstraint _ _ kn _ horn) = (kn, horn)

-- deriving instance Ord HornConstraint
-- deriving instance Eq HornConstraint
instance Eq HornConstraint where
    hca == hcb = (==) (hcProj hca) (hcProj hcb)
instance Ord HornConstraint where
    compare hca hcb = compare (hcProj hca) (hcProj hcb)

-- | @resolve@ that propagates @SrcSpan@ and naming information.
resolveCons
    :: CInfo -> HornConstraint -> HornConstraint -> Maybe HornConstraint
resolveCons ci left right = addInfo
    <$> resolve (view _horn left) (view _horn right)
  where
    addInfo horn = HornConstraint { hornConLeftSpan  = view _lspan left
                                  , hornConRightSpan = view _rspan right
                                  , hornConKName     = view _kname left
                                  , hornConInner     = horn
                                  , hornConInfo      = ci
                                  }

saturateCons :: CInfo -> HornSet -> HornSet
saturateCons ci = saturateUnder (resolveCons ci)

instance Binary Atom where
    put_ bh (Atom k rv) = put_ bh (k, rv)
    get bh = uncurry Atom <$> get bh

instance Binary HornConstraint where
    put_ bh (HornConstraint sl sr kn ci horn) = put_ bh (sl, sr, kn, ci, horn)
    get bh = uncurry5 HornConstraint <$> get bh
        where uncurry5 f (a, b, c, d, e) = f a b c d e

instance Refined Atom where
    domain (Atom _ x) = I.singleton x
    rename x y (Atom k rv) | rv == x   = Atom k y
                           | otherwise = Atom k rv
    prpr m (Atom k x) = hcat [m x, "_", ppr k]

instance Refined HornConstraint where
    domain = domain . view _horn
    rename x y = over _horn (rename x y)
    prpr m hc =
        let HornConstraint _ _ kn (CInfo _ sspn) horn = hc
        in  hcat
                [ "HornConstraint(loc: "
                , ppr sspn
                , ", "
                , "kn: "
                , ppr kn
                , ", "
                , prpr m horn
                , ")"
                ]
