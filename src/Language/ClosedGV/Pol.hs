{-# LANGUAGE
  ConstraintKinds,
  DataKinds,
  FlexibleContexts,
  FlexibleInstances,
  GADTs,
  MultiParamTypeClasses,
  RankNTypes,
  ScopedTypeVariables,
  TypeFamilies,
  TypeOperators,
  UndecidableInstances
 #-}

module Language.ClosedGV.Pol where

import Prelude hiding ((^), (<*>), (+))

import Language.LLC
import Language.LLC.Monadic
import Language.LLC.Plain
import Language.ClosedGV
import qualified Language.ST as S
import qualified Language.PolGV as P

import Language.PolGV.CPS

import Control.Monad.Cont

import GVexamples

-- representation for polarisation
newtype RP (os :: * -> *) (is :: * -> *)
           (repr :: Nat -> Bool -> [Maybe Nat] -> [Maybe Nat] -> * -> *)
           (vid :: Nat) (tf::Bool) (hi::[Maybe Nat]) (ho::[Maybe Nat]) a =
  RP {unRP :: (LLC repr, P.GV os is repr, Conv repr) => repr vid tf hi ho a}

-- session type representation for polarisation
data STP (os :: * -> *) (is :: * -> *) (s :: Sess) where
  STPO :: Pol s ~ O => os (SToO s) -> STP os is s
  STPI :: Pol s ~ I => is (SToI s) -> STP os is s

unSTPO :: Pol s ~ O => STP os is s -> os (SToO s)
unSTPO (STPO o) = o

unSTPI :: Pol s ~ I => STP os is s -> is (SToI s)
unSTPI (STPI i) = i

type instance Mon (STP os is s) = Mon' (Pol s) (STP os is s)

type family Mon' (p :: Polarity) (a :: *) :: (* -> *) -> *
type instance Mon' O (STP os is s) = Mon (os (SToO s))
type instance Mon' I (STP os is s) = Mon (is (SToI s))

-- conversion between GV and polarised GV representations
class Conv (repr :: Nat -> Bool -> [Maybe Nat] -> [Maybe Nat] -> * -> *) where
  stoo :: Pol s ~ O => repr vid tf hi ho (STP os is s) -> repr vid tf hi ho (os (SToO s))
  stoi :: Pol s ~ I => repr vid tf hi ho (STP os is s) -> repr vid tf hi ho (is (SToI s))
  otos :: Pol s ~ O => repr vid tf hi ho (os (SToO s)) -> repr vid tf hi ho (STP os is s)
  itos :: Pol s ~ I => repr vid tf hi ho (is (SToI s)) -> repr vid tf hi ho (STP os is s)

-- We want to prove these equations
--
--   S.Dual (SToI s) ~ SToO (Dual s)
--   S.Dual (SToO s) ~ SToI (Dual s)
--
-- in order to derive this equation
--
--   S.Dual (S.Dual (SToI (Dual s))) ~ SToI (Dual s)
--
-- amongst others.

-- dualisation commutes with the transformations
data DualTrans (s :: Sess) where
  DualTrans :: (S.Dual (SToI s) ~ SToO (Dual s),
                S.Dual (SToO s) ~ SToI (Dual s),
                S.Dual (SToI (Dual s)) ~ SToO s,
                S.Dual (SToO (Dual s)) ~ SToI s)
                  => DualTrans s

-- compute the commuting duality laws for a give session type
dualTrans :: ST s -> DualTrans s
dualTrans (SOutput _ s) = case dualTrans s of
                            DualTrans -> DualTrans
dualTrans SEndOut = DualTrans
dualTrans (SInput _ s) = case dualTrans s of
                           DualTrans -> DualTrans
dualTrans SEndIn = DualTrans
dualTrans (SChoose s1 s2) = case (dualTrans s1, dualTrans s2) of
                              (DualTrans, DualTrans) -> DualTrans
dualTrans (SOffer s1 s2) = case (dualTrans s1, dualTrans s2) of
                             (DualTrans, DualTrans) -> DualTrans

--- conversions with shifts where necessary
otosShift :: (P.GV os is repr, Conv repr) =>
               SPolarity s -> repr vid tf hi ho (os (SToO s)) -> repr vid tf hi ho (STP os is s)
otosShift SO = otos
otosShift SI = itos . P.ish

itosShift :: (P.GV os is repr, Conv repr) =>
               SPolarity s -> repr vid tf hi ho (is (SToI s)) -> repr vid tf hi ho (STP os is s)
itosShift SO = otos . P.osh
itosShift SI = itos

-- conversion for the monadic interpretation
instance Conv (RM m) where
  stoo = RM . unRM
  stoi = RM . unRM
  otos = RM . unRM
  itos = RM . unRM

-- conversion for the plain interpretation
instance Conv R where
  stoo = R . unSTPO . unR
  stoi = R . unSTPI . unR
  otos = R . STPO . unR
  itos = R . STPI . unR

--- type families for mapping between GV and polarised types

-- polarised output to GV
type family OToS (o :: *) :: Sess
type instance OToS (t S.<!> o)    = t <!> OToS o
type instance OToS (S.EndOut)     = EndOut
type instance OToS (o1 S.<++> o2) = OToS o1 <++> OToS o2

-- polarised input to GV
type family IToS (i :: *) :: Sess
type instance IToS (t S.<?> i)    = t <?> IToS i
type instance IToS S.EndIn        = EndIn
type instance IToS (i1 S.<&&> i2) = IToS i1 <&&> IToS i2

-- session to polarised output
type family SToO (s :: Sess) :: *
type instance SToO s = SToOShift (Pol s) s

type family SToOShift (p :: Polarity) (s :: Sess) :: *
type instance SToOShift O s = OSToO s
type instance SToOShift I s = P.OutShift (ISToI s)

-- output session to polarised output session
type family OSToO (s :: Sess) :: *
type instance OSToO (t <!> s)    = t S.<!> (SToO s)
type instance OSToO EndOut       = S.EndOut
type instance OSToO (s1 <++> s2) = SToO s1 S.<++> SToO s2

-- session to polarised input
type family SToI (s :: Sess) :: *
type instance SToI s = SToIShift (Pol s) s

type family SToIShift (p :: Polarity) (s :: Sess) :: *
type instance SToIShift I s = ISToI s
type instance SToIShift O s = P.InShift (OSToO s)

-- input session to polarised input session
type family ISToI (s :: Sess) :: *
type instance ISToI (t <?> s)    = t S.<?> SToI s
type instance ISToI EndIn        = S.EndIn
type instance ISToI (s1 <&&> s2) = SToI s1 S.<&&> SToI s2

instance LLC repr => LLC (RP os is repr) where
    llam f         = RP (llam (\x -> unRP (f (RP x))))
    f ^ x          = RP (unRP f ^ unRP x)
    bang x         = RP (bang (unRP x))
    letBang x f    = RP (letBang (unRP x) (\x -> unRP (f (RP x))))
    ulam f         = RP (ulam (\x -> unRP (f (RP x))))
    f $$ x         = RP (unRP f $$ unRP x)
    x <*> y        = RP (unRP x <*> unRP y)
    letStar xy f   = RP (letStar (unRP xy) (\x y -> unRP (f (RP x) (RP y))))
    one            = RP one
    letOne x y     = RP (letOne (unRP x) (unRP y))
    top            = RP top
    x & y          = RP (unRP x & unRP y)
    pi1 x          = RP (pi1 (unRP x))
    pi2 x          = RP (pi2 (unRP x))
    inl x          = RP (inl (unRP x))
    inr x          = RP (inr (unRP x))
    letPlus xy f g = RP (letPlus (unRP xy) (\x -> unRP (f (RP x))) (\y -> unRP (g (RP y))))
    abort x        = RP (abort (unRP x))
    constant x     = RP (constant x)
    f $$$ x        = RP (unRP f $$$ unRP x)

instance (LLC repr, P.GV os is repr, Conv repr) => GV (STP os is) (RP os is repr) where
  send (RP m)
       (RP (n :: (P.GV os is repr, Conv repr) =>
                   repr vid tf h o (STP os is (t <!> s)))) =
                     RP (otosShift (polarity :: SPolarity s) (P.send m (stoo n)))
  -- This use of letStar for meta programming depends on Or being
  -- defined as a closed overlapping type family
  recv (RP (m :: (P.GV os is repr, Conv repr) =>
                   repr vid tf h o (STP os is (t <?> s)))) =
    RP (letStar (P.recv (stoi m)) (\x y -> x <*> itosShift (polarity :: SPolarity s) y))
  wait (RP m) = RP (P.wait (stoi m))
  -- To get fork to work, we need to ensure that the appropriate
  -- duality constraint holds. We do this by using a closed version of
  -- GV and analysing the appropriate singleton type representation of
  -- the session type.
  --
  -- To get it to type check we pre- and post- compose the function
  -- argument with appropriate coercions.
  fork (RP (m :: (P.GV os is repr, Conv repr) =>
                   repr vid tf i o (STP os is s -<> STP os is EndOut))) =
    let p = polarity :: SPolarity s in
    let p' = polarity :: SPolarity (Dual s) in
    let m' = compose ^ (llam (\x -> stoo x)) ^ (compose ^ m ^ (llam (\x -> otosShift p x))) in
    case (dualTrans (sing :: ST s), dualTrans (sing :: ST (Dual s))) of
      (DualTrans, DualTrans) ->
         RP (itosShift p' (P.fork m'))
  chooseLeft (RP (m :: (P.GV os is repr, Conv repr) => repr vid tf i o (STP os is (s1 <++> s2)))) =
    RP (otosShift (polarity :: SPolarity s1) (P.chooseLeft (stoo m)))
  chooseRight (RP (m :: (P.GV os is repr, Conv repr) => repr vid tf i o (STP os is (s1 <++> s2)))) =
    RP (otosShift (polarity :: SPolarity s2) (P.chooseRight (stoo m)))
  offer (RP (m :: (P.GV os is repr, Conv repr) => repr vid tf i h (STP os is (s1 <&&> s2))))
        (RP n1) (RP n2) =
    let m' = stoi m in
    let n1' = compose ^ n1 ^ llam (\x1 -> itosShift (polarity :: SPolarity s1) x1) in
    let n2' = compose ^ n2 ^ llam (\x2 -> itosShift (polarity :: SPolarity s2) x2) in
    case (dualTrans (sing :: ST s1), dualTrans (sing :: ST s2)) of
      (DualTrans, DualTrans) ->
        RP (P.offer m' n1' n2')

evalPol :: (LLC repr, P.GV os is repr, Conv repr) => RP os is repr vid tf '[] '[] a -> repr vid tf '[] '[] a
evalPol (RP m) = m

evalPolCont :: RP OST IST (RM (Cont r)) vid tf '[] '[] a -> RM (Cont r) vid tf '[] '[] a
evalPolCont = evalPol
