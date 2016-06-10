{-# LANGUAGE
  ConstraintKinds,
  DataKinds,
  FlexibleContexts,
  FunctionalDependencies,
  GADTs,
  KindSignatures,
  NoMonomorphismRestriction,
  RankNTypes,
  TypeFamilies,
  TypeOperators,
  TypeSynonymInstances
 #-}

module Language.ClosedGV where

import Prelude hiding ((^), (<*>), (+))

import Language.LLC
import Data.Proxy

-- session types
data Sess = forall (t :: *).Output t Sess
          | EndOut
          | forall (t :: *).Input t Sess
          | EndIn
          | Choose Sess Sess
          | Offer Sess Sess
-- data Output t s
-- data EndOut
-- data Input t s
-- data EndIn
-- data Choose s1 s2
-- data Offer s1 s2

-- infix aliases
type t <!> s = Output t s
type t <?> s = Input t s
type s1 <++> s2 = Choose s1 s2
type s1 <&&> s2 = Offer s1 s2

-- default wrapper for session types
data ST (s :: Sess) where
  SOutput :: Session s => Proxy t -> ST s -> ST (t <!> s)
  SEndOut :: ST EndOut
  SInput :: Session s => Proxy t -> ST s -> ST (t <?> s)
  SEndIn :: ST EndIn
  SChoose :: (Session s1, Session s2) => ST s1 -> ST s2 -> ST (s1 <++> s2)
  SOffer :: (Session s1, Session s2) => ST s1 -> ST s2 -> ST (s1 <&&> s2)

class (Dual (Dual s) ~ s, Flip (Pol s) ~ Pol (Dual s)) => Session (s :: Sess) where
  polarity :: SPolarity s
  sing :: ST s
instance Session s => Session (t <!> s) where
  polarity = SO
  sing = SOutput Proxy sing
instance Session EndOut where
  polarity = SO
  sing = SEndOut
instance Session s => Session (t <?> s) where
  polarity = SI
  sing = SInput Proxy sing
instance Session EndIn where
  polarity = SI
  sing = SEndIn
instance (Session s1, Session s2) => Session (s1 <++> s2) where
  polarity = SO
  sing = SChoose sing sing
instance (Session s1, Session s2) => Session (s1 <&&> s2) where
  polarity = SI
  sing = SOffer sing sing

-- polarity
data Polarity = O | I

type family Pol (s :: Sess) :: Polarity
type instance Pol (t <!> s) = O
type instance Pol EndOut = O
type instance Pol (t <?> s) = I
type instance Pol EndIn = I
type instance Pol (s1 <++> s2) = O
type instance Pol (s1 <&&> s2) = I

data SPolarity (s :: Sess) where
  SO :: Pol s ~ O => SPolarity s
  SI :: Pol s ~ I => SPolarity s

type family Flip (p :: Polarity) :: Polarity where
  Flip O = I
  Flip I = O

-- duality
type family Dual (s :: Sess) :: Sess
type instance Dual (t <!> s)    = t <?> Dual s
type instance Dual EndOut       = EndIn
type instance Dual (t <?> s)    = t <!> Dual s
type instance Dual EndIn        = EndOut
type instance Dual (s1 <++> s2) = Dual s1 <&&> Dual s2
type instance Dual (s1 <&&> s2) = Dual s1 <++> Dual s2

type DualSession (s :: Sess) = (Session s, Session (Dual s))

class GV (st :: Sess -> *) (repr :: Nat -> Bool -> [Maybe Nat] -> [Maybe Nat] -> * -> *) | repr -> st where
  send :: DualSession s => repr vid tf i h t -> repr vid tf h o (st (t <!> s)) -> repr vid tf i o (st s)
  recv :: DualSession s => repr vid tf i o (st (t <?> s)) ->                      repr vid tf i o (t * st s)
  wait :: repr vid tf i o (st EndIn) ->                                       repr vid tf i o One
  fork :: (Session s, Session (Dual s)) => repr vid tf i o (st s -<> st EndOut) ->                repr vid tf i o (st (Dual s))
  chooseLeft  :: (DualSession s1, DualSession s2)
              => repr vid tf i o (st (s1 <++> s2)) ->                         repr vid tf i o (st s1)
  chooseRight :: (DualSession s1, DualSession s2)
              => repr vid tf i o (st (s1 <++> s2)) ->                         repr vid tf i o (st s2)
  offer       :: (DualSession s1, DualSession s2)
              => repr vid tf i h (st (s1 <&&> s2)) ->
                   repr vid tf h o (st s1 -<> t) ->
                     repr vid tf h o (st s2 -<> t) ->                         repr vid tf i o t

-- we can encode choice
chooseLeft'
  :: (LLC repr, GV st repr, DualSession s1, DualSession s2)
     => repr vid False i i (st ((st s1 + st s2) <!> EndOut) -<> st (Dual s1))
chooseLeft' = llam (\m -> fork (llam (\x -> send (inl x) m)))

type DefnGV st tf a =
    forall repr i vid v v'
    . (LLC repr, GV st repr, MrgLs i)
    => repr vid tf i i a
defnGV :: DefnGV st tf a -> DefnGV st tf a
defnGV x = x

bind e f = f ^ e
ret e = e

easiest =
    defnGV $ fork (llam $ \c -> send (bang (constant 6)) c) `bind` (llam $ \c ->
             recv c                                         `bind` (llp $  \x c ->
             wait c                                         `bind` (llz $
             ret x
    )))
