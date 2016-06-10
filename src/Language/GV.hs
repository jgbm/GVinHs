{-# LANGUAGE
  ConstraintKinds,
  DataKinds,
  FlexibleContexts,
  FunctionalDependencies,
  GADTs,
  NoMonomorphismRestriction,
  RankNTypes,
  TypeFamilies,
  TypeOperators
 #-}

module Language.GV where

import Prelude hiding ((^), (<*>), (+))

import Language.LLC
import Language.ST
import Data.Proxy

-- default wrapper for session types (singleton type)
data ST (s :: *) where
  SOutput :: Session s => Proxy t -> ST s -> ST (t <!> s)
  SEndOut :: ST EndOut
  SInput :: Session s => Proxy t -> ST s -> ST (t <?> s)
  SEndIn :: ST EndIn
  SChoose :: (Session s1, Session s2) => ST s1 -> ST s2 -> ST (s1 <++> s2)
  SOffer :: (Session s1, Session s2) => ST s1 -> ST s2 -> ST (s1 <&&> s2)

class (Dual (Dual s) ~ s, Flip (Pol s) ~ Pol (Dual s)) => Session (s :: *) where
  polarity :: SPolarity s
  sing :: ST s
instance Session s => Session (t <!> s) where
  polarity = SO
  sing =  SOutput Proxy sing
instance Session EndOut where
  polarity = SO
  sing = SEndOut
instance Session s => Session (t <?> s) where
  polarity = SI
  sing =  SInput Proxy sing
instance Session EndIn where
  polarity = SI
  sing = SEndIn
instance (Session s1, Session s2) => Session (s1 <++> s2) where
  polarity = SO
  sing =  SChoose sing sing
instance (Session s1, Session s2) => Session (s1 <&&> s2) where
  polarity = SI
  sing =  SOffer sing sing

type DualSession (s :: *) = (Session s, Session (Dual s))

class GV (st :: * -> *) (repr :: Nat -> Bool -> [Maybe Nat] -> [Maybe Nat] -> * -> *) | repr -> st where
  send :: DualSession s => repr vid tf i h t -> repr vid tf h o (st (t <!> s)) -> repr vid tf i o (st s)
  recv :: DualSession s => repr vid tf i o (st (t <?> s)) ->                      repr vid tf i o (t * st s)
  wait :: repr vid tf i o (st EndIn) ->                                           repr vid tf i o One
  fork :: DualSession s => repr vid tf i o (st s -<> st EndOut) ->                repr vid tf i o (st (Dual s))
  chooseLeft  :: (DualSession s1, DualSession s2)
              => repr vid tf i o (st (s1 <++> s2)) ->                             repr vid tf i o (st s1)
  chooseRight :: (DualSession s1, DualSession s2)
              => repr vid tf i o (st (s1 <++> s2)) ->                             repr vid tf i o (st s2)
  offer       :: (DualSession s1, DualSession s2)
              => repr vid tf i h (st (s1 <&&> s2)) ->
                   repr vid tf h o (st s1 -<> t) ->
                     repr vid tf h o (st s2 -<> t) ->                             repr vid tf i o t

-- we can encode choice
chooseLeft'
  :: (LLC repr, GV st repr, DualSession s1, DualSession s2)
     => repr vid False i i (st ((st s1 + st s2) <!> EndOut) -<> st (Dual s1))
chooseLeft' = llam (\m -> fork (llam (\x -> send (inl x) m)))

type DefnGV st tf a =
    forall repr i vid
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
