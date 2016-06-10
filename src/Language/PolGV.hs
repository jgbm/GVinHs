{-# LANGUAGE
  DataKinds,
  FlexibleContexts,
  FunctionalDependencies,
  GADTs,
  RankNTypes,
  TypeFamilies,
  TypeOperators
 #-}

module Language.PolGV where

import Prelude hiding ((^), (<*>), (+))

import Language.LLC
import Language.ST

-- session types
data OutShift s
data InShift s

-- duality
type instance Dual (OutShift s) = InShift (Dual s)
type instance Dual (InShift s)  = OutShift (Dual s)

class GV (os :: * -> *) (is :: * -> *) (repr :: Nat -> Bool -> [Maybe Nat] -> [Maybe Nat] -> * -> *) | repr -> os is where
  send :: repr vid tf i h t -> repr vid tf h o (os (t <!> s)) -> repr vid tf i o (os s)
  recv :: repr vid tf i o (is (t <?> s)) ->                      repr vid tf i o (t * is s)
  wait :: repr vid tf i o (is EndIn) ->                          repr vid tf i o One
  fork :: Dual (Dual s) ~ s =>
          repr vid tf i o (os s -<> os EndOut) ->                repr vid tf i o (is (Dual s))
  osh  :: repr vid tf i o (is (InShift s)) ->                    repr vid tf i o (os s)
  ish  :: repr vid tf i o (os (OutShift s)) ->                   repr vid tf i o (is s)
  chooseLeft  :: repr vid tf i o (os (s1 <++> s2)) ->            repr vid tf i o (os s1)
  chooseRight :: repr vid tf i o (os (s1 <++> s2)) ->            repr vid tf i o (os s2)
  offer       :: (Dual (Dual s1) ~ s1, Dual (Dual s2) ~ s2) =>
                 repr vid tf i h (is (s1 <&&> s2)) ->
                   repr vid tf h o (is s1 -<> t) ->
                     repr vid tf h o (is s2 -<> t) ->            repr vid tf i o t

chooseLeft'
  :: (LLC repr, GV os is repr, Dual (Dual s) ~ s)
  => repr vid False i i (os ((is s + is s') <!> EndOut) -<> os (Dual s))
chooseLeft' = llam (\m -> osh (fork (llam (\x -> send (inl (ish x)) m))))

type DefnGV os is tf a =
    forall repr i vid v v'
    . (LLC repr, GV os is repr, MrgLs i)
    => repr vid tf i i a
defnGV :: DefnGV os is tf a -> DefnGV os is tf a
defnGV x = x

bind e f = f ^ e
ret e = e
