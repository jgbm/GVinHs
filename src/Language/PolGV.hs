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
  send :: repr v tf i h t -> repr v tf h o (os (t <!> s)) -> repr v tf i o (os s)
  recv :: repr v tf i o (is (t <?> s)) ->                    repr v tf i o (t * is s)
  wait :: repr v tf i o (is EndIn) ->                        repr v tf i o One
  fork :: Dual (Dual s) ~ s =>
          repr v tf i o (os s -<> os EndOut) ->              repr v tf i o (is (Dual s))
  osh  :: repr v tf i o (is (InShift s)) ->                  repr v tf i o (os s)
  ish  :: repr v tf i o (os (OutShift s)) ->                 repr v tf i o (is s)
  chooseLeft  :: repr v tf i o (os (s1 <++> s2)) ->          repr v tf i o (os s1)
  chooseRight :: repr v tf i o (os (s1 <++> s2)) ->          repr v tf i o (os s2)
  offer       :: (Dual (Dual s1) ~ s1, Dual (Dual s2) ~ s2) =>
                 repr v tf i h (is (s1 <&&> s2)) ->
                   repr v tf h o (is s1 -<> t) ->
                     repr v tf h o (is s2 -<> t) ->          repr v tf i o t

chooseLeft'
  :: (LLC repr, GV os is repr, Dual (Dual s) ~ s)
  => repr v False i i (os ((is s + is s') <!> EndOut) -<> os (Dual s))
chooseLeft' = llam (\m -> osh (fork (llam (\x -> send (inl (ish x)) m))))

type DefnGV os is tf a =
    forall repr i v
    . (LLC repr, GV os is repr, MrgLs i)
    => repr v tf i i a
defnGV :: DefnGV os is tf a -> DefnGV os is tf a
defnGV x = x

bind e f = f ^ e
ret e = e
