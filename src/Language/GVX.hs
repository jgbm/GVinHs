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

module Language.GVX where

import Prelude hiding ((^), (<*>), (+))

import Language.LLC
import Language.ST
import Language.GV

data AP (s :: *)

class (GV c repr) => GVX (ap :: * -> *) (c :: * -> *) (repr :: Nat -> Bool -> [Maybe Nat] -> [Maybe Nat] -> * -> *) | repr -> c ap
    where amb :: repr vid tf i o a -> repr vid tf i o a -> repr vid tf i o a
          spawn :: repr vid tf i o (One -<> One) -> repr vid tf i o One
          close :: repr vid tf i o (c EndOut) -> repr vid tf i o One
          new :: repr vid tf i o (ap s ->> t) -> repr vid tf i o t
          accept :: repr vid tf i o (ap s) -> repr vid tf i o (c s)
          request :: repr vid tf i o (ap s) -> repr vid tf i o (c (Dual s))

type DefnGVX tf m c ap a =
    forall repr i vid
    . (LLC repr, GV c repr, GVX ap c repr, MrgLs i)
    => repr vid tf i i a
defnGVX :: DefnGVX tf m c ap a -> DefnGVX tf m c ap a
defnGVX x = x
