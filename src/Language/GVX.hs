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

class (GV c repr) => GVX (ap :: * -> *) (c :: * -> *) (repr :: Bool -> [Maybe Nat] -> [Maybe Nat] -> * -> *) | repr -> c ap
    where amb     :: repr tf i o a -> repr tf i o a -> repr tf i o a
          spawn   :: repr tf i o (One -<> One  )    -> repr tf i o One
          close   :: repr tf i o (c EndOut)         -> repr tf i o One
          new     :: repr tf i o (ap s ->> t)       -> repr tf i o t
          accept  :: repr tf i o (ap s)             -> repr tf i o (c s)
          request :: repr tf i o (ap s)             -> repr tf i o (c (Dual s))

type DefnGVX tf m c ap a =
    forall repr i
    . (LLC repr, GV c repr, GVX ap c repr, MrgLs i)
    => repr tf i i a
defnGVX :: DefnGVX tf m c ap a -> DefnGVX tf m c ap a
defnGVX x = x
