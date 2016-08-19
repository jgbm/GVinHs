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
    where amb     :: repr v tf i o a -> repr v tf i o a -> repr v tf i o a
          spawn   :: repr v tf i o (One -<> One  )      -> repr v tf i o One
          close   :: repr v tf i o (c EndOut)           -> repr v tf i o One
          new     :: repr v tf i o (ap s ->> t)         -> repr v tf i o t
          accept  :: repr v tf i o (ap s)               -> repr v tf i o (c s)
          request :: repr v tf i o (ap s)               -> repr v tf i o (c (Dual s))

type DefnGVX tf m c ap a =
    forall repr i v
    . (LLC repr, GV c repr, GVX ap c repr, MrgLs i)
    => repr v tf i i a
defnGVX :: DefnGVX tf m c ap a -> DefnGVX tf m c ap a
defnGVX x = x
