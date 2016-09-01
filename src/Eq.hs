{-# LANGUAGE
  DataKinds,
  FlexibleInstances,
  FunctionalDependencies,
  MultiParamTypeClasses,
  PolyKinds,
  TypeFamilies,
  UndecidableInstances
 #-}

module Eq where

class EQ (x::k) (y::k) (b::Bool) | x y -> b
instance {-# OVERLAPPING #-} EQ x x True
instance {-# OVERLAPPING #-} (b ~ False) => EQ x y b
