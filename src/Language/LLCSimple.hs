{-# LANGUAGE
  DataKinds,
  FlexibleContexts,
  FlexibleInstances,
  FunctionalDependencies,
  RankNTypes,
  ScopedTypeVariables,
  TypeFamilies,
  TypeOperators,
  UndecidableInstances
#-}

-- Based on Jeff Polakow, "Embedding a Full Linear Lambda Calculus in Haskell"

module Language.LLCSimple where

-- this version omits Top and Zero and hence the need for a flag to
-- indicate whether we can dump the linear context (we never can)

import Prelude hiding((^), (<*>), (+))
import Eq

--
-- Linear type constructors
--
data a -<> b
data a ->> b
data Bang a
-- data Top
data a & b
data One
data a * b
data a + b
-- data Zero
data Base a

infixr 5 -<>
infixr 5 ->>

--
-- linear variable v in Haskell context
--
type LVar repr (x::Nat) a =
    forall (v::Nat)
           (i::[Maybe Nat])
           (o::[Maybe Nat])
    . (Consume x i o, v ~ Length i) => repr i o a

--
-- unrestricted variable in Haskell context
--
type UVar repr a =
    forall (i::[Maybe Nat])
    . repr i i a

--
-- The syntax of LLC.
--
class LLC (repr :: [Maybe Nat]
                -> [Maybe Nat]
                -> *
                -> *
               ) where
  llam
    :: (v ~ Length i)
    => (LVar repr v a -> repr (Just v  ': i)
                              (Nothing ': o)
                              b
       )
    -> repr i o (a -<> b)
  (^)
    :: repr i h (a -<> b)
    -> repr h o a
    -> repr i o b

  bang
    :: repr i i a
    -> repr i i (Bang a)
  letBang
    :: repr i h (Bang a)
    -> (UVar repr a -> repr h o b)
    -> repr i o b

  ulam
    :: (UVar repr a -> repr i o b)
    -> repr i o (a ->> b)
  ($$)
    :: repr i o (a ->> b)
    -> repr o o a
    -> repr i o b

  -- top
  --   :: repr True i i Top

  (&)
    :: repr i o a
    -> repr i o b
    -> repr i o (a & b)
  pi1
    :: repr i o (a & b)
    -> repr i o a
  pi2
    :: repr i o (a & b)
    -> repr i o b

  one
    :: repr i i One
  letOne
    :: repr i h One
    -> repr h o a
    -> repr i o a

  (<*>)
    :: repr i h a
    -> repr h o b
    -> repr i o (a * b)
  letStar
    :: v ~ Length i
    => repr i h (a * b)
    -> (LVar repr v a
        -> LVar repr (S v) b
        -> repr (Just v  ': Just (S v) ': h)
                (Nothing ': Nothing    ': o)
                c
       )
    -> repr i o c

  inl
    :: repr i o a
    -> repr i o (a + b)
  inr
    :: repr i o b
    -> repr i o (a + b)
  letPlus
    :: v ~ Length i
    => repr i h (a + b)
    -> (LVar repr v a -> repr (Just v  ': h)
                              (Nothing ': o)
                              c
       )
    -> (LVar repr v b -> repr (Just v  ': h)
                              (Nothing ': o)
                              c
       )
    -> repr i o c

  constant :: a -> repr i i (Base a)

  ($$$) :: repr i h (Base (a -> b))
        -> repr h o (Base a)
        -> repr i o (Base b)

type Defn a =
    forall repr i v v' . LLC repr => repr i i a
defn :: Defn a -> Defn a
defn x = x


{------------------------------------------------------

Type level machinery

------------------------------------------------------}

--
-- We will use type level Nats, via DataKinds extension
--
data Nat = Z | S Nat

type family Length (xs :: [Maybe Nat]) :: Nat where
  Length '[]      = Z
  Length (x : xs) = S (Length xs)

type family Or (x::Bool) (y::Bool) :: Bool where
  Or True  y = True
  Or False y = y
  Or x True  = True
  Or x False = x

type family And (x::Bool) (y::Bool) :: Bool where
  And False y = False
  And True  y = y
  And x False = False
  And x True  = x

--
-- Type level machinery for consuming a variable
-- in a list of variables.
--
class Consume (v::Nat)
              (i::[Maybe Nat])
              (o::[Maybe Nat])
      | v i -> o
class Consume1 (b::Bool)
               (v::Nat)
               (x::Nat)
               (i::[Maybe Nat])
               (o::[Maybe Nat])
      | b v x i -> o

instance (Consume v i o)
      => Consume v (Nothing ': i) (Nothing ': o)
instance (EQ v x b, Consume1 b v x i o)
      => Consume v (Just x ': i) o

instance Consume1 True v x i (Nothing ': i)
instance (Consume v i o)
      => Consume1 False v x i (Just x ': o)

-- GHC 8.0.1 cannot infer this type but GHC 7.10.3 can.
--
-- The bug is in GHC 7.10.3 which should not be able to infer this
-- type without enabling ImpredicativeTypes.
--
-- Lambda-bound variables cannot be polymorphic unless they are
-- specifically annotated as such - or ImpredicativeTypes is enabled.
llp :: (LLC repr, v ~ Length i) =>
     (LVar repr (S v) a -> LVar repr (S (S v)) b ->
        repr (Just (S v) : Just (S (S v)) : Nothing : i)
             (Nothing    : Nothing        : Nothing : o) c) ->
          repr i (o :: [Maybe Nat]) ((a * b) -<> c)
llp f = llam (\p -> letStar p f)
llz f = llam (\z -> letOne z f)

compose :: LLC repr =>
           repr i i ((b -<> c) -<> (a -<> b) -<> a -<> c)
compose = llam (\g -> llam (\f -> llam (\x -> g ^ (f ^ x))))
