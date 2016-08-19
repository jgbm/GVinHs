{-# LANGUAGE
  ConstraintKinds,
  DataKinds,
  FlexibleContexts,
  FlexibleInstances,
  FunctionalDependencies,
  MultiParamTypeClasses,
  NoMonomorphismRestriction,
  PolyKinds,
  RankNTypes,
  TypeFamilies,
  TypeOperators,
  UndecidableInstances
 #-}

-- Based on Jeff Polakow, "Embedding a Full Linear Lambda Calculus in Haskell"

module Language.LLC where

import Prelude hiding((^), (<*>), (+))

--
-- Linear types
--
newtype a -<> b = Lolli {unLolli :: a -> b}
infixr 5 -<>
newtype a ->> b = Arrow {unArrow :: a -> b}
infixr 5 ->>
newtype Bang a = Bang {unBang :: a}
type Top = ()
type a & b = (a, b)
data One = One
  deriving Show
data a * b = Tensor a b
  deriving Show
data a + b = Inl a | Inr b
  deriving Show
data Zero
newtype Base a = Base {unBase :: a}
--
-- linear variable v in Haskell context
--
type LVar repr (x::Nat) a =
    forall (v::Nat)
           (i::[Maybe Nat])
           (o::[Maybe Nat])
    . (Consume x i o, v ~ Length i, v ~ Length o) => repr False i o a

--
-- unrestricted variable in Haskell context
--
type UVar repr a =
    forall (i::[Maybe Nat])
    . repr False i i a

--
-- The syntax of LLC.
--
class LLC (repr :: Bool
                -> [Maybe Nat]
                -> [Maybe Nat]
                -> *
                -> *
               ) where
  llam
    :: (VarOk tf var, v ~ Length i, v ~ Length o)
    => (LVar repr v a -> repr tf
                              (Just v ': i)
                              (var ': o)
                              b
       )
    -> repr tf i o (a -<> b)
  (^)
    :: repr tf1 i h (a -<> b)
    -> repr tf2 h o a
    -> repr (Or tf1 tf2) i o b

  bang
    :: repr tf i i a
    -> repr False i i (Bang a)
  letBang
    :: repr tf0 i h (Bang a)
    -> (UVar repr a -> repr tf1 h o b)
    -> repr (Or tf0 tf1) i o b

  ulam
    :: (UVar repr a -> repr tf i o b)
    -> repr tf i o (a ->> b)
  ($$)
    :: repr tf0 i o (a ->> b)
    -> repr tf1 o o a
    -> repr tf0 i o b

  top
    :: repr True i i Top

  (&)
    :: ( MrgL h0 tf0 h1 tf1 o
       , And tf0 tf1 ~ tf
       )
    => repr tf0 i h0 a
    -> repr tf1 i h1 b
    -> repr tf i o (a & b)
  pi1
    :: repr tf i o (a & b)
    -> repr tf i o a
  pi2
    :: repr tf i o (a & b)
    -> repr tf i o b

  one
    :: repr False i i One
  letOne
    :: repr tf0 i h One
    -> repr tf1 h o a
    -> repr (Or tf0 tf1) i o a

  (<*>)
    :: repr tf0 i h a
    -> repr tf1 h o b
    -> repr (Or tf0 tf1) i o (a * b)
  letStar
    :: ( VarOk tf1 var0
       , VarOk tf1 var1
       , v ~ Length i
-- breaks POLGV.hs as it doesn't know that Length i ~ Length o         
--       , v ~ Length o
       )
    => repr tf0 i h (a * b)
    -> (LVar repr v a
        -> LVar repr (S v) b
        -> repr tf1
                (Just v ': Just (S v) ': h)
                (var0 ': var1 ': o)
                c
       )
    -> repr (Or tf0 tf1) i o c

  inl
    :: repr tf i o a
    -> repr tf i o (a + b)
  inr
    :: repr tf i o b
    -> repr tf i o (a + b)
  letPlus
    :: ( MrgL o1 tf1 o2 tf2 o
       , VarOk tf1 var1
       , VarOk tf2 var2
       , v ~ Length i
       , v ~ Length o
       )
    => repr tf0 i h (a + b)
    -> (LVar repr v a -> repr tf1
                                (Just v ': h)
                                (var1 ': o1)
                                c
       )
    -> (LVar repr v b -> repr tf2
                                (Just v ': h)
                                (var2 ': o2)
                                c
       )
    -> repr (Or tf0 (And tf1 tf2)) i o c

  abort
    :: repr tf i o Zero
    -> repr True i o a

  constant :: a -> repr False i i (Base a)

  ($$$) :: repr tf i h (Base (a -> b))
        -> repr tf h o (Base a)
        -> repr tf i o (Base b)

--
-- A definition for a closed LLC term.
--
type MrgLs i = ( MrgL i False i False i
               , MrgL i False i True i
               , MrgL i True i False i
               , MrgL i True i True i
               )

--type MrgLs' i v v' = ( MrgL i v i v' i )

type Defn tf a =
    forall repr i v v'
    . (LLC repr, MrgLs i)
    => repr tf i i a
defn :: Defn tf a -> Defn tf a
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
--instance (Consume1 (EQF v x) v x i o)
      => Consume v (Just x ': i) o

instance Consume1 True v x i (Nothing ': i)
instance (Consume v i o)
      => Consume1 False v x i (Just x ': o)

class EQ (x::k) (y::k) (b::Bool) | x y -> b
instance {-# OVERLAPPING #-} EQ x x True
instance {-# OVERLAPPING #-} (b ~ False) => EQ x y b

type family EQF (x::k) (y::k) :: Bool where
  EQF x x = True
  EQF x y = False

--
-- Type level machinery for merging outputs of
-- additive operations and getting right Top flag.
--
class MrgL (h1::[Maybe Nat])
           (tf1::Bool)
           (h2::[Maybe Nat])
           (tf2::Bool)
           (h::[Maybe Nat])
  | h1 h2 -> h
instance MrgL '[] v1 '[] v2 '[]
instance (MrgL h1 v1 h2 v2 h)
      => MrgL (x ': h1) v1 (x ': h2) v2 (x ': h)
instance (MrgL h1 True h2 v2 h)
      => MrgL (Just x ': h1) True (Nothing ': h2) v2 (Nothing ': h)
instance (MrgL h1 v1 h2 True h)
      => MrgL (Nothing ': h1) v1 (Just x ': h2) True (Nothing ': h)

--
-- Check, in -<> type rule, that Top flag
-- was set or hypothesis was consumed.
--
class VarOk (tf :: Bool) (v :: Maybe Nat)
instance VarOk True (Just v)
instance VarOk True Nothing
instance VarOk False Nothing

-- GHC 8.0.1 doesn't seem to be able to infer this type (GHC 7.10.3 can)
llp :: (VarOk tf var, VarOk tf var0, VarOk tf var1, LLC repr, v ~ Length i, v ~ Length o) =>
     (LVar repr (S v) a -> LVar repr (S (S v)) b ->
        repr tf ('Just (S v) ': 'Just (S (S v)) ': 'Nothing ': i) (var0 ': var1 ': var ': o) c) ->
          repr tf i (o :: [Maybe Nat]) ((a * b) -<> c)
llp f = llam (\p -> letStar p f)
llz f = llam (\z -> letOne z f)

compose :: (LLC repr) =>
           repr False i i ((b -<> c) -<> (a -<> b) -<> a -<> c)
compose = llam (\g -> llam (\f -> llam (\x -> g ^ (f ^ x))))
