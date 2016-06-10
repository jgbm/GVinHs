{-# LANGUAGE
  DataKinds,
  FlexibleContexts,
  FlexibleInstances,
  RankNTypes,
  TypeFamilies,
  TypeOperators
 #-}

-- Based on Jeff Polakow, "Embedding a Full Linear Lambda Calculus in Haskell"

module Language.LLC.Plain where

import Language.LLC
import Prelude hiding((^), (<*>), (+))

--
-- Evaluator
--   i.e. a concrete representation which evaluates the LLC terms.
--
newtype R (vid::Nat) (tf::Bool) (hi::[Maybe Nat]) (ho::[Maybe Nat]) a = R {unR :: a}

instance LLC (R :: Nat -> Bool -> [Maybe Nat] -> [Maybe Nat] -> * -> *) where
    llam f = R $ Lolli $ \x -> unR (f (R x))
    f ^ x = R $ unLolli (unR f) (unR x)

    bang = R . Bang . unR
    letBang x f = R $ unR $ f' (unR x)
      where f' (Bang x) = f (R x)

    ulam f = R $ Arrow $ \x -> unR (f (R x))
    f $$ x = R $ unArrow (unR f) (unR x)

    x <*> y = R $ Tensor (unR x) (unR y)
    letStar xy f = R $ unR $ f' (unR xy)
      where f' (Tensor x y) = f (R x) (R y)

    one = R One
    letOne x y = R $ unR $ (\One -> y) $ unR x

    top = R ()

    x & y = R $ (unR x, unR y)
    pi1 = R . fst . unR
    pi2 = R . snd . unR

    inl = R . Inl . unR
    inr = R . Inr . unR
    letPlus xy fInl fInr = case unR xy of
                             Inl x -> R $ unR $ fInl (R x)
                             Inr y -> R $ unR $ fInr (R y)

    abort x = R $ error "abort"

    constant x = R (Base x)
    R (Base f) $$$ R (Base x) = R (Base (f x))

eval :: R Z tf '[] '[] a -> a
eval = unR


--
-- Recursive types
--
newtype Mu a = Mu {unMu :: a (Mu a)}

class LLCRec (repr :: Nat -> Bool -> [Maybe Nat] -> [Maybe Nat] -> * -> *) where
    wrap :: (b -> a (Mu a)) -> repr vid tf i o b -> repr vid tf i o (Mu a)
    unwrap :: (a (Mu a) -> b) -> repr vid tf i o (Mu a) -> repr vid tf i o b
    fix :: ((forall vid h . repr vid False h h a) -> repr vid tf h h a) -> repr vid tf h h a

instance LLCRec (R :: Nat -> Bool -> [Maybe Nat] -> [Maybe Nat] -> * -> *) where
    wrap f = R . Mu . f . unR
    unwrap f = R . f . unMu . unR
    fix f = f (R $ unR $ fix f)

type DefnRec tf a =
    forall repr i vid
    . (LLCRec repr, LLC repr, MrgLs i)
    => repr vid tf i i a
defnRec :: DefnRec tf a -> DefnRec tf a
defnRec x = x


--
-- Linear Lists
--
newtype MyListF a lst = MLF {unMLF :: One + (a * lst)}
type MyList a = Mu (MyListF a)

instance Show a => Show (MyList a) where
    show (Mu (MLF (Inl _))) = "nil"
    show (Mu (MLF (Inr (Tensor x xs)))) = show x ++ ":" ++ show xs

nil :: DefnRec False (MyList a)
nil = wrap MLF (inl one)

cons :: DefnRec False (a -<> (MyList a -<> MyList a))
cons = llam $ \x -> llam $ \xs -> wrap MLF (inr (x <*> xs))

x <:> xs = cons ^ x ^ xs
infixr 5 <:>

listC :: DefnRec False (MyList a -<> (b & (a -<> MyList a -<> b)) -<> b)
listC = llam $ \l -> llam $ \k ->
        letPlus (unwrap unMLF l)
                (\x -> letOne x (pi1 k))
                (\xs -> letStar xs (\x xs -> pi2 k ^ x ^ xs))

rev :: DefnRec False (MyList a -<> MyList a -<> MyList a)
rev = fix $ \r -> llam $ \l -> llam $ \k ->
      letPlus (unwrap unMLF l)
              (\x -> letOne x k)
              (\xs -> letStar xs (\x xs -> r ^ xs ^ (x <:> k)))

rev' :: DefnRec False (MyList a -<> MyList a -<> MyList a)
rev' = llam $ \l -> llam $ \k ->
       listC ^ l ^ ( k
                   & (llam $ \x -> llam $ \xs -> rev' ^ xs ^ (x <:> k))
                   )

newtype MyList1F a lst = ML1F {unML1F :: One + (a & lst)}
type MyList1 a = Mu (MyList1F a)

cons1 :: DefnRec False ((a & MyList1 a) -<> MyList1 a)
cons1 = llam $ \x -> wrap ML1F (inr (pi1 x & pi2 x))
