{-# LANGUAGE
  DataKinds,
  PolyKinds,
  TypeFamilies,
  TypeOperators
 #-}

module Language.LLC.Monadic where

import Language.LLC

newtype MFun (a :: (* -> *) -> *) (b :: (* -> *) -> *) (m :: * -> *)  = MFun  {unMFun  :: a m -> m (b m)}
data    MOne m      = MOne
data    MZero m     = MZero
newtype MProd a b m = MProd {unMProd :: (a m, b m)}
newtype MSum a b m  = MSum  {unMSum  :: Either (a m) (b m)}
newtype MBase a m   = MBase {unMFBase :: a}

type family Mon (t :: *) :: (* -> *) -> *
type instance Mon (a -<> b) = MFun (Mon a) (Mon b)
type instance Mon (a ->> b) = MFun (Mon a) (Mon b)
type instance Mon (Bang a)  = Mon a
type instance Mon Top       = MOne
type instance Mon (a & b)   = MProd (Mon a) (Mon b)
type instance Mon One       = MOne
type instance Mon (a * b)   = MProd (Mon a) (Mon b)
type instance Mon (a + b)   = MSum (Mon a) (Mon b)
type instance Mon Zero      = MZero
type instance Mon (Base a)  = MBase a

--
-- A monadic evaluator
--
newtype RM (m :: * -> *) (vid::Nat) (tf::Bool) (hi::[Maybe Nat]) (ho::[Maybe Nat]) a = RM {unRM :: m (Mon a m)}

instance Monad m => LLC (RM m) where
    llam f = RM (return (MFun (\x -> unRM (f (RM (return x))))))
    f ^ x = RM $ do f' <- unRM f
                    x' <- unRM x
                    unMFun f' x'

    bang x = RM (unRM x)
    letBang x f = RM (do x' <- unRM x
                         unRM (f (RM (return x'))))

    ulam f = RM (return (MFun (\x -> unRM (f (RM (return x))))))
    f $$ x = RM $ do f' <- unRM f
                     x' <- unRM x
                     unMFun f' x'

    x <*> y = RM $ do x' <- unRM x
                      y' <- unRM y
                      return (MProd (x', y'))
    letStar xy f = RM (unRM xy >>= unRM .  f')
        where f' (MProd (x, y)) = f (RM (return x)) (RM (return y))

    one = RM (return MOne)
    letOne x y = RM (unRM x >>= const (unRM y))

    top = RM (return MOne)

    x & y = RM $ do x' <- unRM x
                    y' <- unRM y
                    return (MProd (x', y'))
    pi1 x = RM (unRM x >>= return . fst)
        where fst (MProd (x, y)) = x
    pi2 x = RM (unRM x >>= return . snd)
        where snd (MProd (x, y)) = y

    inl x = RM (unRM x >>= return . MSum . Left)
    inr x = RM (unRM x >>= return . MSum . Right)
    letPlus xy fInl fInr =
        RM $ do (MSum xy') <- unRM xy
                case xy' of
                  Left x  -> unRM (fInl (RM (return x)))
                  Right y -> unRM (fInr (RM (return y)))

    abort x = RM $ error "abort"

    constant x = RM (return (MBase x))
    RM m $$$ RM n = RM (do MBase f <- m
                           MBase x <- n
                           return (MBase (f x)))

eval :: RM m Z tf '[] '[] a -> m (Mon a m)
eval = unRM
