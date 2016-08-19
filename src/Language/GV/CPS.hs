{-# LANGUAGE
  DataKinds,
  FlexibleContexts,
  FlexibleInstances,
  FunctionalDependencies,
  GADTs,
  KindSignatures,
  MultiParamTypeClasses,
  NoMonomorphismRestriction,
  RankNTypes,
  ScopedTypeVariables,
  TypeFamilies,
  TypeOperators,
  UndecidableInstances
 #-}

module Language.GV.CPS where

import Prelude hiding ((^), (<*>), (+))

import Language.LLC
import Language.LLC.Monadic
import Language.ST
import Language.GV

import GVexamples

import Control.Monad
import Control.Monad.Cont

-- CPS transformation for session types
newtype COutput t s r = COutput {unCOutput :: t (Cont r) -> s r -> r}
newtype CEndOut r     = CEndOut {unCEndOut :: r}

newtype CIn s r = CIn {unCIn :: s r -> r}

-- return type of a continuation monad
type family Ret (m :: * -> *) where
  Ret (Cont r) = r

-- Monadic/CPS translation of a session type
newtype CST (s :: *) (m :: * -> *) = CST {unCST :: CPS s (Ret m)}

type family CPS (s :: *) :: * -> *
type instance CPS s = CPS' (Pol s) s


type family CPS' (p :: Polarity) (s :: *) :: * -> *
type instance CPS' O (t <!> s)    = COutput (Mon t) (CPS (Dual s))
type instance CPS' O EndOut       = CEndOut
type instance CPS' O (s1 <++> s2) = CPS (ST (Dual s1) + ST (Dual s2) <!> EndOut)
type instance CPS' I s            = CIn (CPS (Dual s))

type instance Mon (ST s)        = CST s

-- communication (input consumes output through application)
comm :: (Dual (Dual s) ~ s, Pol (Dual s) ~ Flip (Pol s)) => SPolarity s -> (CPS (Dual s) r -> r) -> (CPS s r -> r) -> r
comm SO c d = c (CIn d)
comm SI c d = d (CIn c)

csid :: CST EndOut (Cont r) -> r
csid (CST (CEndOut x)) = x

wid :: CIn CEndOut r
wid = CIn (\(CEndOut x) -> x)

instance GV ST (RM (Cont r)) where
  send (RM m) (RM n) = RM (cont $ \(k :: CST s (Cont r) -> r) ->
                                      runCont m (\x -> runCont n (\(CST (COutput f)) ->
                                                    comm (polarity :: SPolarity s) (f x) (\x -> k (CST x)))))
  recv (RM m) = RM (cont $ \k -> runCont m (\(CST (CIn f)) -> f (COutput (\x y -> k (MProd (x, CST y))))))
  wait (RM m) = RM (cont $ \k -> runCont m (\(CST (CIn f)) -> f (CEndOut (k MOne))))
  fork (RM (m :: Cont r (Mon (ST s -<> ST EndOut) (Cont r)))) =
    RM (cont $ \(k :: CST (Dual s) (Cont r) -> r) -> runCont m (\(MFun f) ->
                                                  comm (polarity :: SPolarity s)
                                                  (k . CST)
                                                  (\x -> runCont (f (CST x)) csid)))
  chooseLeft (RM m) = RM (cont $ \(k :: CST s1 (Cont r) -> r) ->
                                     runCont m (\(CST (COutput f)) ->
                                                    comm (polarity :: SPolarity s1)
                                                    (\x -> f (MSum (Left (CST x))) wid)
                                                    (\y -> k (CST y))))
  chooseRight (RM m) = RM (cont $ \(k :: CST s2 (Cont r) -> r) ->
                                      runCont m (\(CST (COutput f)) ->
                                                     comm (polarity :: SPolarity s2)
                                                     (\x -> f (MSum (Right (CST x))) wid)
                                                     (\y -> k (CST y))))
  offer (RM m) (RM n1) (RM n2) =
    RM (cont $ \k -> runCont m (\(CST (CIn f)) ->
                                  f (COutput (\x y ->
                                       case x of
                                         MSum (Left  x1) -> runCont n1 (\(MFun f1) -> runCont (f1 x1) k)
                                         MSum (Right x2) -> runCont n2 (\(MFun f2) -> runCont (f2 x2) k)))))

evalCont :: RM (Cont r) tf '[] '[] a -> (Mon a (Cont r) -> r) -> r
evalCont (RM m) = runCont m

evalBase :: RM (Cont a) tf '[] '[] (Bang (Base a)) -> a
evalBase m = evalCont m (\(MBase x) -> x)
