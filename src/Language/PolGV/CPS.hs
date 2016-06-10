{-# LANGUAGE
  DataKinds,
  FlexibleContexts,
  FlexibleInstances,
  FunctionalDependencies,
  GADTs,
  MultiParamTypeClasses,
  RankNTypes,
  ScopedTypeVariables,
  TypeFamilies,
  TypeOperators,
  UndecidableInstances
 #-}

module Language.PolGV.CPS where

import Prelude hiding ((^), (<*>), (+))

import Language.LLC
import Language.LLC.Monadic
import Language.ST
import Language.PolGV
import PolGVexamples

import Control.Monad
import Control.Monad.Cont

-- Proxies for session typed channels
data IST (s :: *)
data OST (s :: *)

-- CPS transformation for session types
newtype COutput t s r = COutput {unCOutput :: t (Cont r) -> s r -> r}
newtype CEndOut r     = CEndOut {unCEndOut :: r}

newtype CNegative s r = CNeg { unCNeg :: CPSO (Dual s) r -> r }

-- return type of a continuation monad
type family Ret (m :: * -> *) where
  Ret (Cont r) = r

-- Monadic/CPS translation of a session types
data OutC (s :: *) (m :: * -> *) where
  OutC :: Dual (Dual s) ~ s => CPSO s (Ret m) -> OutC s m
data InC  (s :: *) (m :: * -> *) where
  InC :: Dual (Dual s) ~ s => CPSI s (Ret m) -> InC s m

type family CPSO (s :: *) :: * -> *
type instance CPSO (t <!> s)    = COutput (Mon t) (CPSI (Dual s))
type instance CPSO (s1 <++> s2) = CPSO ((IST (Dual s1) + IST (Dual s2)) <!> EndOut)
type instance CPSO (OutShift s) = CPSO (OST (Dual s) <!> EndOut)
type instance CPSO EndOut       = CEndOut

type family CPSI (s :: *) :: * -> *
type instance CPSI s            = CNegative s

type instance Mon (IST s)       = InC s
type instance Mon (OST s)       = OutC s

-- communication (input consumes output through application)
comm :: (CNegative s r -> r) -> (CPSO (Dual s) r -> r) -> r
comm c d = c (CNeg d)

csid :: OutC EndOut (Cont r) -> r
csid (OutC (CEndOut x)) = x

instance GV OST IST (RM (Cont r)) where
  send (RM m) (RM n) = RM (cont $ \k -> runCont m (\x -> runCont n (\(OutC (COutput f)) -> comm (f x) (\x -> k (OutC x)))))

--  send (RM m) (RM n) = RM $
--    cont $ \k ->
--    do x <- m
--       OutC (COutput f) <- n
--       comm (f x) (k . OutC)

  recv (RM m) = RM (cont $ \k -> runCont m (\(InC (CNeg f)) -> f (COutput (\x y -> k (MProd (x, InC y))))))
  wait (RM m) = RM (cont $ \k -> runCont m (\(InC (CNeg f)) -> f (CEndOut (k MOne))))
  fork (RM m) = RM (cont $ \k -> runCont m (\(MFun f) -> comm (k . InC) (\x -> runCont (f (OutC x)) csid)))
  osh  (RM m) = RM (cont $ \k -> runCont m (\(InC (CNeg f)) -> f (COutput (\x (CNeg g) -> g (CEndOut (k x))))))
  ish  (RM m) = RM (cont $ \k -> runCont m (\(OutC (COutput f)) -> comm (k . InC)
                                                                        (\z -> comm (f (OutC z))
                                                                                    (\x -> csid (OutC x)))))

  chooseLeft (RM m) = RM (cont $ \(k :: OutC s1 (Cont r) -> r) ->
                          runCont m (\(OutC (COutput f)) ->
                                         (comm :: (CNegative (InShift s1) r -> r) -> (CPSO (OutShift (Dual s1)) r -> r) -> r)
                                              (\(CNeg y) -> y (COutput (\x (CNeg g) -> g (CEndOut (k x)))))
                                              (\(COutput g) ->
                                                   comm (\x' -> f (MSum (Left (InC x'))) (CNeg (\(CEndOut x) -> x)))
                                                        (\z -> comm (g (OutC z))
                                                                       (\x -> csid (OutC x))))))
  chooseRight (RM m) = RM (cont $ \(k :: OutC s2 (Cont r) -> r) ->
                           runCont m (\(OutC (COutput f)) ->
                                          (comm :: (CNegative (InShift s2) r -> r) -> (CPSO (OutShift (Dual s2)) r -> r) -> r)
                                               (\(CNeg y) -> y (COutput (\x (CNeg g) -> g (CEndOut (k x)))))
                                               (\(COutput g) ->
                                                    comm (\x' -> f (MSum (Right (InC x'))) (CNeg (\(CEndOut x) -> x)))
                                                         (\z -> comm (g (OutC z))
                                                                        (\x -> csid (OutC x))))))
  offer (RM m) (RM n1) (RM n2) =
    RM (cont $ \k -> runCont m (\(InC (CNeg f)) ->
                                  f (COutput (\x y ->
                                                  case x of
                                                    MSum (Left  x1) -> runCont n1 (\(MFun f1) -> runCont (f1 x1) k)
                                                    MSum (Right x2) -> runCont n2 (\(MFun f2) -> runCont (f2 x2) k)))))
