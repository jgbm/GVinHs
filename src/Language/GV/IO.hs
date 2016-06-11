{-# LANGUAGE
  ConstraintKinds,
  DataKinds,
  FlexibleContexts,
  FlexibleInstances,
  FunctionalDependencies,
  GeneralizedNewtypeDeriving,
  KindSignatures,
  MultiParamTypeClasses,
  NoMonomorphismRestriction,
  PolyKinds,
  RankNTypes,
  TypeFamilies,
  TypeOperators,
  UndecidableInstances
 #-}

module Language.GV.IO where

import GVexamples
import GVXexamples
import Language.ST
import Language.GV
import Language.GVX
import Language.LLC
import Language.LLC.Monadic

import Control.Concurrent (forkIO)
import Control.Concurrent.Chan.Synchronous
import Control.Concurrent.MVar
import Data.Dynamic
import System.IO
import System.Random
import Unsafe.Coerce

import Prelude hiding ((^), (<*>), (+))

newtype IOChan s m = IOChan (Chan Int)

data STC s

type instance Mon (STC s) = IOChan s

instance GV STC (RM IO)
    where send (RM mv) (RM mc) =
              RM (do v <- mv
                     IOChan c <- mc
                     writeChan c (unsafeCoerce v)
                     return (IOChan c))
          recv (RM mc) =
              RM (do IOChan c <- mc
                     v <- readChan c
                     return (MProd (unsafeCoerce v, IOChan c)))
          chooseLeft (RM mc) =
              RM (do IOChan c <- mc
                     writeChan c (unsafeCoerce False)
                     return (IOChan c))
          chooseRight (RM mc) =
              RM (do IOChan c <- mc
                     writeChan c (unsafeCoerce True)
                     return (IOChan c))
          offer (RM mc) (RM mleft) (RM mright) =
              RM (do IOChan c <- mc
                     MFun left <- mleft
                     MFun right <- mright
                     v <- readChan c
                     if unsafeCoerce v
                     then right (IOChan c)
                     else left (IOChan c))
          wait (RM mc) =
              RM (do IOChan c <- mc
                     v <- readChan c
                     case unsafeCoerce v of
                       () -> return MOne)
          fork (RM mf) =
              RM (do MFun f <- mf
                     c <- newChan
                     forkIO (do (IOChan c) <- f (IOChan c)
                                writeChan c (unsafeCoerce ()))
                     return (IOChan c))

data APState s = Empty | Accepting [MVar (IOChan s IO)] | Requesting [MVar (IOChan (Dual s) IO)]
newtype IOAP s m = IOAP (MVar (APState s))

type instance Mon (AP s) = IOAP s

instance GVX AP STC (RM IO)
    where amb l r =
              RM (do b <- getStdRandom (randomR (False,True))
                     if b then unRM l else unRM r)
          spawn (RM mf) =
              RM (do MFun f <- mf
                     forkIO (f MOne >> return ())
                     return MOne)
          close (RM mc) =
              RM (do IOChan c <- mc
                     writeChan c (unsafeCoerce ())
                     return MOne)
          new (RM mf) =
              RM (do MFun f <- mf
                     m <- newMVar Empty
                     f (IOAP m))
          accept (RM apm) =
              RM (do IOAP mv <- apm
                     apState <- takeMVar mv
                     case apState of
                       Empty ->
                           do cv <- newEmptyMVar
                              putMVar mv (Accepting [cv])
                              takeMVar cv
                       Accepting cvs ->
                           do cv <- newEmptyMVar
                              putMVar mv (Accepting (cv:cvs))
                              takeMVar cv
                       Requesting (cv:cvs) ->
                           do c <- newChan
                              putMVar mv (if null cvs then Empty else Requesting cvs)
                              putMVar cv (IOChan c)
                              return (IOChan c))
          request (RM apm) =
              RM (do IOAP mv <- apm
                     apState <- takeMVar mv
                     case apState of
                       Empty ->
                           do cv <- newEmptyMVar
                              putMVar mv (Requesting [cv])
                              takeMVar cv
                       Requesting cvs ->
                           do cv <- newEmptyMVar
                              putMVar mv (Requesting (cv:cvs))
                              takeMVar cv
                       Accepting (cv:cvs) ->
                           do c <- newChan
                              putMVar mv (if null cvs then Empty else Accepting cvs)
                              putMVar cv (IOChan c)
                              return (IOChan c))
