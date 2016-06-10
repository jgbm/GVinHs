{-# LANGUAGE
  DataKinds,
  FlexibleContexts,
  NoMonomorphismRestriction,
  TypeFamilies,
  TypeOperators
 #-}

module PolGVexamples where

import Prelude hiding ((^), (<*>), (+))
import Language.LLC
import Language.PolGV

easiest =
    defnGV $ fork (llam $ \c -> send (bang (constant 6)) c) `bind` (llam $ \c ->
             recv c                                         `bind` (llp $  \x c ->
             wait c                                         `bind` (llz $
             ret x
    )))

easier =
    defnGV $ fork (llam $ \c -> ish c      `bind` (llam $ \c ->
                                recv c     `bind` (llp  $ \x c ->
                                osh c      `bind` (llam $ \c ->
                                send x c
                  ))))                     `bind` (llam $ \c ->
             osh c                         `bind` (llam $ \c ->
             send (bang (constant 6)) c    `bind` (llam $ \c ->
             ish c                         `bind` (llam $ \c ->
             recv c                        `bind` (llp  $ \z c ->
             wait c                        `bind` (llz  $
             ret z
    ))))))



times :: Defn 'False (Bang (Base Int) -<> (Bang (Base Int) -<> Bang (Base Int)))
times = llam $ \x -> llam $ \y -> letBang x $ \x' -> letBang y $ \y' -> bang (constant (*) $$$ x' $$$ y')

multiplier =
    defnGV $ llam $
    \c -> recv c                   `bind` (llp $ \x c ->
          recv c                   `bind` (llp $ \y c ->
          osh c                    `bind` (llam $ \c  ->
          send (times ^ x ^ y) c
    )))

calculator =
    defnGV $ llam $
    \c -> ish c                                   `bind` (llam $ \c ->
          offer c
            (llam $ \c -> multiplier ^ c)
            (llam $ \c -> recv c                  `bind` (llp $ \x c ->
                          osh c                   `bind` (llam $ \c ->
                          send (times ^ (bang (constant (-1))) ^ x) c
            ))))


answer2 =
    defnGV $ fork calculator                  `bind` (llam $ \c ->
             osh c                            `bind` (llam $ \c ->
             chooseRight c                    `bind` (llam $ \c ->
             send (bang (constant 4)) c       `bind` (llam $ \c ->
             ish c                            `bind` (llam $ \c ->
             recv c                           `bind` (llp  $ \x c ->
             wait c                           `bind` (llz  $
             ret x
    )))))))

answer3 =
    defnGV $ fork calculator                 `bind` (llam $ \c ->
             osh c                           `bind` (llam $ \c ->
             chooseLeft c                    `bind` (llam $ \c ->
             send (bang (constant 6)) c      `bind` (llam $ \c ->
             send (bang (constant 7)) c      `bind` (llam $ \c ->
             ish c                           `bind` (llam $ \c ->
             recv c                          `bind` (llp  $ \z c ->
             wait c                          `bind` (llz  $
             ret z
    ))))))))
