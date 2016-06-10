{-# LANGUAGE
  DataKinds,
  FlexibleContexts,
  NoMonomorphismRestriction,
  TypeOperators
 #-}

module GVexamples where

import Prelude hiding ((^), (<*>), (+))
import Language.LLC
import Language.GV

--------------------------------------------------------------------------------
-- Sending and receiving

easiest =
    defnGV $ fork (llam $ \c -> send (bang (constant 6)) c) `bind` (llam $ \c ->
             recv c                                         `bind` (llp $  \x c ->
             wait c                                         `bind` (llz $
             ret x
    )))

times :: Defn 'False (Bang (Base Int) -<> (Bang (Base Int) -<> Bang (Base Int)))
times = llam $ \x -> llam $ \y -> letBang x $ \x' -> letBang y $ \y' -> bang (constant (*) $$$ x' $$$ y')

multiplier =
    defnGV $ llam $
    \c -> recv c                   `bind` (llp $ \x c ->
          recv c                   `bind` (llp $ \y c ->
          send (times ^ x ^ y) c
    ))

easier =
    defnGV $ fork multiplier                  `bind` (llam $ \c ->
             send (bang (constant 6)) c       `bind` (llam $ \c ->
             send (bang (constant 7)) c       `bind` (llam $ \c ->
             recv c                           `bind` (llp $ \z c ->
             wait c                           `bind` (llz $
             ret z
    )))))

--------------------------------------------------------------------------------
-- Choice and consequences

easy =
    defnGV $ fork (llam $ \c -> offer c (llam $ \c -> ret c) (llam $ \c -> ret c))
                                              `bind` (llam $ \c ->
             chooseRight c                    `bind` (llam $ \c ->
             wait c                           `bind` (llz  $
             ret (constant ())
    )))

calculator =
    defnGV $ llam $
    \c -> offer c
            (llam $ \c -> multiplier ^ c)
            (llam $ \c -> recv c                  `bind` (llp $ \x c ->
                          send (times ^ (bang (constant (-1))) ^ x) c
            ))

answer2 =
    defnGV $ fork calculator                  `bind` (llam $ \c ->
             chooseRight c                    `bind` (llam $ \c ->
             send (bang (constant 4)) c       `bind` (llam $ \c ->
             recv c                           `bind` (llp  $ \x c ->
             wait c                           `bind` (llz  $
             ret x
    )))))

answer3 =
    defnGV $ fork calculator                 `bind` (llam $ \c ->
             chooseLeft c                    `bind` (llam $ \c ->
             send (bang (constant 6)) c      `bind` (llam $ \c ->
             send (bang (constant 7)) c      `bind` (llam $ \c ->
             recv c                          `bind` (llp  $ \z c ->
             wait c                          `bind` (llz  $
             ret z
    ))))))

--------------------------------------------------------------------------------
-- Delegation

sixSender =
    defnGV $ llam $
    \c -> recv c                          `bind` (llp  $ \d c ->
          send (bang (constant 6)) d      `bind` (llam $ \d ->
          send d c
    ))

answer =
    defnGV $ fork sixSender                 `bind` (llam $ \d ->
             fork multiplier                `bind` (llam $ \c ->
             send c d                       `bind` (llam $ \d ->
             recv d                         `bind` (llp  $ \c d ->
             send (bang (constant 7)) c     `bind` (llam $ \c ->
             recv c                         `bind` (llp  $ \x c ->
             wait c                         `bind` (llz  $
             wait d                         `bind` (llz  $
             ret x
    ))))))))
