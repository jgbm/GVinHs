{-# LANGUAGE
  DataKinds,
  FlexibleContexts,
  NoMonomorphismRestriction,
  TypeOperators
 #-}

module GVXexamples where

import Prelude hiding ((^), (<*>), (+))
import Language.GV
import Language.GVX
import Language.LLC

--------------------------------------------------------------------------------
-- Access points

wut = defnGVX $ new (ulam $ \ap -> accept ap `bind` llam (\c -> accept ap `bind` (llam (\d -> ret (c <*> d)))))

answer4 =
    defnGVX $ new                                      (ulam $ \ap ->
              spawn (llz $ accept ap                   `bind` (llam $ \c ->
                           send (bang (constant 42)) c `bind` (llam $ \c ->
                           close c
                    )))                                `bind` (llz $
              request ap                               `bind` (llam $ \c ->
              recv c                                   `bind` (llp $ \z c ->
              wait c                                   `bind` (llz $
              ret z
    )))))
