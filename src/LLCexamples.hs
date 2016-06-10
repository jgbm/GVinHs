{-# LANGUAGE
  FlexibleContexts,
  NoMonomorphismRestriction
 #-}

-- Based on Jeff Polakow, "Embedding a Full Linear Lambda Calculus in Haskell"

module LLCexamples where

import Prelude hiding( (^), (<*>), (+))
import Language.LLC

ex0 = defn $ llam $ \x -> x
-- bad1 = defn $ llam $ \x -> bang x
ex01 = defn $ ulam $ \x -> bang x
ex1 = defn $ llam $ \f -> llam $ \x -> f ^ x
-- bad2 = defn $ llam $ \f -> llam $ \x -> f ^ x ^ x
ex2 = defn $ llam $ \f -> ulam $ \x -> f ^ x ^ x
-- bad3 = defn $ llam $ \f -> llam $ \x -> llam $ \y -> f ^ x
ex4 = defn $ top & top
ex5 = defn $ (llam $ \x -> x) & top
ex6 = defn $ llam $ \f -> llam $ \y -> llam $ \x -> (f ^ x ^ y) & (f ^ y ^ x)
--bad7 = defn $ llam $ \f -> llam $ \x -> llam $ \y -> (f ^ x ^ y) & (f ^ x)
ex7 = defn $ llam $ \f -> llam $ \x -> ulam $ \y -> (f ^ x ^ y) & (f ^ x)
ex8 = defn $ llam $ \f -> llam $ \x -> llam $ \y -> (f ^ x ^ y) & (f ^ top)
ex9 = defn $ llam $ \x -> llam $ \y -> llam $ \z -> x <*> (z & z) <*> top
ex10 = defn $ llam $ \f -> llam $ \xy -> letStar xy (\x y -> f ^ x ^ y)
