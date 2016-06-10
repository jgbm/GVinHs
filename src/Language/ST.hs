{-# LANGUAGE
  DataKinds,
  GADTs,
  TypeFamilies,
  TypeOperators
 #-}

module Language.ST where

-- session types
data t <!> s
data s1 <++> s2
data EndOut
data t <?> s
data s1 <&&> s2
data EndIn

-- polarity
data Polarity = O | I

type family Pol s :: Polarity
type instance Pol (t <!> s) = O
type instance Pol EndOut = O
type instance Pol (t <?> s) = I
type instance Pol EndIn = I
type instance Pol (s1 <++> s2) = O
type instance Pol (s1 <&&> s2) = I

-- polarity singleton
data SPolarity s where
  SO :: Pol s ~ O => SPolarity s
  SI :: Pol s ~ I => SPolarity s

type family Flip (p :: Polarity) :: Polarity where
  Flip O = I
  Flip I = O

-- duality
type family Dual s :: *
type instance Dual (t <!> s)    = t <?> Dual s
type instance Dual EndOut       = EndIn
type instance Dual (t <?> s)    = t <!> Dual s
type instance Dual EndIn        = EndOut
type instance Dual (s1 <++> s2) = Dual s1 <&&> Dual s2
type instance Dual (s1 <&&> s2) = Dual s1 <++> Dual s2
