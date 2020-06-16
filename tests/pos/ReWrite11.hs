{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--smttimeout=10" @-}

module Rewrite11 where

infixl 3 ***
{-@ assume (***) :: a -> p:QED -> { if (isAdmit p) then false else true } @-}
(***) :: a -> QED -> ()
_ *** _ = ()

data QED = Admit | QED

{-@ measure isAdmit :: QED -> Bool @-}
{-@ Admit :: {v:QED | isAdmit v } @-}

{-@ (?) :: forall a b <pa :: a -> Bool, pb :: b -> Bool>. a<pa> -> b<pb> -> a<pa> @-}
(?) :: a -> b -> a 
x ? _ = x 
{-# INLINE (?)   #-}

infixl 3 ===
{-@ (===) :: x:a -> y:{a | y == x} -> {v:a | v == x && v == y} @-}
(===) :: a -> a -> a
_ === y  = y

data Bin = One | ZeroAnd Bin | OneAnd Bin

{-@ reflect toNat @-}
toNat :: Bin -> Int
toNat One = 1
toNat (ZeroAnd xs) = toNat xs + toNat xs
toNat (OneAnd xs) = 1 + toNat xs + toNat xs

{-@ reflect s @-}
s :: Bin -> Bin
s One = ZeroAnd One
s (ZeroAnd xs) = OneAnd xs
s (OneAnd xs) = ZeroAnd (s xs)

{-@ reflect plus @-}
plus :: Bin -> Bin -> Bin
plus One xs = s xs
plus xs@ZeroAnd{} One = s xs
plus xs@OneAnd{} One = s xs
plus (ZeroAnd xs) (ZeroAnd ys) = ZeroAnd (plus xs ys)
plus (ZeroAnd xs) (OneAnd ys) = OneAnd (plus xs ys)
plus (OneAnd xs) (ZeroAnd ys) = OneAnd (plus xs ys)
plus (OneAnd xs) (OneAnd ys) = ZeroAnd (s (plus xs ys))

{-@ prop_s :: n : Bin -> { toNat (s n) = 1 + toNat n } @-}
prop_s :: Bin -> ()
prop_s One          = ()
prop_s (OneAnd ys)  = prop_s ys
prop_s (ZeroAnd xs) = prop_s xs

{-@ rewriteWith prop_plus [prop_s] @-}
{-@ prop_plus :: x : Bin -> y : Bin -> { toNat (plus x y) = toNat x + toNat y }@-}
prop_plus :: Bin -> Bin -> ()
prop_plus One abcde = ()
prop_plus xs@ZeroAnd{} One = ()
prop_plus xs@OneAnd{} One = ()
prop_plus (ZeroAnd xs) (ZeroAnd ys) = prop_plus xs ys
prop_plus (ZeroAnd xs) (OneAnd ys) = prop_plus xs ys
prop_plus (OneAnd xs) (ZeroAnd ys) = prop_plus xs ys
prop_plus (OneAnd xs) (OneAnd ys) = prop_plus xs ys
