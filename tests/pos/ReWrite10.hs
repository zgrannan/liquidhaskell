module ReWrite10 where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

import Prelude hiding (and)

data Nat = S Nat | Z

{-@ reflect and @-}
and :: Bool -> Bool -> Bool
and True  y = y
and False _ = False

{-@ reflect f @-}
f :: Bool -> Nat
f True  = S Z
f False = Z

{-@ assume myProof ::
    x : Bool -> y : Bool -> { f (and x y) = Z } @-}
myProof :: Bool -> Bool -> ()
myProof x y = ()

{-@ inline g @-}
g :: Bool -> Bool -> Bool
g x y = x && y

{-@ rewriteWith mp [myProof] @-}
{-@ mp ::
        x : Bool
     -> y : Bool
     -> { v : () | f (g x y) = Z }
@-}
mp :: Bool -> Bool -> ()          
mp x y = ()
