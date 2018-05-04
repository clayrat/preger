module Util

import Data.Sign
import Data.Fin

%access public export
%default total

Not0 : Integer -> Type
Not0 k = Not (k = 0)

Signed Integer where
  sign x with (compare x 0)
    | LT = Minus
    | EQ = Zero
    | GT = Plus

notzs : Not0 x -> Not (sign x = Zero)
notzs nzx = really_believe_me nzx

opposite : Sign -> Sign
opposite Plus  = Minus
opposite Zero  = Zero
opposite Minus = Plus

multiply : Sign -> Sign -> Sign
multiply Zero  _    = Zero
multiply _     Zero = Zero
multiply Plus  x    = x
multiply Minus x    = opposite x

fromSign : Sign -> Integer
fromSign Plus = 1    
fromSign Zero = 0
fromSign Minus = -1

Uninhabited (Minus = Zero) where
  uninhabited Refl impossible

Uninhabited (Plus = Zero) where
  uninhabited Refl impossible

mulsnz : (x, y : Sign) -> Not (x=Zero) -> Not (y=Zero) -> Not (multiply x y = Zero)
mulsnz Zero  _     xnz _   = absurd $ xnz Refl
mulsnz _     Zero  _   ynz = absurd $ ynz Refl
mulsnz Plus  Plus  _   _   = uninhabited
mulsnz Plus  Minus _   _   = uninhabited
mulsnz Minus Plus  _   _   = uninhabited
mulsnz Minus Minus _   _   = uninhabited

eitherFromSign : (s : Sign) -> Not (s = Zero) -> Either (fromSign s = 1) (fromSign s = -1)
eitherFromSign Plus  _  = Left Refl
eitherFromSign Zero  nz = absurd $ nz Refl
eitherFromSign Minus _  = Right Refl

NotNull : Type
NotNull = (k ** Not0 k)

not01 : Not0 1
not01 z1 = really_believe_me ()

not0m1 : Not0 (-1)
not0m1 zm1 = really_believe_me ()

oneNN : NotNull
oneNN = (1 ** not01)

mulnz : Not0 a -> Not0 b -> Not0 (a*b)
mulnz anz bnz = really_believe_me ()

mulnz2 : Not0 (a*b) -> (Not0 a, Not0 b)
mulnz2 abnz = (really_believe_me (), really_believe_me ())

m0p0 : (k : Integer) -> 0-k = 0 -> k = 0
m0p0 k prf = really_believe_me prf

m1 : (k : Integer) -> 1*k = k
m1 k = really_believe_me ()

massoc : (x,y,z : Integer) -> x*(y*z) = (x*y)*z
massoc x y z = really_believe_me ()

data Divides : (d : Integer) -> (x : Integer) -> Type where
  DivBy : x = q*d -> Divides d x

divRefl : Divides k k
divRefl {k} = DivBy {q=1} (sym $ m1 k)
  
divTrans : Divides x y -> Divides y z -> Divides x z
divTrans {x} (DivBy {q=q1} xy) (DivBy {q=q2} yz) = 
  DivBy {q=q2*q1} $ rewrite sym $ massoc q2 q1 x in rewrite sym xy in yz

data LCM : (i : Integer) -> (j : Integer) -> (d : Integer) -> Type where
  MkLCM : Divides i d
       -> Divides j d
       -> ((m : Integer) -> Divides i m -> Divides j m -> Divides d m)
       -> LCM i j d

-- TODO add to prelude?       

partial
quot : Integer -> Integer -> Integer       
quot = div -- TODO

partial
rem : Integer -> Integer -> Integer       
rem = mod -- TODO

partial
gcdI : Integer -> Integer -> Integer
gcdI x y = gcd' (abs x) (abs y)
  where 
  gcd' a 0 = a
  gcd' a b = gcd' b (a `rem` b)

partial
lcmI : Integer -> Integer -> Integer
lcmI _ 0 = 0
lcmI 0 _ = 0
lcmI x y = abs ((x `quot` (gcdI x y)) * y)       

---
lcm : (i, j : Integer) -> (d ** LCM i j d)
lcm i j = let d = assert_total $ lcmI i j in 
          (d ** MkLCM (DivBy {q=d `div` i} $ really_believe_me ()) 
                      (DivBy {q=d `div` j} $ really_believe_me ()) 
                      (\m, idm, jdm => DivBy {q=d `div` m} $ really_believe_me ()))

lcmNeq : (m, n : NotNull) -> LCM (fst m) (fst n) d -> Not0 d
lcmNeq m n lmnd = really_believe_me ()

data FOrd : (i, j : Fin n) -> Type where
  Less : Nat.LTE (finToNat (FS i)) (finToNat j) -> FOrd i j
  Equal : i = j -> FOrd i j
  Greater : Nat.LTE (finToNat (FS j)) (finToNat i) -> FOrd i j

fCompare : (i, j : Fin n) -> FOrd i j
fCompare {n=S _}  FZ     FZ    = Equal Refl
fCompare {n=S _}  FZ    (FS x) = Less $ LTESucc LTEZero
fCompare {n=S _} (FS x)  FZ    = Greater $ LTESucc LTEZero
fCompare {n=S _} (FS x) (FS y) with (fCompare x y)
  | Less l = Less $ LTESucc l
  | Equal e = Equal $ cong e
  | Greater g = Greater $ LTESucc g