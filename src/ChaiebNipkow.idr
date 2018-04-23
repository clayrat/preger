module ChaiebNipkow

import Data.So
import Data.Fin
import Data.Vect
import Data.Sign

%default total

-- TODO use ZZ or Biz instead of Integer to avoid totality/proof issues

-- expression with n variables

data Exp : (n : Nat) -> Type where
  Val    : (k : Integer) -> Exp n
  Var    : (p : Fin n) -> Exp n
  Negate : (e : Exp n) -> Exp n
  Plus   : (e1, e2 : Exp n) -> Exp n
  Minus  : (e1, e2 : Exp n) -> Exp n
  Times  : (k : Integer) -> (e : Exp n) -> Exp n

-- formulas with n variables

data Form : (n : Nat) -> Type where
  Top    : Form n
  Bot    : Form n
  Dvd    : (k : Integer) -> (e : Exp n) -> Form n
  Lt     : (e1, e2 : Exp n) -> Form n
  Gt     : (e1, e2 : Exp n) -> Form n
  Lte    : (e1, e2 : Exp n) -> Form n
  Gte    : (e1, e2 : Exp n) -> Form n
  Equ    : (e1, e2 : Exp n) -> Form n
  Notf   : (f : Form n) -> Form n
  Exists : (f : Form (S n)) -> Form n
  Forall : (f : Form (S n)) -> Form n
  Conj   : (f1, f2 : Form n) -> Form n
  Disj   : (f1, f2 : Form n) -> Form n
  Impl   : (f1, f2 : Form n) -> Form n
-- Eqf  : (f1, f2 : Form n) -> Form n

-- Integer semantics

iExp : (e : Exp n) -> (rho : Vect n Integer) -> Integer
iExp (Val k)       _   = k
iExp (Var p)       rho = index p rho
iExp (Negate e)    rho = -(iExp e rho)
iExp (Plus e1 e2)  rho = iExp e1 rho + iExp e2 rho
iExp (Minus e1 e2) rho = iExp e1 rho - iExp e2 rho
iExp (Times k e)   rho = k * iExp e rho

iForm : (f : Form n) -> (rho : Vect n Integer) -> Type
iForm Top          _   = Unit
iForm Bot          _   = Void
iForm (Dvd k e)    rho = (q ** k = q * iExp e rho)
iForm (Lt e1 e2)   rho = So (iExp e1 rho < iExp e2 rho)
iForm (Gt e1 e2)   rho = So (iExp e1 rho > iExp e2 rho)
iForm (Lte e1 e2)  rho = So (iExp e1 rho <= iExp e2 rho)
iForm (Gte e1 e2)  rho = So (iExp e1 rho >= iExp e2 rho)
iForm (Equ e1 e2)  rho = iExp e1 rho = iExp e2 rho
iForm (Notf f)     rho = Not (iForm f rho)
iForm (Exists f)   rho = (k ** iForm f (k :: rho))
iForm (Forall f)   rho = (k : Integer) -> iForm f (k :: rho)
iForm (Conj f1 f2) rho = (iForm f1 rho, iForm f2 rho)
iForm (Disj f1 f2) rho = Either (iForm f1 rho) (iForm f2 rho)
iForm (Impl f1 f2) rho = iForm f1 rho -> iForm f2 rho

-- TODO naive
qelimF : (qe : {k : Nat} -> Form (S k) -> Form k) -> Form n -> Form n
qelimF qe (Forall p) = Notf (qe (Notf (qelimF qe p)))
qelimF qe (Exists p) = qe (qelimF qe p)
qelimF qe (Conj p q) = Conj (qelimF qe p) (qelimF qe q)
qelimF qe (Disj p q) = Disj (qelimF qe p) (qelimF qe q)
qelimF qe (Impl p q) = Impl (qelimF qe p) (qelimF qe q)
qelimF _  p          = p

-- Helpers

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

absFromSign : (s : Sign) -> Not (s = Zero) -> abs (fromSign s) = 1
absFromSign Plus  _  = Refl
absFromSign Zero  nz = absurd $ nz Refl
absFromSign Minus _  = Refl

NotNull : Type
NotNull = (k ** Not0 k)

not01 : Not0 1
not01 = really_believe_me ()

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

divRefl : (k : Integer) -> Divides k k
divRefl k = DivBy {q=1} (sym $ m1 k)
  
divTrans : (x, y, z : Integer) -> Divides x y -> Divides y z -> Divides x z
divTrans x y z (DivBy {q=q1} xy) (DivBy {q=q2} yz) = 
  DivBy {q=q2*q1} $ rewrite sym $ massoc q2 q1 x in rewrite sym xy in yz

--zeroNotDivides : Divides d x -> Not (x=0) -> Not (d=0)
--zeroNotDivides {d} (DivBy {q} dx) xnz = snd $ mulnz2 {a=q} {b=d} $ rewrite sym dx in xnz

data LCM : (i : Integer) -> (j : Integer) -> (d : Integer) -> Type where
  MkLCM : Divides i d
       -> Divides j d
       -> ((m : Integer) -> Divides i m -> Divides j m -> Divides d m)
       -> LCM i j d

lcm : (i, j : Integer) -> (d ** LCM i j d)
lcm i j = ?lcm

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

Zero : Exp n
Zero {n} = Val {n} 0

MulV0 : (k : Integer) -> Exp (S n)
MulV0 k = k `Times` Var FZ

-- Quantifier free

data IsQFree : Form n -> Type where
  LtQF  : {t1, t2 : Exp n} -> IsQFree (Lt t1 t2)
  GtQF  : {t1, t2 : Exp n} -> IsQFree (Gt t1 t2)
  LteQF : {t1, t2 : Exp n} -> IsQFree (Lte t1 t2)
  GteQF : {t1, t2 : Exp n} -> IsQFree (Gte t1 t2)
  EquQF : {t1, t2 : Exp n} -> IsQFree (Equ t1 t2)
  DvdQF : {k : Integer} -> {t : Exp n} -> IsQFree (Dvd k t)
  NotQF : {f : Form n} -> (pr : IsQFree f) -> IsQFree (Notf f)
  ConjQF : {f1, f2 : Form n} -> (pr1 : IsQFree f1) -> (pr2 : IsQFree f2) -> IsQFree (Conj f1 f2)
  DisjQF : {f1, f2 : Form n} -> (pr1 : IsQFree f1) -> (pr2 : IsQFree f2) -> IsQFree (Disj f1 f2)
  ImplQF : {f1, f2 : Form n} -> (pr1 : IsQFree f1) -> (pr2 : IsQFree f2) -> IsQFree (Impl f1 f2)

QFree : Nat -> Type
QFree n = (f : Form n ** IsQFree f)

-- Negation normal form

data IsNNF : Form n -> Type where
  LteNNF  : {t1, t2 : Exp n} -> IsNNF (Lte t1 t2)
  EquNNF  : {t1, t2 : Exp n} -> IsNNF (Equ t1 t2)
  NeqNNF  : {t1, t2 : Exp n} -> IsNNF (Notf (Equ t1 t2))
  DvdNNF  : {k : Integer} -> {t : Exp n} -> IsNNF (Dvd k t)
  NdvdNNF : {k : Integer} -> {t : Exp n} -> IsNNF (Notf (Dvd k t))
  ConjNNF : {f1, f2 : Form n} -> (pr1 : IsNNF f1) -> (pr2 : IsNNF f2) -> IsNNF (Conj f1 f2)
  DisjNNF : {f1, f2 : Form n} -> (pr1 : IsNNF f1) -> (pr2 : IsNNF f2) -> IsNNF (Disj f1 f2)

NNF : Nat -> Type
NNF n = (f : Form n ** IsNNF f)

-- TODO: `assert_total` needed since Idris apparently can't see structure decreasing under sigma

nnfNeg : (f : NNF n) -> NNF n
nnfNeg (Lte t1 t2 ** LteNNF)           = ((t2 `Plus` (Val 1)) `Lte` t1 ** LteNNF)
nnfNeg (Equ t1 t2 ** EquNNF)           = (Notf (t1 `Equ` t2) ** NeqNNF)
nnfNeg (Notf (Equ t1 t2) ** NeqNNF)    = (t1 `Equ` t2 ** EquNNF)
nnfNeg (Dvd k t ** DvdNNF)             = (Notf (Dvd k t) ** NdvdNNF)
nnfNeg (Notf (Dvd k t) ** NdvdNNF)     = (Dvd k t ** DvdNNF)
nnfNeg (Conj f1 f2 ** ConjNNF nf1 nf2) = case ( assert_total $ nnfNeg (f1 ** nf1)
                                              , assert_total $ nnfNeg (f2 ** nf2)) of
    ((p1 ** np1), (p2 ** np2)) => (p1 `Disj` p2 ** DisjNNF np1 np2)
nnfNeg (Disj f1 f2 ** DisjNNF nf1 nf2) = case ( assert_total $ nnfNeg (f1 ** nf1)
                                              , assert_total $ nnfNeg (f2 ** nf2)) of
    ((p1 ** np1), (p2 ** np2)) => (p1 `Conj` p2 ** ConjNNF np1 np2)

qfreeNnf : (f : QFree n) -> NNF n
qfreeNnf (Lt t1 t2 ** LtQF)             = ((t1 `Plus` (Val 1)) `Lte` t2 ** LteNNF)
qfreeNnf (Gt t1 t2 ** GtQF)             = ((t2 `Plus` (Val 1)) `Lte` t1 ** LteNNF)
qfreeNnf (Lte t1 t2 ** LteQF)           = (t1 `Lte` t2 ** LteNNF)
qfreeNnf (Gte t1 t2 ** GteQF)           = (t2 `Lte` t1 ** LteNNF)
qfreeNnf (Equ t1 t2 ** EquQF)           = (t1 `Equ` t2 ** EquNNF)
qfreeNnf (Dvd k t ** DvdQF)             = (Dvd k t ** DvdNNF)
qfreeNnf (Notf f ** NotQF qf)           = nnfNeg (assert_total $ qfreeNnf (f ** qf))
qfreeNnf (Conj f1 f2 ** ConjQF qf1 qf2) = case ( assert_total $ qfreeNnf (f1 ** qf1)
                                               , assert_total $ qfreeNnf (f2 ** qf2)) of
  ((p1 ** np1), (p2 ** np2)) => (p1 `Conj` p2 ** ConjNNF np1 np2)
qfreeNnf (Disj f1 f2 ** DisjQF qf1 qf2) = case ( assert_total $ qfreeNnf (f1 ** qf1)
                                               , assert_total $ qfreeNnf (f2 ** qf2)) of
  ((p1 ** np1), (p2 ** np2)) => (p1 `Disj` p2 ** DisjNNF np1 np2)
qfreeNnf (Impl f1 f2 ** ImplQF qf1 qf2) = case (nnfNeg $ assert_total $ qfreeNnf (f1 ** qf1)
                                                       , assert_total $ qfreeNnf (f2 ** qf2)) of
  ((p1 ** np1), (p2 ** np2)) => (p1 `Disj` p2 ** DisjNNF np1 np2)

-- Linearisation

data IsELin : (n0 : Nat) -> (e : Exp n) -> Type where
  ValEL : {n0 : Nat} -> {k : Integer} -> IsELin n0 (Val {n} k)
  VarEL : {n0 : Nat} -> {k : Integer} -> {p : Fin n} -> {r : Exp n}
       -> (knz : Not0 k)
       -> (n0lep : n0 `Nat.LTE` finToNat p)
       -> (pr : IsELin (S (finToNat p)) r)
       -> IsELin n0 (Plus (Times k (Var p)) r)

ELin : Nat -> Nat -> Type
ELin n p = (e : Exp n ** IsELin p e)

data IsLin : Form n -> Type where
  LteLin  : {t : Exp n} -> (pr : IsELin Z t) -> IsLin (Lte t Zero)
  EqLin   : {t : Exp n} -> (pr : IsELin Z t) -> IsLin (Equ t Zero)
  NeqLin  : {t : Exp n} -> (pr : IsELin Z t) -> IsLin (Notf $ Equ t Zero)
  DvdLin  : {k : Integer} -> {t : Exp n} -> (knz : Not0 k) -> (pr : IsELin Z t) -> IsLin (Dvd k t)
  NdvdLin : {k : Integer} -> {t : Exp n} -> (knz : Not0 k) -> (pr : IsELin Z t) -> IsLin (Notf $ Dvd k t)
  ConjLin : {f1, f2 : Form n} -> (pr1 : IsLin f1) -> (pr2 : IsLin f2) -> IsLin (Conj f1 f2)
  DisjLin : {f1, f2 : Form n} -> (pr1 : IsLin f1) -> (pr2 : IsLin f2) -> IsLin (Disj f1 f2)

Lin : Nat -> Type
Lin n = (f : Form n ** IsLin f)

linInject : Nat.LTE p1 p2 -> IsELin p2 r -> IsELin p1 r
linInject _     ValEL               = ValEL
linInject le12 (VarEL knz le2p pr) = VarEL knz (lteTransitive le12 le2p) pr

linNeg : ELin n p -> ELin n p
linNeg (Val k ** ValEL) = (Val (-k) ** ValEL)
linNeg (Plus (Times k (Var p)) r ** VarEL knz n0lep pr) = case assert_total $ linNeg (r ** pr) of
  (e ** pe) => (((-k) `Times` (Var p)) `Plus` e ** VarEL (knz . m0p0 k) n0lep pe)

linPlus : ELin n p -> ELin n p -> ELin n p
linPlus (Val k ** ValEL)                                 (Val l ** ValEL)                                 = (Val (k+l) ** ValEL)
linPlus (Val k ** ValEL)                                 (Plus (Times l (Var t)) r ** VarEL lnz n0let pr) =
  case assert_total $ linPlus (Val k ** ValEL) (r ** pr) of
    (e ** pe) => ((l `Times` (Var t)) `Plus` e ** VarEL lnz n0let pe)
linPlus (Plus (Times k (Var p)) r ** VarEL knz n0lep pr) (Val l ** ValEL)                                 =
  case assert_total $ linPlus (r ** pr) (Val l ** ValEL) of
    (e ** pe) => ((k `Times` (Var p)) `Plus` e ** VarEL knz n0lep pe)
linPlus (Plus (Times k (Var p)) r ** VarEL knz n0lep pr) (Plus (Times l (Var t)) s ** VarEL lnz n0let ps) with (fCompare p t)
  | Less lpt = case assert_total $ linPlus (r ** pr) (Plus (Times l (Var t)) s ** VarEL lnz lpt ps) of
                 (e ** pe) => ((k `Times` (Var p)) `Plus` e ** VarEL knz n0lep pe)
  | Equal ept = case assert_total $ linPlus (r ** pr) (s ** rewrite ept in ps) of
                  (e ** pe) => case decEq (k+l) 0 of
                                Yes _  => (e ** linInject (lteSuccRight n0lep) pe)
                                No neq => (((k+l) `Times` (Var p)) `Plus` e ** VarEL neq n0lep pe)
  | Greater gpt = case assert_total $ linPlus (Plus (Times k (Var p)) r ** VarEL knz gpt pr) (s ** ps) of
                    (e ** pe) => ((l `Times` (Var t)) `Plus` e ** VarEL lnz n0let pe)

linMult : Integer -> ELin n p -> ELin n p
linMult x (Val k ** ValEL)                                 = (Val (x * k) ** ValEL)
linMult x (Plus (Times k (Var p)) r ** VarEL knz n0lep pr) = case decEq x 0 of
  Yes _ => (Val 0 ** ValEL)
  No xnz => case assert_total $ linMult x (r ** pr) of
          (e ** pe) => (((x*k) `Times` (Var p)) `Plus` e ** VarEL (mulnz xnz knz) n0lep pe)

elin : Exp n -> ELin n Z
elin (Val k)       = (Val k ** ValEL)
elin (Var p)       = ((1 `Times` (Var p)) `Plus` Zero ** VarEL not01 LTEZero ValEL)
elin (Negate e)    = linNeg (elin e)
elin (Plus e1 e2)  = linPlus (elin e1) (elin e2)
elin (Minus e1 e2) = linPlus (elin e1) (linNeg $ elin e2)
elin (Times k e)   = linMult k (elin e)

lin : NNF n -> Lin n
lin (Lte t1 t2 ** LteNNF)           = case elin (t1 `Minus` t2) of
  (e ** pe) => (e `Lte` Zero ** LteLin pe)
lin (Equ t1 t2 ** EquNNF)           = case elin (t1 `Minus` t2) of
  (e ** pe) => (e `Equ` Zero ** EqLin pe)
lin (Notf (Equ t1 t2) ** NeqNNF)    = case elin (t1 `Minus` t2) of
  (e ** pe) => (Notf (e `Equ` Zero) ** NeqLin pe)
lin (Dvd k t ** DvdNNF)             = case elin t of
  (e ** pe) => case decEq k 0 of
    Yes _ => (e `Equ` Zero ** EqLin pe)
    No knz => (k `Dvd` e ** DvdLin knz pe)
lin (Notf (Dvd k t) ** NdvdNNF)     = case elin t of
  (e ** pe) => case decEq k 0 of
    Yes _ => (Notf (e `Equ` Zero) ** NeqLin pe)
    No knz => (Notf (k `Dvd` e) ** NdvdLin knz pe)
lin (Conj f1 f2 ** ConjNNF nf1 nf2) = case ( assert_total $ lin (f1 ** nf1)
                                           , assert_total $ lin (f2 ** nf2)) of
  ((p1 ** np1), (p2 ** np2)) => (p1 `Conj` p2 ** ConjLin np1 np2)
lin (Disj f1 f2 ** DisjNNF nf1 nf2) = case ( assert_total $ lin (f1 ** nf1)
                                           , assert_total $ lin (f2 ** nf2)) of
  ((p1 ** np1), (p2 ** np2)) => (p1 `Disj` p2 ** DisjLin np1 np2)

-- Unitarization

data EDiv : (s : NotNull) -> (e : Exp n) -> Type where
  ValED  : EDiv {n} s (Val k)
  VarNED : {t : Exp n} -> {p : Nat} -> (pr : IsELin (S p) t) -> EDiv s t
  Var0ED : {t : Exp (S n)} -> (kd : k `Divides` (fst s)) -> (pr : IsELin 1 t) -> EDiv s (MulV0 k `Plus` t)

data Div : (s : NotNull) -> Form n -> Type where
  LteDiv  : (pr : EDiv s t) -> Div s (t `Lte` Zero)
  EqDiv   : (pr : EDiv s t) -> Div s (t `Equ` Zero)
  NeqDiv  : (pr : EDiv s t) -> Div s (Notf (t `Equ` Zero))
  DvdDiv  : (knz : Not0 k) -> (pr : EDiv s t) -> Div s (k `Dvd` t)
  NdvdDiv : (knz : Not0 k) -> (pr : EDiv s t) -> Div s (Notf (k `Dvd` t))
  ConjDiv : (pr1 : Div s f1) -> (pr2 : Div s f2) -> Div s (f1 `Conj` f2)
  DisjDiv : (pr1 : Div s f1) -> (pr2 : Div s f2) -> Div s (f1 `Disj` f2)

edivExt : (pr : EDiv m e) -> (n : NotNull) -> (hDiv : Divides (fst m) (fst n)) -> EDiv n e
edivExt      ValED             _ _    = ValED
edivExt     (VarNED {p} pr)    _ _    = VarNED {p} pr
edivExt {m} (Var0ED {k} kd pr) n hDiv = Var0ED (divTrans k (fst m) (fst n) kd hDiv) pr

divExt : {m : NotNull} -> {f : Form n} -> (pr : Div m f) -> (p : NotNull) -> Divides (fst m) (fst p) -> Div p f
divExt (LteDiv pr)       p dd = LteDiv $ edivExt pr p dd
divExt (EqDiv pr)        p dd = EqDiv $ edivExt pr p dd
divExt (NeqDiv pr)       p dd = NeqDiv $ edivExt pr p dd
divExt (DvdDiv knz pr)   p dd = DvdDiv knz $ edivExt pr p dd
divExt (NdvdDiv knz pr)  p dd = NdvdDiv knz $ edivExt pr p dd
divExt (ConjDiv pr1 pr2) p dd = ConjDiv (divExt pr1 p dd) (divExt pr2 p dd)
divExt (DisjDiv pr1 pr2) p dd = DisjDiv (divExt pr1 p dd) (divExt pr2 p dd)

lcme : (e : ELin n p) -> (x : NotNull ** EDiv x (fst e))
lcme         (Val _ ** ValEL)                                  = (oneNN ** ValED {s = oneNN})
lcme {n=Z}   (Plus (Times _ (Var i)) _ ** VarEL _ _ _)         = absurd i
lcme {n=S _} (Plus (Times k (Var FZ)) _ ** VarEL knz _ pr)     = ((k ** knz) ** Var0ED (divRefl k) pr)
lcme {n=S n} (Plus (Times _ (Var (FS i))) _ ** VarEL knz _ pr) = (oneNN ** VarNED {p=finToNat i} {s=oneNN} $ VarEL knz lteRefl pr)

partial -- can't fix this with Integers
lcmf : (f : Lin n) -> (x : NotNull ** Div x (fst f))
lcmf (Lte t (Zero {n})        ** LteLin  pr)      = case lcme (t ** pr) of
                                                      (e ** pe) => (e ** LteDiv pe)
lcmf (Equ t (Zero {n})        ** EqLin   pr)      = case lcme (t ** pr) of
                                                      (e ** pe) => (e ** EqDiv pe)
lcmf (Notf (Equ t (Zero {n})) ** NeqLin  pr)      = case lcme (t ** pr) of
                                                      (e ** pe) => (e ** NeqDiv pe)
lcmf (Dvd k t                 ** DvdLin  knz pr)  = case lcme (t ** pr) of
                                                      (e ** pe) => (e ** DvdDiv knz pe)
lcmf (Notf (Dvd k t)          ** NdvdLin knz pr)  = case lcme (t ** pr) of
                                                      (e ** pe) => (e ** NdvdDiv knz pe)
lcmf (Conj f1 f2              ** ConjLin pr1 pr2) =
  case (lcmf (f1 ** pr1), lcmf (f2 ** pr2)) of
    (((z1 ** nz1) ** d1), ((z2 ** nz2) ** d2)) =>
      case lcm z1 z2 of
        (d ** MkLCM z1d z2d prf) =>
           let dnn = (d ** lcmNeq (z1 ** nz1) (z2 ** nz2) (MkLCM z1d z2d prf)) in
           (dnn ** ConjDiv {s=dnn}
                   (divExt d1 dnn z1d)
                   (divExt d2 dnn z2d))
lcmf (Disj f1 f2              ** DisjLin pr1 pr2) =
  case (lcmf (f1 ** pr1), lcmf (f2 ** pr2)) of
    (((z1 ** nz1) ** d1), ((z2 ** nz2) ** d2)) =>
      case lcm z1 z2 of
        (d ** MkLCM z1d z2d prf) =>
           let dnn = (d ** lcmNeq (z1 ** nz1) (z2 ** nz2) (MkLCM z1d z2d prf)) in
           (dnn ** DisjDiv {s=dnn}
                   (divExt d1 dnn z1d)
                   (divExt d2 dnn z2d))

data IsEUni : Exp n -> Type where
  ValEU :  IsEUni (Val {n} k)
  VarNEU : {t : Exp n} -> (pr : IsELin (S p) t) -> IsEUni t
  Var0EU : {t : Exp (S n)} -> (k1 : abs k = 1) -> (pr : IsELin 1 t) -> IsEUni (MulV0 k `Plus` t)

EUni : Nat -> Type
EUni n = (e : Exp n ** IsEUni e)

elinEuni : {e : Exp n} -> IsELin (S p) e -> IsEUni e
elinEuni  ValEL               = ValEU
elinEuni (VarEL knz n0lep pr) = VarNEU (VarEL knz n0lep pr)

data IsUni : Form n -> Type where
  LteUni  : (pr : IsEUni t1) -> IsUni (t1 `Lte` Zero)
  EqUni   : (pr : IsEUni t1) -> IsUni (t1 `Equ` Zero)
  NeqUni  : {t1 : Exp n} -> (pr : IsEUni t1) -> IsUni (Notf $ (t1 `Equ` Zero))
  DvdUni  : {t1 : Exp n} -> (knz : Not0 k) -> (pr : IsEUni t1) -> IsUni (k `Dvd` t1)
  NdvdUni : {t1 : Exp n} -> (knz : Not0 k) -> (pr : IsEUni t1) -> IsUni (Notf $ (k `Dvd` t1))
  ConjUni : {f1, f2 : Form n} -> (pr1 : IsUni f1) -> (pr2 : IsUni f2) -> IsUni (f1 `Conj` f2)
  DisjUni : {f1, f2 : Form n} -> (pr1 : IsUni f1) -> (pr2 : IsUni f2) -> IsUni (f1 `Disj` f2)

Uni : Nat -> Type
Uni n = (f : Form n ** IsUni f)

unitExp : (e : ELin n p) -> (s : NotNull) -> EDiv s (fst e) -> EUni n
unitExp (Val k ** ValEL)          _          ValED         = (Val k ** ValEU)
unitExp (e ** _)                  _         (VarNED pr)    = (e ** elinEuni pr)
unitExp (MulV0 k `Plus` t ** he) (l ** lnz) (Var0ED (DivBy {q} lqk) pr) = 
  case linMult q (t ** pr) of 
    (i ** hi) => let skl = sign k `multiply` sign l in 
                 (MulV0 (fromSign skl) `Plus` i ** Var0EU (absFromSign skl $ mulsnz (sign k) (sign l) (notzs $ snd $ mulnz2 {a=q} {b=k} $ rewrite sym lqk in lnz) (notzs lnz)) hi)

myk : (e : ELin n p) -> (hdiv : EDiv s (fst e)) -> Integer
myk (Val _ ** _)             ValED                   = 1
myk (_ ** _)                (VarNED _)               = 1
myk (MulV0 _ `Plus` _ ** _) (Var0ED (DivBy {q} _) _) = q

mykNZ : (e : ELin n p) -> (hdiv : EDiv s (fst e)) -> Not0 (myk e hdiv)
mykNZ              (Val _ ** _)              ValED                     = not01
mykNZ              (_ ** _)                 (VarNED _)                 = not01
mykNZ {s=(_**xnz)} (MulV0 k `Plus` _ ** _)  (Var0ED (DivBy {q} xqk) _) = fst $ mulnz2 {a=q} {b=k} $ rewrite sym xqk in xnz

partial -- can't fix this with Integers
unitariseAux : (f : Lin n) -> (s : NotNull) -> Div s (fst f) -> Uni n
unitariseAux (Lte t (Zero {n})        ** LteLin  pr)      s (LteDiv pr0)        = 
  case unitExp (t ** pr) s pr0 of
    (e ** he) => (e `Lte` Zero ** LteUni he)
unitariseAux (Equ t (Zero {n})        ** EqLin   pr)      s (EqDiv  pr0)        = 
  case unitExp (t ** pr) s pr0 of
    (e ** he) => (e `Equ` Zero ** EqUni he)
unitariseAux (Notf (Equ t (Zero {n})) ** NeqLin  pr)      s (NeqDiv pr0)        = 
  case unitExp (t ** pr) s pr0 of
    (e ** he) => (Notf (e `Equ` Zero) ** NeqUni he)
unitariseAux (Dvd k t                 ** DvdLin  knz pr)  s (DvdDiv knz0 pr0)   = 
  case unitExp (t ** pr) s pr0 of
    (e ** he) => (((myk (t ** pr) pr0) * k) `Dvd` e ** DvdUni (mulnz (mykNZ (t ** pr) pr0) knz) he)
unitariseAux (Notf (Dvd k t)          ** NdvdLin knz pr)  s (NdvdDiv knz0 pr0)  = 
  case unitExp (t ** pr) s pr0 of
    (e ** he) => (Notf (((myk (t ** pr) pr0) * k) `Dvd` e) ** NdvdUni (mulnz (mykNZ (t ** pr) pr0) knz) he)
unitariseAux (Conj f1 f2              ** ConjLin pr1 pr2) s (ConjDiv pr01 pr02) = 
  case (assert_total $ unitariseAux (f1 ** pr1) s pr01, assert_total $ unitariseAux (f2 ** pr2) s pr02) of 
    ((e1 ** he1), (e2 ** he2)) => (e1 `Conj` e2 ** ConjUni he1 he2)
unitariseAux (Disj f1 f2              ** DisjLin pr1 pr2) s (DisjDiv pr01 pr02) = 
  case (assert_total $ unitariseAux (f1 ** pr1) s pr01, assert_total $ unitariseAux (f2 ** pr2) s pr02) of 
    ((e1 ** he1), (e2 ** he2)) => (e1 `Disj` e2 ** DisjUni he1 he2)

unitarise : (f : Lin n) -> Uni n
unitarise f = let (x ** xdiv) = assert_total $ lcmf f in 
              assert_total $ unitariseAux f x xdiv
