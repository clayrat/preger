module ChaiebNipkow

import Data.So
import Data.Fin
import Data.Vect

%default total

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

NotNull : Type
NotNull = (k ** Not0 k)

not01 : Not0 1
not01 = really_believe_me ()

oneNN : NotNull
oneNN = (1 ** not01)

mulnz : Not0 a -> Not0 b -> Not0 (a*b)
mulnz anz bnz = really_believe_me ()

m0p0 : (k : Integer) -> 0-k = 0 -> k = 0
m0p0 k prf = really_believe_me prf

m1 : (k : Integer) -> k*1 = k
m1 k = really_believe_me ()

massoc : (x,y,z : Integer) -> x*(y*z) = (x*y)*z
massoc x y z = really_believe_me ()

data Divides : (d : Integer) -> Integer -> Type where
  DivBy : Divides d (d * div)

divRefl : (k : Integer) -> Divides k k
divRefl k = replace {P=\x=>Divides k x} (m1 k) (DivBy {div=1})

divTrans : (x, y, z : Integer) -> Divides x y -> Divides y z -> Divides x z
divTrans x (x*xy) ((x*xy)*yz) (DivBy {div=xy}) (DivBy {div=yz}) = replace {P=\t=>Divides x t} (massoc x xy yz) (DivBy {div=xy*yz})

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
