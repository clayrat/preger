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

-- Notations

Not0 : Integer -> Type
Not0 k = Not (k = 0)

not01 : Not0 1 
not01 = really_believe_me ()

Zero : Exp n
Zero {n} = Val {n} 0

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

nnfNeg : (f : NNF n) -> NNF n
nnfNeg (Lte t1 t2 ** LteNNF)           = ((t2 `Plus` (Val 1)) `Lte` t1 ** LteNNF)
nnfNeg (Equ t1 t2 ** EquNNF)           = (Notf (t1 `Equ` t2) ** NeqNNF)
nnfNeg (Notf (Equ t1 t2) ** NeqNNF)    = (t1 `Equ` t2 ** EquNNF)
nnfNeg (Dvd k t ** DvdNNF)             = (Notf (Dvd k t) ** NdvdNNF)
nnfNeg (Notf (Dvd k t) ** NdvdNNF)     = (Dvd k t ** DvdNNF)
nnfNeg (Conj f1 f2 ** ConjNNF nf1 nf2) = case (assert_total $ nnfNeg (f1 ** nf1)
                                              ,assert_total $ nnfNeg (f2 ** nf2)) of 
    ((p1 ** np1), (p2 ** np2)) => (p1 `Disj` p2 ** DisjNNF np1 np2)
nnfNeg (Disj f1 f2 ** DisjNNF nf1 nf2) = case (assert_total $ nnfNeg (f1 ** nf1)
                                              ,assert_total $ nnfNeg (f2 ** nf2)) of
    ((p1 ** np1), (p2 ** np2)) => (p1 `Conj` p2 ** ConjNNF np1 np2)
    
qfreeNnf : (f : QFree n) -> NNF n
qfreeNnf (Lt t1 t2 ** LtQF)             = ((t1 `Plus` (Val 1)) `Lte` t2 ** LteNNF)
qfreeNnf (Gt t1 t2 ** GtQF)             = ((t2 `Plus` (Val 1)) `Lte` t1 ** LteNNF)
qfreeNnf (Lte t1 t2 ** LteQF)           = (t1 `Lte` t2 ** LteNNF)
qfreeNnf (Gte t1 t2 ** GteQF)           = (t2 `Lte` t1 ** LteNNF)
qfreeNnf (Equ t1 t2 ** EquQF)           = (t1 `Equ` t2 ** EquNNF)
qfreeNnf (Dvd k t ** DvdQF)             = (Dvd k t ** DvdNNF)
qfreeNnf (Notf f ** NotQF qf)           = nnfNeg (assert_total $ qfreeNnf (f ** qf))
qfreeNnf (Conj f1 f2 ** ConjQF qf1 qf2) = case (assert_total $ qfreeNnf (f1 ** qf1)
                                               ,assert_total $ qfreeNnf (f2 ** qf2)) of  
  ((p1 ** np1), (p2 ** np2)) => (p1 `Conj` p2 ** ConjNNF np1 np2)
qfreeNnf (Disj f1 f2 ** DisjQF qf1 qf2) = case (assert_total $ qfreeNnf (f1 ** qf1)
                                               ,assert_total $ qfreeNnf (f2 ** qf2)) of  
  ((p1 ** np1), (p2 ** np2)) => (p1 `Disj` p2 ** DisjNNF np1 np2)
qfreeNnf (Impl f1 f2 ** ImplQF qf1 qf2) = case (nnfNeg $ assert_total $ qfreeNnf (f1 ** qf1)
                                                       , assert_total $ qfreeNnf (f2 ** qf2)) of  
  ((p1 ** np1), (p2 ** np2)) => (p1 `Disj` p2 ** DisjNNF np1 np2)

-- Linear

data IsELin : (n0 : Nat) -> (e : Exp n) -> Type where
  ValELin : {n0 : Nat} -> {k : Integer} -> IsELin n0 (Val {n} k)
  VarELin : {n0 : Nat} -> {k : Integer} -> {p : Fin n} -> {r : Exp n} 
         -> (knz : Not0 k) 
         -> (n0ltep : n0 `Nat.LTE` finToNat p) 
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