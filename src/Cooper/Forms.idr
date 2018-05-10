module Cooper.Forms

import Data.Fin
import Util

%access public export
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

-- Helpers

Zero : Exp n
Zero {n} = Val {n} 0

MulV0 : (k : Integer) -> Exp (S n)
MulV0 k = k `Times` Var FZ

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

data IsEUni : Exp n -> Type where
  ValEU :  IsEUni (Val {n} k)
  VarNEU : {t : Exp n} -> (pr : IsELin (S p) t) -> IsEUni t
  Var0EU : {t : Exp (S n)} -> (k1 : Either (k = 1) (k = -1)) -> (pr : IsELin 1 t) -> IsEUni (MulV0 k `Plus` t)

EUni : Nat -> Type
EUni n = (e : Exp n ** IsEUni e)

data IsUni : Form n -> Type where
  LteUni  : (pr : IsEUni t1) -> IsUni (t1 `Lte` Zero)
  EqUni   : (pr : IsEUni t1) -> IsUni (t1 `Equ` Zero)
  NeqUni  : {t1 : Exp n} -> (pr : IsEUni t1) -> IsUni (Notf (t1 `Equ` Zero))
  DvdUni  : {t1 : Exp n} -> (knz : Not0 k) -> (pr : IsEUni t1) -> IsUni (k `Dvd` t1)
  NdvdUni : {t1 : Exp n} -> (knz : Not0 k) -> (pr : IsEUni t1) -> IsUni (Notf (k `Dvd` t1))
  ConjUni : {f1, f2 : Form n} -> (pr1 : IsUni f1) -> (pr2 : IsUni f2) -> IsUni (f1 `Conj` f2)
  DisjUni : {f1, f2 : Form n} -> (pr1 : IsUni f1) -> (pr2 : IsUni f2) -> IsUni (f1 `Disj` f2)

Uni : Nat -> Type
Uni n = (f : Form n ** IsUni f)

-- Almost free from `Var FZ`

data IsEAF0 : Exp n -> Type where
  ValEAF0 : IsEAF0 (Val {n} k)
  VarEAF0 : {t : Exp n} -> (pr : IsELin (S p) t) -> IsEAF0 t

EAf0 : Nat -> Type
EAf0 n = (e : Exp n ** IsEAF0 e)
  
data IsAF0 : Form n -> Type where
--  TopAF0  : IsAF0 Top
--  BotAF0  : IsAF0 Bot
  LteAF0  : {t1 : Exp n} -> (pr : IsEAF0 t1) -> IsAF0 (t1 `Lte` Zero)
  EquAF0  : {t1 : Exp n} -> (pr : IsEAF0 t1) -> IsAF0 (t1 `Equ` Zero)
  NeqAF0  : {t1 : Exp n} -> (pr : IsEAF0 t1) -> IsAF0 (Notf (t1 `Equ` Zero))
  DvdAF0  : {t1 : Exp n} -> (knz : Not0 k) -> (pr : IsEUni t1) -> IsAF0 (k `Dvd` t1)
  NdvdAF0 : {t1 : Exp n} -> (knz : Not0 k) -> (pr : IsEUni t1) -> IsAF0 (Notf (k `Dvd` t1))
  ConjAF0 : {f1, f2 : Form n} -> (pr1 : IsAF0 f1) -> (pr2 : IsAF0 f2) -> IsAF0 (f1 `Conj` f2)
  DisjAF0 : {f1, f2 : Form n} -> (pr1 : IsAF0 f1) -> (pr2 : IsAF0 f2) -> IsAF0 (f1 `Disj` f2)              

Af0 : Nat -> Type
Af0 n = (f : Form n ** IsAF0 f)

-- Alldvd

data AllDvd : (s : NotNull) -> Form n -> Type where
--  TopAD  : AllDvd s Top
--  BotAD  : AllDvd s Bot
  LteAD  : {t1 : Exp n} -> AllDvd s (t1 `Lte` Zero)
  EquAD  : {t1 : Exp n} -> AllDvd s (t1 `Equ` Zero)
  NeqAD  : {t1 : Exp n} -> AllDvd s (Notf (t1 `Equ` Zero))
  DvdAD  : {t1 : Exp n} -> (knz : Not0 k) -> (pr : k `Divides` (fst s)) -> AllDvd s (k `Dvd` t1)
  NdvdAD : {t1 : Exp n} -> (knz : Not0 k) -> (pr : k `Divides` (fst s)) -> AllDvd s (Notf (k `Dvd` t1))
  ConjAD : {f1, f2 : Form n} -> (pr1 : AllDvd s f1) -> (pr2 : AllDvd s f2) -> AllDvd s (f1 `Conj` f2)
  DisjAD : {f1, f2 : Form n} -> (pr1 : AllDvd s f1) -> (pr2 : AllDvd s f2) -> AllDvd s (f1 `Disj` f2)

DAll : Form n -> Type
DAll f = (s : NotNull ** AllDvd s f)  