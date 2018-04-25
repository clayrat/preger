module Cooper

import Data.So
import Data.Vect
import Util
import Cooper.Forms

%access public export
%default total

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
iForm (Dvd k e)    rho = Divides k (iExp e rho)
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
