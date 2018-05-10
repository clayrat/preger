module Cooper

import Data.So
import Data.Vect
import Util
import Cooper.Forms
import Cooper.QElim

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

iEquiv : (f1, f2 : Form n) -> Type
iEquiv {n} f1 f2 = (r : Vect n Integer) -> (iForm f1 r -> iForm f2 r, iForm f2 r -> iForm f1 r)

-- Decision procedure

qfreeSem : (f : Form n) -> iEquiv f (fst $ qfree f)
qfreeSem  Top        _ = (id, id)
qfreeSem  Bot        _ = (id, id)
qfreeSem (Dvd k e)   _ = (id, id)
qfreeSem (Lt e1 e2)  _ = (id, id)
qfreeSem (Gt e1 e2)  _ = (id, id)
qfreeSem (Lte e1 e2) _ = (id, id)
qfreeSem (Gte e1 e2) _ = (id, id)
qfreeSem (Equ e1 e2) _ = (id, id)
qfreeSem (Notf f)    r with (qfree f) proof qf
  qfreeSem (Notf f)    r | (p ** h) = let (a, b) = qfreeSem f r in 
                                      rewrite cong {f=DPair.fst} qf in 
                                      (\x => x . b, \y => y . a)
qfreeSem (Exists f)   r = ?wot_10
qfreeSem (Forall f)   r = ?wot_11
qfreeSem (Conj f1 f2) r = ?wot_12
qfreeSem (Disj f1 f2) r = ?wot_13
qfreeSem (Impl f1 f2) r = ?wot_14
 
decPA : (f : Form n) -> (r : Vect n Integer) -> Dec (iForm f r)  
decPA f r = 
  let (p, q) = qfreeSem f r in 
  ?wat  
  --case qfreeDec (qfree f) r of 
  --  Yes h => Yes (q h)
  --  No nh => No (\x => nh (p x))  