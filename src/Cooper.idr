module Cooper

import Data.So
import Data.Vect
import Util
import Cooper.Forms
import Cooper.Normalize
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

-- Equivalences

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
qfreeSem (Exists f)   r with (qfree f) proof qf
  qfreeSem (Exists f)    r | (p ** h) = let ab = qfreeSem f in  
                                        ?wot
qfreeSem (Forall f)   r = ?wot_11
qfreeSem (Conj f1 f2) r = ?wot_12
qfreeSem (Disj f1 f2) r = ?wot_13
qfreeSem (Impl f1 f2) r = ?wot_14

nnfSem : (f : QFree n) -> iEquiv (fst f) (fst $ qfreeNnf f)
nnfSem (Top ** TopQF)                 r = (id, id)
nnfSem (Bot ** BotQF)                 r = (id, id)
nnfSem (Lt t1 t2 ** LtQF)             r = ?wut3
nnfSem (Gt t1 t2 ** GtQF)             r = ?wut4
nnfSem (Lte t1 t2 ** LteQF)           r = (id, id)
nnfSem (Gte t1 t2 ** GteQF)           r = ?wut6
nnfSem (Equ t1 t2 ** EquQF)           r = (id, id)
nnfSem (Dvd k t ** DvdQF)             r = (id, id)
nnfSem (Notf f ** NotQF qf)           r = ?wut9
nnfSem (Conj f1 f2 ** ConjQF qf1 qf2) r = ?wut10
nnfSem (Disj f1 f2 ** DisjQF qf1 qf2) r = ?wut11
nnfSem (Impl f1 f2 ** ImplQF qf1 qf2) r = ?wut12

-- Decision procedure

nnfDec : (f : NNF n) -> (r : Vect n Integer) -> Dec (iForm (fst f) r)
nnfDec (Top ** TopNNF)                 r = Yes ()
nnfDec (Bot ** BotNNF)                 r = No id
nnfDec (Lte t1 t2 ** LteNNF)           r with (iExp t1 r <= iExp t2 r) 
  nnfDec (Lte t1 t2 ** LteNNF) r | True  = Yes Oh
  nnfDec (Lte t1 t2 ** LteNNF) r | False = No absurd
nnfDec (Equ t1 t2 ** EquNNF)           r = decEq (iExp t1 r) (iExp t2 r)
nnfDec (Notf (Equ t1 t2) ** NeqNNF)    r with (decEq (iExp t1 r) (iExp t2 r))
  nnfDec (Notf (Equ t1 t2) ** NeqNNF) r | Yes prf = No $ \neq => neq prf
  nnfDec (Notf (Equ t1 t2) ** NeqNNF) r | No cprf = Yes cprf
nnfDec (Dvd k t ** DvdNNF)             r = ?wat6
nnfDec (Notf (Dvd k t) ** NdvdNNF)     r = ?wat7
nnfDec (Conj f1 f2 ** ConjNNF nf1 nf2) r = case (assert_total $ nnfDec (f1 ** nf1) r, assert_total $ nnfDec (f2 ** nf2) r) of 
  (No c1 , _     ) => No $ \(i1, _) => c1 i1
  (_     , No c2 ) => No $ \(_, i2) => c2 i2
  (Yes p1, Yes p2) => Yes (p1, p2)
nnfDec (Disj f1 f2 ** DisjNNF nf1 nf2) r = case (assert_total $ nnfDec (f1 ** nf1) r, assert_total $ nnfDec (f2 ** nf2) r) of 
  (Yes p1, _     ) => Yes $ Left p1
  (_     , Yes p2) => Yes $ Right p2
  (No c1 , No c2 ) => No $ either c1 c2

qfreeDec : (f : QFree n) -> (r : Vect n Integer) -> Dec (iForm (fst f) r)
qfreeDec f r = 
  let (p, q) = nnfSem f r in 
    case nnfDec (qfreeNnf f) r of 
      Yes h => Yes (q h)
      No nh => No (\x => nh (p x))  
  
decPA : (f : Form n) -> (r : Vect n Integer) -> Dec (iForm f r)  
decPA f r = 
  let (p, q) = qfreeSem f r in 
  case qfreeDec (qfree f) r of 
    Yes h => Yes (q h)
    No nh => No (\x => nh (p x))  