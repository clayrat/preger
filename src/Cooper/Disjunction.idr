module Cooper.Disjunction

import Data.Vect
import Util
import Cooper.Forms
import Cooper.Properties
import Cooper.Normalize

%access public export
%default total

finDij : (f : a -> Lin n) -> (l : Vect (S p) a) -> Lin n
finDij f [x] = f x
finDij f (x :: x1 :: xs) = 
  let (p1 ** h1) = f x
      (p2 ** h2) = finDij f (x1 :: xs)
     in
  (p1 `Disj` p2 ** DisjLin h1 h2)

decrLin : ELin (S n) (S p) -> ELin n p
decrLin (Val k                         ** ValEL)              = (Val k ** ValEL)
decrLin (Plus (Times _ (Var  FZ))    _ ** VarEL _   n0lep _ ) = absurd n0lep
decrLin (Plus (Times k (Var (FS i))) r ** VarEL knz n0lep pr) = 
  let (r1 ** h1) = assert_total $ decrLin (r ** pr) in 
    (Plus (Times k (Var i)) r1 ** VarEL knz (fromLteSucc n0lep) h1)

instExp : (e : ELin (S n) p) -> (e1 : ELin (S n) (S p1)) -> ELin (S n) 1
instExp (Val k                         ** ValEL)               _        = (Val k ** ValEL)
instExp (Plus (Times k (Var  FZ))    r ** VarEL knz n0lep pr) (e ** he) = 
  let (e1 ** h1) = linMult k (e ** he) in 
  linPlus (e1 ** isELinWeak (LTESucc LTEZero) h1) (r ** pr)
instExp (Plus (Times k (Var (FS i))) r ** VarEL knz n0lep pr)  _        = (Plus (Times k (Var (FS i))) r ** VarEL knz (LTESucc LTEZero) pr)

partial
instForm : (f : Lin (S n)) -> (e1 : ELin (S n) (S p1)) -> Lin n
instForm (Lte t Zero        ** LteLin  pr)     e1 = 
  let (e ** he) = decrLin (instExp (t ** pr) e1) in 
  (e `Lte` Zero ** LteLin he)
instForm (Equ t Zero        ** EqLin   pr)     e1 = 
  let (e ** he) = decrLin (instExp (t ** pr) e1) in 
  (e `Equ` Zero ** EqLin he)
instForm (Notf (Equ t Zero) ** NeqLin  pr)     e1 = 
  let (e ** he) = decrLin (instExp (t ** pr) e1) in 
  (Notf (e `Equ` Zero) ** NeqLin he)
instForm (Dvd k t           ** DvdLin  knz pr) e1 = 
  let (e ** he) = decrLin (instExp (t ** pr) e1) in 
  (k `Dvd` e ** DvdLin knz he)
instForm (Notf (Dvd k t)    ** NdvdLin knz pr) e1 = 
  let (e ** he) = decrLin (instExp (t ** pr) e1) in 
  (Notf (k `Dvd` e) ** NdvdLin knz he)
instForm (Conj f1 f2        ** ConjLin pr1 pr2) e1 = 
  let (p1 ** h1) = instForm (f1 ** pr1) e1
      (p2 ** h2) = instForm (f2 ** pr2) e1
     in
  (p1 `Conj` p2 ** ConjLin h1 h2)    
instForm (Disj f1 f2        ** DisjLin pr1 pr2) e1 = 
  let (p1 ** h1) = instForm (f1 ** pr1) e1
      (p2 ** h2) = instForm (f2 ** pr2) e1
     in
  (p1 `Disj` p2 ** DisjLin h1 h2)    
    
finiteDisjunction : (f : Lin (S n)) -> (l : Vect p (ELin (S n) (S p1))) -> Lin n
finiteDisjunction _ []  = (Bot ** BotLin)
finiteDisjunction f [x] = assert_total $ instForm f x
finiteDisjunction f (x :: x1 :: xs) = 
  let (p1 ** h1) = assert_total $ instForm f x 
      (p2 ** h2) = finiteDisjunction f (x1 :: xs)
    in
      (p1 `Disj` p2 ** DisjLin h1 h2)

finiteDisjunctionL : (f : Lin (S n)) -> (l : List (ELin (S n) (S p1))) -> Lin n
finiteDisjunctionL _ []  = (Bot ** BotLin)
finiteDisjunctionL f [x] = assert_total $ instForm f x
finiteDisjunctionL f (x :: x1 :: xs) = 
  let (p1 ** h1) = assert_total $ instForm f x 
      (p2 ** h2) = finiteDisjunctionL f (x1 :: xs)
    in
      (p1 `Disj` p2 ** DisjLin h1 h2)      
