module Cooper

import Data.So
import Data.Vect
import Util
import Cooper.Forms
import Cooper.Disjunction
import Cooper.Coefficients
import Cooper.Properties
import Cooper.Normalize

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

-- Quantifier elimination

uniQelimL1 : (f : Uni (S n)) -> (j : Fin (jset f)) -> Lin n
uniQelimL1 f j = finiteDisjunctionL (fst f ** isUniIsLin (snd f)) (bjset f j)

uniQelimL : (f : Uni (S n)) -> Lin n
uniQelimL f =
  let d = assert_total $ lcmDvd $ assert_total $ minusinf f
      lf = uniQelimL1 f 
     in 
  assert_total $ finDij lf (range {len = S (dExtract d)})

uniQelimR : (f : Uni (S n)) -> Lin n
uniQelimR f = 
  let (p ** h) = assert_total $ minusinf f
      d = assert_total $ lcmDvd (p ** h) 
     in 
  assert_total $ finiteDisjunction {p1 = 1} (p ** (isUniIsLin (isAF0IsUni h))) (map (\u => (Val (finToInteger u) ** ValEL)) (range {len=dExtract d}))

uniQelim : (f : Uni (S n)) -> Lin n
uniQelim f = 
  let (f1 ** hf1) = uniQelimL f
      (f2 ** hf2) = uniQelimR f 
     in 
  (Disj f1 f2 ** DisjLin hf1 hf2)

linQelim : (f : Lin (S n)) -> Lin n
linQelim f = 
  let ((l ** lz) ** hl) = assert_total $ lcmf f
      (p ** hp) = unitarise f
     in 
   uniQelim ((l `Dvd` ((1 `Times` Var FZ) `Plus` Zero)) `Conj` p ** ConjUni (DvdUni lz (Var0EU (Left Refl) ValEL)) hp)

nnfQelim : (f : NNF (S n)) -> NNF n
nnfQelim f = 
  let (p ** hp) = linQelim (lin f) in 
  (p ** isLinIsNNF hp)

qelim : (а : QFree (S n)) -> QFree n
qelim f = 
  let (p ** hp) = nnfQelim (qfreeNnf f) in
  (p ** isNNFIsQFree hp)

-- TODO naive
--qelimF : (qe : {k : Nat} -> Form (S k) -> Form k) -> Form n -> Form n
--qelimF qe (Forall p) = Notf (qe (Notf (qelimF qe p)))
--qelimF qe (Exists p) = qe (qelimF qe p)
--qelimF qe (Conj p q) = Conj (qelimF qe p) (qelimF qe q)
--qelimF qe (Disj p q) = Disj (qelimF qe p) (qelimF qe q)
--qelimF qe (Impl p q) = Impl (qelimF qe p) (qelimF qe q)
--qelimF _  p          = p
