module Cooper.QElim

import Data.Vect
import Data.Fin
import Util
import Cooper.Forms
import Cooper.Coefficients
import Cooper.Normalize
import Cooper.Properties
import Cooper.Disjunction

%access public export
%default total

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

qneg : (f : QFree n) -> QFree n
qneg (Top          ** TopQF)        = (Bot ** BotQF)
qneg (Bot          ** BotQF)        = (Top ** TopQF)
qneg (t1 `Lt` t2   ** LtQF)         = (t1 `Gte` t2 ** GteQF)
qneg (t1 `Gt` t2   ** GtQF)         = (t1 `Lte` t2 ** LteQF)
qneg (t1 `Lte` t2  ** LteQF)        = (t1 `Gt` t2 ** GtQF)
qneg (t1 `Gte` t2  ** GteQF)        = (t1 `Lt` t2 ** LtQF)
qneg (t1 `Equ` t2  ** EquQF)        = (Notf (t1 `Equ` t2) ** NotQF EquQF)
qneg (k `Dvd` t    ** DvdQF)        = (Notf (k `Dvd` t) ** NotQF DvdQF)
qneg (Notf f       ** NotQF h)      = (f ** h)
qneg (f1 `Conj` f2 ** ConjQF h1 h2) = 
  let (p1 ** hp1) = assert_total $ qneg (f1 ** h1) 
      (p2 ** hp2) = assert_total $ qneg (f2 ** h2) 
     in
  (p1 `Disj` p2 ** DisjQF hp1 hp2)
qneg (f1 `Disj` f2 ** DisjQF h1 h2) = 
  let (p1 ** hp1) = assert_total $ qneg (f1 ** h1) 
      (p2 ** hp2) = assert_total $ qneg (f2 ** h2) 
     in
  (p1 `Conj` p2 ** ConjQF hp1 hp2)
qneg (f1 `Impl` f2 ** ImplQF h1 h2) = 
  let (p2 ** hp2) = assert_total $ qneg (f2 ** h2) in
  (f1 `Conj` p2 ** ConjQF h1 hp2)

qfree : (f : Form n) -> QFree n
qfree  Top         = (Top ** TopQF)
qfree  Bot         = (Bot ** BotQF)
qfree (Dvd k e)    = (k `Dvd` e ** DvdQF)
qfree (Lt e1 e2)   = (e1 `Lt` e2 ** LtQF)
qfree (Gt e1 e2)   = (e1 `Gt` e2 ** GtQF)
qfree (Lte e1 e2)  = (e1 `Lte` e2 ** LteQF)
qfree (Gte e1 e2)  = (e1 `Gte` e2 ** GteQF)
qfree (Equ e1 e2)  = (e1 `Equ` e2 ** EquQF)
qfree (Notf f)     = let (p ** h) = qfree f in 
                     (Notf p ** NotQF h)
qfree (Exists f)   = qelim (qfree f)
qfree (Forall f)   = (qneg . qelim . qneg) (qfree f)
qfree (Conj f1 f2) = let (p1 ** h1) = qfree f1 
                         (p2 ** h2) = qfree f2
                        in 
                     (p1 `Conj` p2 ** ConjQF h1 h2)
qfree (Disj f1 f2) = let (p1 ** h1) = qfree f1 
                         (p2 ** h2) = qfree f2
                        in 
                     (p1 `Disj` p2 ** DisjQF h1 h2)
qfree (Impl f1 f2) = let (p1 ** h1) = qfree f1 
                         (p2 ** h2) = qfree f2
                        in 
                     (p1 `Impl` p2 ** ImplQF h1 h2)