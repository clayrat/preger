module Cooper.Normalize

import Data.Fin
import Data.Sign
import Util
import Cooper.Forms

%access public export
%default total

-- Quantifier elimination

--qfree : (f : Form n) -> QFree n
--qfree Top = ?qfree_rhs_1
--qfree Bot = ?qfree_rhs_2
--qfree (Dvd k e) = (k `Dvd` e ** DvdQF)
--qfree (Lt e1 e2) = (e1 `Lt` e2 ** LtQF)
--qfree (Gt e1 e2) = (e1 `Gt` e2 ** GtQF)
--qfree (Lte e1 e2) = (e1 `Lte` e2 ** LteQF)
--qfree (Gte e1 e2) = (e1 `Gte` e2 ** GteQF)
--qfree (Equ e1 e2) = (e1 `Equ` e2 ** EquQF)
--qfree (Notf f) = case qfree f of 
--                   (p ** hp) = (Notf p ** NotQF hp)
--qfree (Exists f) = ?qfree_rhs_10
--qfree (Forall f) = ?qfree_rhs_11
--qfree (Conj f1 f2) = ?qfree_rhs_12
--qfree (Disj f1 f2) = ?qfree_rhs_13
--qfree (Impl f1 f2) = ?qfree_rhs_14

-- Negation normal form

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

edivExt : (pr : EDiv m e) -> (n : NotNull) -> (hDiv : Divides (fst m) (fst n)) -> EDiv n e
edivExt      ValED             _ _    = ValED
edivExt     (VarNED {p} pr)    _ _    = VarNED {p} pr
edivExt {m} (Var0ED {k} kd pr) n hDiv = Var0ED (divTrans kd hDiv) pr

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
lcme {n=S _} (Plus (Times k (Var FZ)) _ ** VarEL knz _ pr)     = ((k ** knz) ** Var0ED divRefl pr)
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

elinEuni : {e : Exp n} -> IsELin (S p) e -> IsEUni e
elinEuni  ValEL               = ValEU
elinEuni (VarEL knz n0lep pr) = VarNEU (VarEL knz n0lep pr)

unitExp : (e : ELin n p) -> (s : NotNull) -> EDiv s (fst e) -> EUni n
unitExp (Val k ** ValEL)          _          ValED         = (Val k ** ValEU)
unitExp (e ** _)                  _         (VarNED pr)    = (e ** elinEuni pr)
unitExp (MulV0 k `Plus` t ** he) (l ** lnz) (Var0ED (DivBy {q} lqk) pr) = 
  case linMult q (t ** pr) of 
    (i ** hi) => let skl = sign k `multiply` sign l 
                     sklnz = mulsnz (sign k) (sign l) (notzs $ snd $ mulnz2 {a=q} {b=k} $ rewrite sym lqk in lnz) (notzs lnz)
                    in 
                 (MulV0 (fromSign skl) `Plus` i ** Var0EU (eitherFromSign skl sklnz) hi)

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