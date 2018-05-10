module Cooper.Coefficients

import Data.Fin
import Util
import Cooper.Forms
import Cooper.Normalize
import Cooper.Properties

%access public export
%default total

-- Coefficients              

bset : (f : Uni n) -> List (ELin n 1)
bset (((MulV0   1 ) `Plus` t) `Lte` Zero ** LteUni (Var0EU (Left  Refl) pr))        = 
  [linPlus (linNeg (t ** pr)) (Val (-1) ** ValEL)]
bset (((MulV0 (-1)) `Plus` t) `Lte` Zero ** LteUni (Var0EU (Right Refl) pr))        = 
  [(t ** pr), linPlus (t ** pr) (Val (-1) ** ValEL)]
bset (((MulV0   1 ) `Plus` t) `Equ` Zero ** EqUni (Var0EU (Left  Refl) pr))         = 
  [linPlus (linNeg (t ** pr)) (Val (-1) ** ValEL)]
bset (((MulV0 (-1)) `Plus` t) `Equ` Zero ** EqUni (Var0EU (Right Refl) pr))         = 
  [linPlus (t ** pr) (Val (-1) ** ValEL)]
bset (Notf $ ((MulV0   1 ) `Plus` t) `Equ` Zero ** NeqUni (Var0EU (Left  Refl) pr)) = 
  [linNeg (t ** pr)]
bset (Notf $ ((MulV0 (-1)) `Plus` t) `Equ` Zero ** NeqUni (Var0EU (Right Refl) pr)) = 
  [(t ** pr)]
bset (f1 `Conj` f2 ** ConjUni pr1 pr2)                                              = 
  assert_total (bset (f1 ** pr1)) ++ assert_total (bset (f2 ** pr2))
bset (f1 `Disj` f2 ** DisjUni pr1 pr2)                                              = 
  assert_total (bset (f1 ** pr1)) ++ assert_total (bset (f2 ** pr2))
bset (_ ** _) = []

-- TODO checks instead of Top/Bot?
partial -- also likely not fixeable with Integers
minusinf : (f : Uni n) -> Af0 n
minusinf ((MulV0   1  `Plus` t)        `Lte` Zero ** LteUni (Var0EU (Left  Refl) pr)) = 
  (Bot ** BotAF0) 
minusinf ((MulV0 (-1) `Plus` t)        `Lte` Zero ** LteUni (Var0EU (Right Refl) pr)) = 
  (Top ** TopAF0)   
minusinf ((MulV0   _  `Plus` _)        `Equ` Zero ** EqUni  (Var0EU _ _))             = 
  (Bot ** BotAF0)
minusinf (Notf $ (MulV0   _  `Plus` _) `Equ` Zero ** NeqUni (Var0EU _ _))             = 
  (Top ** TopAF0)
minusinf (k `Dvd` t                               ** DvdUni  knz pr)                  = 
  (k `Dvd` t ** DvdAF0 knz pr)
minusinf (Notf (k `Dvd` t)                        ** NdvdUni knz pr)                  = 
  (Notf (k `Dvd` t) ** NdvdAF0 knz pr)
minusinf (f1 `Conj` f2                            ** ConjUni pr1 pr2)                 = 
  case (assert_total $ minusinf (f1 ** pr1), assert_total $ minusinf (f2 ** pr2)) of 
    ((p1 ** h1), (p2 ** h2)) => (p1 `Conj` p2 ** ConjAF0 h1 h2)
minusinf (f1 `Disj` f2                            ** DisjUni pr1 pr2)                 = 
  case (assert_total $ minusinf (f1 ** pr1), assert_total $ minusinf (f2 ** pr2)) of 
    ((p1 ** h1), (p2 ** h2)) => (p1 `Disj` p2 ** DisjAF0 h1 h2)
-- writing these together with other corresponding cases blows up the coverage checker for some reason
minusinf ((Val k)                     `Lte` Zero  ** LteUni  ValEU)                   = 
  (Val k `Lte` Zero  ** LteAF0 ValEAF0)
minusinf (t                           `Lte` Zero  ** LteUni (VarNEU pr))              = 
  (t `Lte` Zero ** LteAF0 $ VarEAF0 pr)
minusinf (Val k                       `Equ` Zero  ** EqUni   ValEU)                   = 
  (Val k `Equ` Zero ** EquAF0 ValEAF0)
minusinf (t                           `Equ` Zero  ** EqUni  (VarNEU pr))              = 
  (t `Equ` Zero ** EquAF0 $ VarEAF0 pr)
minusinf (Notf (Val k                 `Equ` Zero) ** NeqUni  ValEU)                   = 
  (Notf (Val k `Equ` Zero) ** NeqAF0 ValEAF0)
minusinf (Notf (t                     `Equ` Zero) ** NeqUni (VarNEU pr))              = 
  (Notf (t `Equ` Zero) ** NeqAF0 $ VarEAF0 pr)

partial -- also likely not fixeable with Integers  
lcmDvd : (f : Af0 n) -> DAll (fst f)
lcmDvd (Top                 ** TopAF0)        = (oneNN ** TopAD)
lcmDvd (Bot                 ** BotAF0)        = (oneNN ** BotAD)
lcmDvd (t `Lte` Zero        ** LteAF0 _)      = (oneNN ** LteAD)
lcmDvd (t `Equ` Zero        ** EquAF0 _)      = (oneNN ** EquAD)
lcmDvd (Notf (t `Equ` Zero) ** NeqAF0 _)      = (oneNN ** NeqAD)
lcmDvd (k `Dvd` t           ** DvdAF0 knz _)  = ((k ** knz) ** DvdAD knz divRefl)
lcmDvd (Notf (k `Dvd` t)    ** NdvdAF0 knz _) = ((k ** knz) ** NdvdAD knz divRefl)
lcmDvd (p1 `Conj` p2        ** ConjAF0 h1 h2) = case (lcmDvd (p1 ** h1), lcmDvd (p2 ** h2)) of
                                                  (((s1 ** sz1) ** pr1), ((s2 ** sz2) ** pr2)) => 
                                                    let (s ** sl) = lcm s1 s2
                                                        sz = lcmNeq (s1 ** sz1) (s2 ** sz2) sl
                                                        MkLCM di dj least = sl
                                                       in 
                                                    ((s ** sz) ** ConjAD (alldvdExt pr1 (s ** sz) di) (alldvdExt pr2 (s ** sz) dj))
lcmDvd (p1 `Disj` p2        ** DisjAF0 h1 h2) = case (lcmDvd (p1 ** h1), lcmDvd (p2 ** h2)) of
                                                  (((s1 ** sz1) ** pr1), ((s2 ** sz2) ** pr2)) => 
                                                    let (s ** sl) = lcm s1 s2
                                                        sz = lcmNeq (s1 ** sz1) (s2 ** sz2) sl
                                                        MkLCM di dj least = sl
                                                       in 
                                                    ((s ** sz) ** DisjAD (alldvdExt pr1 (s ** sz) di) (alldvdExt pr2 (s ** sz) dj))

bjset : (f : Uni n) -> (j : Fin p) -> List (ELin n 1)
bjset f j = map (\u => linPlus u (Val (finToInteger j) ** ValEL)) (bset f)

dExtract : (d : DAll f) -> Nat
dExtract d = fromInteger $ abs $ fst $ fst d

myD : (f : Uni n) -> Nat
myD f = dExtract (assert_total $ lcmDvd (assert_total $ minusinf f))

jset : (f : Uni n) -> Nat
jset f = S (myD f)