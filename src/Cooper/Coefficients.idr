module Cooper.Coefficients

import Util
import Cooper.Forms
import Cooper.Normalize

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

partial -- also likely not fixeable with Integers
minusinf : (f : Uni n) -> Af0 n
minusinf ((MulV0   1  `Plus` t)       `Lte` Zero  ** LteUni (Var0EU (Left  Refl) pr)) = 
  (Bot ** BotAF0)
minusinf ((MulV0 (-1) `Plus` t)       `Lte` Zero  ** LteUni (Var0EU (Right Refl) pr)) = 
  (Top ** TopAF0)  
minusinf ((MulV0   _  `Plus` _)       `Equ` Zero  ** EqUni  (Var0EU _ _))             = 
  (Bot ** BotAF0)
minusinf (Notf $ ((MulV0   _ ) `Plus` _) `Equ` Zero ** NeqUni (Var0EU _ _)) = 
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
