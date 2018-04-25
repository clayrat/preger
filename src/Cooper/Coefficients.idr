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