module Cooper.Properties

import Data.Fin
import Util
import Cooper.Forms

%access public export
%default total

isNNFIsQFree : IsNNF f -> IsQFree f
isNNFIsQFree LteNNF            = LteQF
isNNFIsQFree EquNNF            = EquQF
isNNFIsQFree NeqNNF            = NotQF EquQF
isNNFIsQFree DvdNNF            = DvdQF
isNNFIsQFree NdvdNNF           = NotQF DvdQF
isNNFIsQFree (ConjNNF pr1 pr2) = ConjQF (isNNFIsQFree pr1) (isNNFIsQFree pr2)
isNNFIsQFree (DisjNNF pr1 pr2) = DisjQF (isNNFIsQFree pr1) (isNNFIsQFree pr2)

isLinIsNNF : IsLin f -> IsNNF f
isLinIsNNF (LteLin _)        = LteNNF
isLinIsNNF (EqLin _)         = EquNNF
isLinIsNNF (NeqLin _)        = NeqNNF
isLinIsNNF (DvdLin _ _)      = DvdNNF
isLinIsNNF (NdvdLin _ _)     = NdvdNNF
isLinIsNNF (ConjLin pr1 pr2) = ConjNNF (isLinIsNNF pr1) (isLinIsNNF pr2)
isLinIsNNF (DisjLin pr1 pr2) = DisjNNF (isLinIsNNF pr1) (isLinIsNNF pr2)

isELinWeak : LTE p2 p1 -> IsELin p1 e -> IsELin p2 e
isELinWeak _      ValEL               = ValEL
isELinWeak lte21 (VarEL knz n0lep pr) = VarEL knz (lteTransitive lte21 n0lep) pr

isEUniIsELin : IsEUni e -> IsELin 0 e
isEUniIsELin  ValEU                   = ValEL
isEUniIsELin (VarNEU pr)              = isELinWeak LTEZero pr
isEUniIsELin (Var0EU (Left  Refl) pr) = VarEL not01 LTEZero pr
isEUniIsELin (Var0EU (Right Refl) pr) = VarEL not0m1 LTEZero pr

isUniIsLin : IsUni f -> IsLin f
isUniIsLin (LteUni pr)       = LteLin (isEUniIsELin pr)
isUniIsLin (EqUni pr)        = EqLin (isEUniIsELin pr)
isUniIsLin (NeqUni pr)       = NeqLin (isEUniIsELin pr)
isUniIsLin (DvdUni knz pr)   = DvdLin knz (isEUniIsELin pr)
isUniIsLin (NdvdUni knz pr)  = NdvdLin knz (isEUniIsELin pr)
isUniIsLin (ConjUni pr1 pr2) = ConjLin (isUniIsLin pr1) (isUniIsLin pr2)
isUniIsLin (DisjUni pr1 pr2) = DisjLin (isUniIsLin pr1) (isUniIsLin pr2)

alldvdExt : {m : NotNull} -> {f : Form n} -> (pr : AllDvd m f) -> (p : NotNull) -> (fst m) `Divides` (fst p) -> AllDvd p f
--alldvdExt TopAD            _ _   = TopAD
--alldvdExt BotAD            _ _   = BotAD 
alldvdExt LteAD            _ _   = LteAD
alldvdExt EquAD            _ _   = EquAD 
alldvdExt NeqAD            _ _   = NeqAD 
alldvdExt (DvdAD knz kdm)  _ mdp = DvdAD knz (divTrans kdm mdp)
alldvdExt (NdvdAD knz kdm) _ mdp = NdvdAD knz (divTrans kdm mdp)
alldvdExt (ConjAD pr1 pr2) p mdp = ConjAD (alldvdExt pr1 p mdp) (alldvdExt pr2 p mdp)
alldvdExt (DisjAD pr1 pr2) p mdp = DisjAD (alldvdExt pr1 p mdp) (alldvdExt pr2 p mdp)