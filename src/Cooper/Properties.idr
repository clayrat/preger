module Cooper.Properties

import Data.Fin
import Util
import Cooper.Forms

%access public export
%default total

isNNFIsQFree : IsNNF f -> IsQFree f
isNNFIsQFree TopNNF            = TopQF
isNNFIsQFree BotNNF            = BotQF
isNNFIsQFree LteNNF            = LteQF
isNNFIsQFree EquNNF            = EquQF
isNNFIsQFree NeqNNF            = NotQF EquQF
isNNFIsQFree DvdNNF            = DvdQF
isNNFIsQFree NdvdNNF           = NotQF DvdQF
isNNFIsQFree (ConjNNF pr1 pr2) = ConjQF (isNNFIsQFree pr1) (isNNFIsQFree pr2)
isNNFIsQFree (DisjNNF pr1 pr2) = DisjQF (isNNFIsQFree pr1) (isNNFIsQFree pr2)

isLinIsNNF : IsLin f -> IsNNF f
isLinIsNNF  TopLin           = TopNNF
isLinIsNNF  BotLin           = BotNNF
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
isUniIsLin  TopUni           = TopLin
isUniIsLin  BotUni           = BotLin
isUniIsLin (LteUni pr)       = LteLin (isEUniIsELin pr)
isUniIsLin (EqUni pr)        = EqLin (isEUniIsELin pr)
isUniIsLin (NeqUni pr)       = NeqLin (isEUniIsELin pr)
isUniIsLin (DvdUni knz pr)   = DvdLin knz (isEUniIsELin pr)
isUniIsLin (NdvdUni knz pr)  = NdvdLin knz (isEUniIsELin pr)
isUniIsLin (ConjUni pr1 pr2) = ConjLin (isUniIsLin pr1) (isUniIsLin pr2)
isUniIsLin (DisjUni pr1 pr2) = DisjLin (isUniIsLin pr1) (isUniIsLin pr2)

isEAF0IsEUni : IsEAF0 e -> IsEUni e
isEAF0IsEUni  ValEAF0     = ValEU
isEAF0IsEUni (VarEAF0 pr) = VarNEU pr

isAF0IsUni : IsAF0 f -> IsUni f
isAF0IsUni  TopAF0           = TopUni
isAF0IsUni  BotAF0           = BotUni
isAF0IsUni (LteAF0 pr)       = LteUni (isEAF0IsEUni pr)
isAF0IsUni (EquAF0 pr)       = EqUni (isEAF0IsEUni pr)
isAF0IsUni (NeqAF0 pr)       = NeqUni (isEAF0IsEUni pr)
isAF0IsUni (DvdAF0 knz pr)   = DvdUni knz pr
isAF0IsUni (NdvdAF0 knz pr)  = NdvdUni knz pr
isAF0IsUni (ConjAF0 pr1 pr2) = ConjUni (isAF0IsUni pr1) (isAF0IsUni pr2)
isAF0IsUni (DisjAF0 pr1 pr2) = DisjUni (isAF0IsUni pr1) (isAF0IsUni pr2)

alldvdExt : {m : NotNull} -> {f : Form n} -> (pr : AllDvd m f) -> (p : NotNull) -> (fst m) `Divides` (fst p) -> AllDvd p f
alldvdExt TopAD            _ _   = TopAD
alldvdExt BotAD            _ _   = BotAD 
alldvdExt LteAD            _ _   = LteAD
alldvdExt EquAD            _ _   = EquAD 
alldvdExt NeqAD            _ _   = NeqAD 
alldvdExt (DvdAD knz kdm)  _ mdp = DvdAD knz (divTrans kdm mdp)
alldvdExt (NdvdAD knz kdm) _ mdp = NdvdAD knz (divTrans kdm mdp)
alldvdExt (ConjAD pr1 pr2) p mdp = ConjAD (alldvdExt pr1 p mdp) (alldvdExt pr2 p mdp)
alldvdExt (DisjAD pr1 pr2) p mdp = DisjAD (alldvdExt pr1 p mdp) (alldvdExt pr2 p mdp)