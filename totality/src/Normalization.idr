
module Normalization



import MSubst
import PnP
import R
import Step
import Subst
import Term
import Typing


%default total



----------------------------------------------------------------
-- Begin: PREDICATE 'Halts' IS PRESERVED UNDER TERM CONSTRUCTION

mSubstHalts_Abs : (e : Term) -> (venv : VEnv ctx) ->
                  Halts (msubst (TAbs e) Z venv)
mSubstHalts_Abs e VNil = H (TAbs e) (TAbs e ** (VAbs, TStRefl _))
mSubstHalts_Abs e (VCons x _ _ venv) = mSubstHalts_Abs (subst x (S Z) e) venv



mSubstHalts_Zero : (venv : VEnv ctx) -> Halts (msubst TZero Z venv)
mSubstHalts_Zero VNil = haltsZero
mSubstHalts_Zero (VCons _ _ _ venv) = mSubstHalts_Zero venv



mSubstHalts_Succ : (e : Term) -> (venv : VEnv ctx) ->
                   Halts (msubst e Z venv) ->
                   Halts (msubst (TSucc e) Z venv)
mSubstHalts_Succ e venv (H _ (e1 ** (v1, tst))) = 
  let tst'  = congSucc tst
      eq    = mSubstSuccComm e Z venv
      tst'' = replace {P = \q => TransStep q (TSucc e1)} eq tst'
  in H _ (TSucc e1 ** (VSucc v1, tst''))



mSubstHalts_Pred : (e : Term) -> Typing ctx e TyNat -> 
                   (venv : VEnv ctx) ->
                   Halts (msubst e Z venv) ->
                   Halts (msubst (TPred e) Z venv)
mSubstHalts_Pred e ty venv (H _ (e1 ** (v1, tst))) = 
  let ty'  = mSubstPreservesTy e {ctx1=[]} ty venv
      ty'' = transPreservation _ ty' tst
  in case canonicalNat e1 ty'' v1 of
          (Left Refl) => let tst' = congPred tst .+. StPredZero
                             eq   = mSubstPredComm e Z venv
                         in rewrite (sym eq) in H _ (TZero ** (VZero, tst'))
          (Right (_ ** (v1', Refl))) => let st   = StPredSucc v1'
                                            tst' = congPred tst .+. st
                                            eq   = mSubstPredComm e Z venv
                                        in rewrite (sym eq) in H _ (_ ** (v1', tst'))

-- End: PREDICATE 'Halts' IS PRESERVED UNDER TERM CONSTRUCTION
--------------------------------------------------------------




--------------------------------------------------------------------
-- Begin: LOGICAL PREDICATE 'R' IS PRESERVED UNDER TERM CONSTRUCTION

mSubstR_Var : (i : Nat) ->
              (ctx : Context) ->
              index' i ctx = Just t ->
              (venv : VEnv ctx) ->
              r t (msubst (TVar i) Z venv)
mSubstR_Var Z     []       Refl VNil impossible
mSubstR_Var (S _) []       Refl VNil impossible
mSubstR_Var Z     (s::ctx) Refl (VCons x _ rx venv) = 
  let tyx = rTyping x rx
      eq  = mSubstPastCtx x [] tyx venv
  in rewrite eq in rx
mSubstR_Var (S i) (s::ctx) prf  (VCons x _ rx venv) = 
  mSubstR_Var i ctx prf venv



mSubstR_App : (e1 : Term) -> (e2 : Term) ->
              (venv : VEnv ctx) ->
              r (s :->: t) (msubst e1 Z venv) ->
              r s (msubst e2 Z venv) ->
              r t (msubst (TApp e1 e2) Z venv)
mSubstR_App e1 e2 venv r1 r2 = 
  let imp = rImplication r1
      r'  = imp (msubst e2 Z venv) r2
  in rewrite (sym $ mSubstAppComm e1 e2 Z venv) in r'



mSubstR_Ifz : (e1 : Term) -> Typing ctx e1 TyNat ->
              (e2 : Term) -> (e3 : Term) -> 
              (venv : VEnv ctx) ->
              r TyNat (msubst e1 Z venv) -> 
              r t (msubst e2 Z venv) -> 
              r t (msubst e3 Z venv) ->
              r t (msubst (TIfz e1 e2 e3) Z venv)
mSubstR_Ifz e1 ty1 e2 e3 venv r1 r2 r3 =
  let (H _ (e11 ** (v11, tst))) = rHalts r1
      ty11 = mSubstPreservesTy e1 ty1 {ctx1=[]} venv
      ty12 = transPreservation _ ty11 tst
  in case canonicalNat e11 ty12 v11 of
     (Left Refl) => let tst' = congIfz tst 
                                       {ez=(msubst e2 Z venv)} 
                                       {es=(msubst e3 Z venv)}
                               .+. StIfzZero
                        ty = TyIfz ty11 (rTyping _ r2) (rTyping _ r3)
                        r' = transStepPreservesR_2 _ _ ty _ tst' r2
                    in rewrite (sym $ mSubstIfzComm e1 e2 e3 Z venv) in r'
     (Right (_ ** (v11', Refl))) => let tst' = congIfz tst 
                                                       {ez=(msubst e2 Z venv)} 
                                                       {es=(msubst e3 Z venv)}
                                               .+. StIfzSucc v11'
                                        ty = TyIfz ty11 (rTyping _ r2) (rTyping _ r3)
                                        r' = transStepPreservesR_2 _ _ ty _ tst' r3
                                    in rewrite (sym $ mSubstIfzComm e1 e2 e3 Z venv) in r'



mSubstR_Rec' : (e1 : Term) -> Value e1 -> Typing [] e1 TyNat -> r TyNat e1 ->
               (e2 : Term) -> (e3 : Term) ->
               (venv : VEnv ctx) ->
               r t (msubst e2 Z venv) -> 
               r (TyNat:->:t:->:t) (msubst e3 Z venv) ->               
               r t (TRec e1 (msubst e2 Z venv) (msubst e3 Z venv))
--
mSubstR_Rec' TZero VZero TyZero r1 e2 e3 venv r2 r3 = 
 let st  = StRecZero {t0=(msubst e2 Z venv)} {t1=(msubst e3 Z venv)}
     ty  = TyRec TyZero (rTyping _ r2) (rTyping _ r3)
 in stepPreservesR_2 _ _ ty _ st r2
--
mSubstR_Rec' (TSucc e1) (VSucc v1) (TySucc ty1) r1 e2 e3 venv r2 r3 =
  let r1' = succRR r1
      ih  = mSubstR_Rec' e1 v1 ty1 r1' e2 e3 venv r2 r3
      rf  = rImplication $ (rImplication r3) _ r1'
      r'  = rf _ ih
      --
      st   = StRecSucc (VSucc v1) {t0=(msubst e2 Z venv)} {t1=(msubst e3 Z venv)}
      ty   = TyRec (TySucc ty1) (rTyping _ r2) (rTyping _ r3)
  in stepPreservesR_2 _ _ ty _ st r'
--
mSubstR_Rec' (TAbs e1)  VAbs _ r1 e2 e3 venv r2 r3 impossible


mSubstR_Rec : (e1 : Term) -> Typing ctx e1 TyNat ->
              (e2 : Term) -> (e3 : Term) ->
              (venv : VEnv ctx) ->
              r TyNat (msubst e1 Z venv)  ->
              r t (msubst e2 Z venv) -> 
              r (TyNat:->:t:->:t) (msubst e3 Z venv) ->               
              r t (msubst (TRec e1 e2 e3) Z venv)
mSubstR_Rec e1 ty1 e2 e3 venv r1 r2 r3 = 
  let (H _ (e11 ** (v11, tst))) = rHalts r1
      tst' = congRec tst {e0=(msubst e2 Z venv)} {e1=(msubst e3 Z venv)}
      ty11 = mSubstPreservesTy e1 ty1 {ctx1=[]} venv
      ty   = TyRec ty11 (rTyping _ r2) (rTyping _ r3)
      ty12 = transPreservation _ ty11 tst
  in case canonicalNat e11 ty12 v11 of
     (Left Refl) => let r'   = mSubstR_Rec' TZero VZero ty12 rZero e2 e3 venv r2 r3
                        r''  = transStepPreservesR_2 _ _ ty _ tst' r'
                    in rewrite (sym $  mSubstRecComm e1 e2 e3 Z venv) in r''
     (Right (_ ** (_, Refl))) => let r1' = transStepPreservesR_1 _ _ _ tst r1
                                     r'  = mSubstR_Rec' _ v11 ty12 r1' e2 e3 venv r2 r3
                                     r'' = transStepPreservesR_2 _ _ ty _ tst' r' 
                                 in rewrite (sym $  mSubstRecComm e1 e2 e3 Z venv) in r''

-- End: LOGICAL PREDICATE 'R' IS PRESERVED UNDER TERM CONSTRUCTION
------------------------------------------------------------------




--------------------------------------------------
-- Begin: PREDICATE 'R' HOLDS FOR ALL CLOSED TERMS

mutual
  mSubstR : (e : Term) -> (t : Ty) ->
            Typing ctx e t -> (venv : VEnv ctx) ->
            r t (msubst e Z venv)
  mSubstR e t ty venv = 
    let h   = mSubstHalts e t ty venv
        ty' = mSubstPreservesTy e {ctx1=[]} ty venv
    in case t of
            TyNat => (ty', h)
            (TyFun t1 t2) => let rf = mSubstR_Fun e t1 t2 ty venv
                             in (ty', h, rf)


  mSubstHalts : (e : Term) -> (t : Ty) ->
                Typing ctx e t -> (venv : VEnv ctx) ->
                Halts (msubst e Z venv)
  --
  mSubstHalts (TVar i) t (TyVar prf) venv = rHalts $ mSubstR_Var _ _ prf venv
  --
  mSubstHalts (TAbs e) (s :->: y) (TyAbs s ty) venv = mSubstHalts_Abs e venv
  --
  mSubstHalts (TApp e1 e2) t (TyApp ty1 ty2) venv =
    let r1  = mSubstR e1 _ ty1 venv
        r2  = mSubstR e2 _ ty2 venv
    in rHalts $ mSubstR_App e1 e2 venv r1 r2
  --
  mSubstHalts (TRec e1 e2 e3) t (TyRec ty1 ty2 ty3) venv =
    let r1  = mSubstR e1 _ ty1 venv
        r2  = mSubstR e2 _ ty2 venv
        r3  = mSubstR e3 _ ty3 venv
    in rHalts $ mSubstR_Rec e1 ty1 e2 e3 venv r1 r2 r3
  --
  mSubstHalts TZero TyNat TyZero venv = mSubstHalts_Zero venv
  --
  mSubstHalts (TSucc e) TyNat (TySucc ty) venv = 
    let h = rHalts $ mSubstR e _ ty venv
    in mSubstHalts_Succ e venv h
  --
  mSubstHalts (TPred e) TyNat (TyPred ty) venv =
    let h = rHalts $ mSubstR e _ ty venv
    in mSubstHalts_Pred e ty venv h  
  --
  mSubstHalts (TIfz e1 e2 e3) t (TyIfz ty1 ty2 ty3) venv =
    let r1  = mSubstR e1 _ ty1 venv
        r2  = mSubstR e2 _ ty2 venv
        r3  = mSubstR e3 _ ty3 venv
    in rHalts $ mSubstR_Ifz e1 ty1 e2 e3 venv r1 r2 r3
  
  
  mSubstR_Fun : (e : Term) -> (s : Ty) -> (t : Ty) ->
                Typing ctx e (s:->:t) -> (venv : VEnv ctx) ->
                rFun s t (msubst e Z venv)
  --
  mSubstR_Fun (TVar i) s t (TyVar prf) venv y ry = 
    let r'  = mSubstR_Var _ _ prf venv
        imp = rImplication r'
    in imp y ry
  --
  mSubstR_Fun (TAbs e) s t (TyAbs s ty) venv y ry {ctx} = 
    let H _ (y1 ** (vy1, tsty)) = rHalts ry
        ry1  = transStepPreservesR_1 s _ _ tsty ry
        tst1 = congApp2 {e=(TAbs $ msubst e (S Z) venv)} {v=VAbs} tsty
        tst2 = tst1 .+. (StBeta vy1)
        eq1  = mSubstAbsComm e Z venv
        tst3 = replace {P = \q => TransStep (TApp q y)
                                            (subst y1 Z (msubst e (S Z) venv))}
                       eq1 tst2
        eq2  = mSubstSubstSwap' e Z venv {s=s} y1 vy1 ry1
        tst4 = replace {P = \q => TransStep (TApp (msubst (TAbs e) Z venv) y) q} 
                       eq2 tst3
        r'   = mSubstR e t ty (VCons y1 vy1 ry1 venv)
        ty'  = mSubstPreservesTy {ctx1=[]} (TAbs e) (TyAbs s ty) venv
        ty'' = TyApp ty' (rTyping y ry)
    in transStepPreservesR_2 t _ ty'' _ tst4 r'
  --
  mSubstR_Fun (TApp e1 e2) s t (TyApp ty1 ty2) venv y ry = 
    let r1  = mSubstR e1 _ ty1 venv
        r2  = mSubstR e2 _ ty2 venv
        r'  = mSubstR_App e1 e2 venv r1 r2
        imp = rImplication r'
    in imp y ry
  --
  mSubstR_Fun (TRec e1 e2 e3) s t (TyRec ty1 ty2 ty3) venv y ry =
    let r1  = mSubstR e1 _ ty1 venv
        r2  = mSubstR e2 _ ty2 venv
        r3  = mSubstR e3 _ ty3 venv
        r'  = mSubstR_Rec e1 ty1 e2 e3 venv r1 r2 r3
        imp = rImplication r'
    in imp y ry
  --
  mSubstR_Fun (TIfz e1 e2 e3) s t (TyIfz ty1 ty2 ty3) venv y ry = 
    let r1  = mSubstR e1 _ ty1 venv
        r2  = mSubstR e2 _ ty2 venv
        r3  = mSubstR e3 _ ty3 venv
        r'  = mSubstR_Ifz e1 ty1 e2 e3 venv r1 r2 r3
        imp = rImplication r'
    in imp y ry



-- Finally, the fact that 'R' holds for all
-- closed terms implies that evaluation halts
-- for all closed terms; i.e. all closed terms
-- are normalizable: 
halts : (e : Term) -> Typing [] e t -> Halts e
halts e ty = let r = mSubstR e _ ty VNil
             in rHalts r

-- End: PREDICATE 'R' HOLDS FOR ALL CLOSED TERMS
------------------------------------------------
