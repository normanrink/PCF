
module PnP

-- Progress and Preservation


import Step
import Subst
import SubstLemmas
import Term
import Typing


%default total
%access export



------------------
-- Begin: PROGRESS

-- Progress: a closed, well-typed term is either a value
--           or it can take a step in the reduction relation.

progress : (e : Term) -> 
           Typing [] e t ->
           Either (Value e) (e' : Term ** (Step e e'))
--
progress (TVar Z)     (TyVar Refl) impossible
progress (TVar (S _)) (TyVar Refl) impossible
--
progress (TAbs e) (TyAbs s ty) = Left VAbs
--
progress (TApp e1 e2) (TyApp ty1 ty2) = 
  case progress e1 ty1 of
    (Left v1) => case canonicalFun _ ty1 v1 of
                      (e1 ** Refl) => case progress e2 ty2 of
                                           (Left v2) => let st' = StBeta v2
                                                        in Right (_ ** st')
                                           (Right (_ ** st2)) => let st' = StApp2 v1 st2
                                                                 in Right (_ ** st')
    (Right (_ ** st1)) => let st' = StApp1 st1
                          in Right (_ ** st')
--                          
progress (TRec e1 e2 e3) (TyRec ty1 ty2 ty3) = 
  case progress e1 ty1 of
    (Left v1) => case canonicalNat _ ty1 v1 of
                      (Left Refl) => let st' = StRecZero
                                     in Right (_ ** st')
                      (Right (e' ** (v', Refl))) => let st' = StRecSucc v1
                                                    in Right (_ ** st')
    (Right (_ ** st1)) => let st' = StRec st1
                          in Right (_ ** st')
--                          
progress TZero TyZero = Left VZero
--
progress (TSucc e) (TySucc ty) = 
  case progress e ty of
       (Left v) => Left $ VSucc v
       (Right (_ ** st)) => let st' = StSucc st
                            in Right (_ ** st')
--
progress (TPred e) (TyPred ty) = 
  case progress e ty of
    (Left v) => case canonicalNat _ ty v of
                     (Left Refl) => let st' = StPredZero
                                    in Right (TZero ** st')
                     (Right (_ ** (v', Refl))) => let st' = StPredSucc v'
                                                  in Right (_ ** st')
    (Right (_ ** st)) => let st' = StPred st
                         in Right (_ ** st')
--                         
progress (TIfz e1 e2 e3) (TyIfz ty1 ty2 ty3) = 
  case progress e1 ty1 of
    (Left v1) => case canonicalNat _ ty1 v1 of
                      (Left Refl) => Right (_ ** StIfzZero)
                      (Right (_ ** (v1', Refl))) => Right (_ ** StIfzSucc v1')
    (Right (_ ** st)) => let st' = StIfz st
                         in Right (_ ** st')

-- End: PROGRESS (AND PRESERVATION)
-----------------------------------




-------------------------------------------------
-- Begin: WELL-TYPED IRREDUCIBLE TERMS ARE VALUES

irreducibleValue : (e : Term) ->
                   Typing [] e t ->
                   ((e' : Term) -> Step e e' -> Void) ->
                   Value e
irreducibleValue e ty nostep = 
  case progress e ty of
       (Left v) => v
       (Right (_ ** st)) => absurd $ nostep _ st

-- End: WELL-TYPED IRREDUCIBLE TERMS ARE VALUES
-----------------------------------------------



----------------------
-- Begin: PRESERVATION

-- Preservation: after reducing a term of type 't' by one
--               step, the resulting term is again of type 't'.

preservation : (e : Term) -> 
               Typing ctx e t ->
               Step e e' ->
               Typing ctx e' t
--               
preservation (TVar i) (TyVar prf) st impossible
--
preservation (TAbs e) (TyAbs s ty) st impossible
--
preservation (TApp e1 e2) (TyApp ty1 ty2) (StApp1 st1) =
  let ty1' = preservation e1 ty1 st1
  in TyApp ty1' ty2
preservation (TApp e1 e2) (TyApp ty1 ty2) (StApp2 v1 st2) = 
  let ty2' = preservation e2 ty2 st2
  in TyApp ty1 ty2'
preservation (TApp (TAbs e) e2) (TyApp ty1 ty2) (StBeta v2) = 
  case ty1 of
       (TyAbs s ty1') => substPreservesTy {ctx1=[]} e ty1' e2 ty2
--
preservation (TRec e1 e2 e3) (TyRec ty1 ty2 ty3) (StRec st1) = 
  let ty1' = preservation e1 ty1 st1
  in TyRec ty1' ty2 ty3
preservation (TRec TZero e2 e3) (TyRec ty1 ty2 ty3) StRecZero = ty2
preservation (TRec (TSucc n) e2 e3) (TyRec ty1 ty2 ty3) (StRecSucc v) = 
  case ty1 of
       (TySucc tyn) => let tyrn = TyRec tyn ty2 ty3
                           tya  = TyApp ty3 tyn
                       in TyApp tya tyrn
--
preservation TZero TyZero st impossible
--
preservation (TSucc e) (TySucc ty) (StSucc st) = 
  let ty' = preservation e ty st
  in TySucc ty'
--
preservation (TPred e) (TyPred ty) (StPred st) = 
  let ty' = preservation e ty st
  in TyPred ty'
preservation (TPred TZero) (TyPred ty) StPredZero = TyZero
preservation (TPred (TSucc e')) (TyPred ty) (StPredSucc v') = 
  case ty of
       (TySucc ty') => ty'
--
preservation (TIfz e1 e2 e3) (TyIfz ty1 ty2 ty3) (StIfz st1) = 
  let ty1' = preservation e1 ty1 st1
  in TyIfz ty1' ty2 ty3
preservation (TIfz TZero e2 e3) (TyIfz ty1 ty2 ty3) StIfzZero = ty2
preservation (TIfz (TSucc n) e2 e3) (TyIfz ty1 ty2 ty3) (StIfzSucc v) = ty3



transPreservation : (e : Term) -> 
                    Typing ctx e t ->
                    TransStep e e' ->
                    Typing ctx e' t
transPreservation e ty (TStRefl e)       = ty
transPreservation e ty (TStTrans st tst) = 
  let ty' = preservation e ty st
  in transPreservation _ ty' tst

-- End: PRESERVATION
--------------------

