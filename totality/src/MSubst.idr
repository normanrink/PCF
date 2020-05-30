
module MSubst

-- Multiple substitution in order to
-- turn a term that is well-typed in
-- a context into a closed term (i.e.
-- into a term that is well-typed in
-- the empty context).


import R
import Subst
import SubstLemmas
import Term
import Typing


%default total
%access export



-------------------------------------------------------------
-- Begin: VALUE ENVIRONMENT THAT IS COMPATIBLE WITH A CONTEXT

public export
data VEnv : Context -> Type where
  VNil  : VEnv []
  VCons : (e : Term) -> Value e -> r s e ->
          VEnv ctx -> 
          VEnv (s::ctx) 

-- End: VALUE ENVIRONMENT THAT IS COMPATIBLE WITH A CONTEXT
-----------------------------------------------------------


  

-------------------------------
-- Begin: MULTIPLE SUBSTITUTION

public export
msubst : Term -> (i : Nat) -> VEnv ctx -> Term
msubst e _ VNil = e
msubst e i (VCons x _ _ venv) = 
  let e' = subst x i e
  in msubst e' i venv

-- End: MULTIPLE SUBSTITUTION
-----------------------------




-------------------
-- Begin: WEAKENING

-- Weakening means extending a typing context
-- of a term 'e' on the right. This leaves the
-- de Bruijn indices that are referenced in 'e'
-- unchanged.
-- Weakening can be implemented with the 'shiftTerm'
-- operation by using a cutoff that is exactly the
-- length of the typing context.
-- Weakening is useful in the subsequent reasoning
-- about the 'msubst' operation.

weaken : (e : Term) -> 
         Typing ctx e t ->
         Context ->
         Term
weaken e {ctx} _ ctx' = shiftTerm (length ctx) (length ctx') e



-- Weakening does not actually change a term:
weakenIdentity : (e : Term) ->
                 (ty : Typing ctx e t) ->
                 (ctx' : Context) ->
                 weaken e ty ctx' = e
weakenIdentity e {ctx} ty ctx' = 
  let eq1 = shiftTermPastCtx e ctx ty Z (length ctx') 
      eq2 = plusZeroRightNeutral (length ctx)
      eq3 = cong {f = \q => shiftTerm q (length ctx') e} (sym eq2)
  in trans eq3 eq1



-- Weakening preserves typing, albeit in
-- an extended context:
weakenPreservesTy : (e : Term) ->
                    (ty : Typing ctx e t) ->
                    (ctx' : Context) ->
                    Typing (ctx++ctx') (weaken e ty ctx') t
weakenPreservesTy e {ctx} {t} ty ctx' = 
  let eq1 = appendNilRightNeutral ctx
      ty1 = replace {P = \q => Typing q e t} (sym eq1) ty
      ty2 = shiftTermTy e {ctx1=ctx} {ctx2=[]} ty1 ctx'
      e'  = shiftTerm (length ctx) (length ctx') e
      eq2 = appendNilRightNeutral ctx'
  in replace {P = \q => Typing (ctx++q) e' t} eq2 ty2

-- End: WEAKENING
-----------------




--------------------------------------------
-- Begin: LEMMAS ABOUT MULTIPLE SUBSTITUTION

-- Multiple substitution preserves typing:
mSubstPreservesTy : (e : Term) ->
                    Typing (ctx1++ctx2) e t ->
                    (venv : VEnv ctx2) ->
                    Typing ctx1 (msubst e (length ctx1) venv) t
mSubstPreservesTy e ty {t} VNil {ctx1} =
  let eq = appendNilRightNeutral ctx1
  in replace {P = \q => Typing q e t} eq ty
mSubstPreservesTy e ty {t} (VCons x _ rx venv) {ctx1} {ctx2 = s::ctx2} = 
  let tyx  = rTyping x rx
      x'   = weaken x tyx ctx2
      tyx1 = weakenPreservesTy x tyx ctx2
      ty'  = substPreservesTy {ctx1=ctx1} e ty x' tyx1
      eq1  = weakenIdentity x tyx ctx2
      ty'' = replace {P = \q => Typing (ctx1++ctx2) (subst q (length ctx1) e) t} eq1 ty'
  in mSubstPreservesTy (subst x (length ctx1) e) ty'' venv



-- Multiple substitution acts as the identity
-- on an expression 'e' if 'e' is typed in the
-- context 'ctx' but multiple substitution only
-- takes place at an index 'i' that is equal to
-- or greater than 'length ctx':
mSubstPastCtx : (e : Term) ->
                (ctx : Context) ->
                (Typing ctx e t) ->
                (venv : VEnv ctx') ->
                msubst e (length ctx) venv = e
mSubstPastCtx e ctx ty VNil = Refl
mSubstPastCtx e ctx ty (VCons x _ rx venv) {t} {ctx' = s::ctx'} = 
  let e'  = weaken e ty [s]
      ty1 = weakenPreservesTy e ty [s]
      tyx = rTyping x rx 
      ty2 = substPreservesTy {ctx1=ctx} {ctx2=[]} e' ty1 x tyx
      eq1 = appendNilRightNeutral ctx
      ty3 = replace {P = \q => Typing q (subst x (length ctx) e') t} eq1 ty2
      eq2 = weakenIdentity e ty [s]
      ty4 = replace {P = \q => Typing ctx (subst x (length ctx) q) t} eq2 ty3
      ih  = mSubstPastCtx (subst x (length ctx) e) ctx ty4 venv
      eq3 = substPastCtx e ctx ty {n=0}
      eq4 = cong {f = \q => subst x q e} $ plusZeroRightNeutral (length ctx)
      eq5 = trans (sym eq4) eq3
  in trans ih eq5



-- Multiple subsitution commutes with (ordinary) substitution:
mSubstSubstSwap : (e : Term) -> 
                  (i : Nat) -> (venv : VEnv ctx) ->
                  (y : Term) -> Typing [] y s ->
                  subst y i (msubst e (S i) venv) = msubst (subst y i e) i venv
mSubstSubstSwap e i VNil y tyy = Refl
mSubstSubstSwap e i (VCons x _ _ venv) y tyy = 
  let eq1 = substSwap e i y x tyy
      eq2 = cong {f = \q => msubst q i venv} eq1
      ih  = mSubstSubstSwap (subst x (S i) e) i venv y tyy
  in trans ih (sym eq2)


-- Following multiple substitution with an ordinary
-- substitution amounts to multiple substitution in
-- an extended environment:
mSubstSubstSwap' : (e : Term) -> 
                   (i : Nat) -> (venv : VEnv ctx) ->
                   (y : Term) -> (vy : Value y) -> (ry : r s y) ->
                   subst y i (msubst e (S i) venv) = msubst e i (VCons y vy ry venv)
mSubstSubstSwap' e i venv y vy ry = mSubstSubstSwap e i venv y (rTyping y ry)

-- End: LEMMAS ABOUT MULTIPLE SUBSTITUTION
------------------------------------------




---------------------------------------------------------------
-- Begin: MULTIPLE SUBSTITUTION COMMUTES WITH TERM CONSTRUCTORS

mSubstAbsComm : (e : Term) -> 
                (i : Nat) -> (venv : VEnv ctx) ->
                TAbs (msubst e (S i) venv) = msubst (TAbs e) i venv
mSubstAbsComm e _ VNil = Refl
mSubstAbsComm e i (VCons x _ _ venv) = mSubstAbsComm (subst x (S i) e) i venv

  
  
mSubstAppComm : (e1 : Term) -> (e2 : Term) ->
                (i : Nat) -> (venv : VEnv ctx) ->
                TApp (msubst e1 i venv) (msubst e2 i venv) = msubst (TApp e1 e2) i venv
mSubstAppComm e1 e2 i VNil = Refl
mSubstAppComm e1 e2 i (VCons x _ _ venv) = 
  mSubstAppComm (subst x i e1) (subst x i e2) i venv



mSubstRecComm : (e1 : Term) -> (e2 : Term) -> (e3 : Term) ->
                (i : Nat) -> (venv : VEnv ctx) ->
                TRec (msubst e1 i venv) (msubst e2 i venv) (msubst e3 i venv) =
                  msubst (TRec e1 e2 e3) i venv
mSubstRecComm e1 e2 e3 i VNil = Refl
mSubstRecComm e1 e2 e3 i (VCons x _ _ venv) =
  mSubstRecComm (subst x i e1) (subst x i e2) (subst x i e3) i venv



mSubstSuccComm : (e : Term) ->
                 (i : Nat) -> (venv : VEnv ctx) ->
                 TSucc (msubst e i venv) = msubst (TSucc e) i venv
mSubstSuccComm e i VNil = Refl
mSubstSuccComm e i (VCons x _ _ venv) = 
  mSubstSuccComm (subst x i e) i venv



mSubstPredComm : (e : Term) ->
                 (i : Nat) -> (venv : VEnv ctx) ->
                 TPred (msubst e i venv) = msubst (TPred e) i venv
mSubstPredComm e i VNil = Refl
mSubstPredComm e i (VCons x _ _ venv) = 
  mSubstPredComm (subst x i e) i venv



mSubstIfzComm : (e1 : Term) -> (e2 : Term) -> (e3 : Term) ->
                (i : Nat) -> (venv : VEnv ctx) ->
                TIfz (msubst e1 i venv) (msubst e2 i venv) (msubst e3 i venv) =
                  msubst (TIfz e1 e2 e3) i venv
mSubstIfzComm e1 e2 e3 i VNil = Refl
mSubstIfzComm e1 e2 e3 i (VCons x _ _ venv) =
  mSubstIfzComm (subst x i e1) (subst x i e2) (subst x i e3) i venv

-- End: MULTIPLE SUBSTITUTION COMMUTES WITH TERM CONSTRUCTORS
-------------------------------------------------------------
