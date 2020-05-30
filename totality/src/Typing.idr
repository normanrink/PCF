
module Typing

-- Typing judgement for the simply-typed lambda
-- calculus with 
--   (1) natural numbers as the only base type, and
--   (2) general recursion.


import Term


%default total
%access public export



---------------------------------------------------
-- Begin: TYPES IN THE SIMPLY-TYPED LAMBDA CALCULUS

-- Data type 'Ty' represents the types in the
-- simply-typed lambda calculus:
--   (1) Base type 'TyNat' of natural numbers.
--   (2) Type constructor 'TyFun' for forming
--       function types.
data Ty = TyNat | TyFun Ty Ty


-- Simplified syntax for function types:
infixr 10 :->:
(:->:) : Ty -> Ty -> Ty
(:->:) t1 t2 = TyFun t1 t2

-- End: TYPES IN THE SIMPLY-TYPED LAMBDA CALCULUS
-------------------------------------------------




---------------------------------------------------------
-- Begin: CONTEXT FOR TYPING TERMS IN THE LAMBDA CALCULUS

Context : Type
Context = List Ty

-- End: CONTEXT FOR TYPING TERMS IN THE LAMBDA CALCULUS
-------------------------------------------------------




--------------------------
-- Begin: TYPING JUDGEMENT

data Typing : Context -> Term -> Ty -> Type where
  TyVar  : (prf : index' i ctx = Just t) -> 
           Typing ctx (TVar i) t
  --
  TyAbs  : (s : Ty) ->
           Typing (s::ctx) e t ->
           Typing ctx (TAbs e) (s :->: t)
  --
  TyApp  : Typing ctx e1 (s :->: t) -> Typing ctx e2 s ->
           Typing ctx (TApp e1 e2) t
  --
  TyRec  : Typing ctx e1 TyNat -> Typing ctx e2 t -> 
           Typing ctx e3 (TyNat :->: t :->: t) ->
           Typing ctx (TRec e1 e2 e3) t
  --
  TyZero : Typing ctx TZero TyNat
  --
  TySucc : Typing ctx e TyNat ->
           Typing ctx (TSucc e) TyNat
  --
  TyPred : Typing ctx e TyNat ->
           Typing ctx (TPred e) TyNat
  --
  TyIfz  : Typing ctx e1 TyNat -> Typing ctx e2 t -> Typing ctx e3 t ->
           Typing ctx (TIfz e1 e2 e3) t


type : Typing ctx e t -> Ty
type {t} _ = t

-- End: TYPING JUDGEMENT
------------------------




-------------------------
-- Begin: CANONICAL FORMS

canonicalNat : (e : Term) ->
               Typing ctx e TyNat ->
               Value e ->
               Either (e = TZero) (e' : Term ** (Value e', e = TSucc e'))
canonicalNat (TVar i) (TyVar prf) v impossible
canonicalNat (TApp e1 e2) (TyApp ty1 ty2) v impossible
canonicalNat (TRec e1 e2 e3) (TyRec ty1 ty2 ty3) v impossible
canonicalNat TZero TyZero v = Left Refl
canonicalNat (TSucc e) (TySucc ty) (VSucc v) = 
  let ih = canonicalNat e ty v
  in case ih of
    (Left eq) => let eq' = cong {f = TSucc} eq
                 in Right (TZero ** (VZero, eq'))
    (Right (e1 ** (v1, eq))) => let e'  = TSucc e1
                                    v'  = VSucc v1
                                    eq' = cong {f = TSucc} eq
                                in Right (e' ** (v', eq'))
canonicalNat (TPred e) (TyPred ty) v impossible
canonicalNat (TIfz e1 e2 e3) (TyIfz ty1 ty2 ty3) v impossible


canonicalFun : (e : Term) ->
               Typing ctx e (s :->: t) ->
               Value e ->
               (e' : Term ** (e = TAbs e'))
canonicalFun (TVar i) (TyVar prf) v impossible
canonicalFun (TAbs e) (TyAbs s ty) v = (e ** Refl)
canonicalFun (TApp e1 e2) (TyApp ty1 ty2) v impossible
canonicalFun (TRec e1 e2 e3) (TyRec ty1 ty2 ty3) v impossible
canonicalFun (TIfz e1 e2 e3) (TyIfz ty1 ty2 ty3) v impossible

-- End: CANONICAL FORMS
-----------------------
