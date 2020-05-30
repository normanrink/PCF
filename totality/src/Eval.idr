
module Eval

-- Evaluators for terms in the simply-typed
-- lambda calculus. 


import PnP
import Step
import Term
import Typing


%access export



------------------------------------------------------------
-- Begin: EVALUATOR (FORMALLY) BASED ON SMALL-STEP SEMANTICS

eval : (e : Term) -> 
       Typing [] e t ->
       (e' : Term ** (Value e', Typing [] e' t, TransStep e e'))
eval e ty = case progress e ty of
  (Left v) => (e ** (v, ty, TStRefl e))
  (Right (e' ** st)) => let ty' = preservation e ty st
                            (e'' ** (v'', ty'', tst)) = eval e' ty'
                        in (e'' ** (v'', ty'', TStTrans st tst))

-- End: EVALUATOR (FORMALLY) BASED ON SMALL-STEP SEMANTICS
----------------------------------------------------------




--------------------------------------------------
-- Begin: ENVIRONMENT-BASED/DENOTATIONAL EVALUATOR

total denoteType : Ty -> Type
denoteType TyNat         = Nat
denoteType (TyFun t1 t2) = denoteType t1 -> denoteType t2



data Env : Context -> Type where
  ENil  : Env []
  ECons : denoteType t -> Env ctx -> Env (t::ctx)



total lookup : (i : Nat) ->
               (ctx : Context) ->
               index' i ctx = Just t ->
               Env ctx ->
               denoteType t
lookup Z     []       Refl ENil impossible
lookup (S _) []       Refl ENil impossible
lookup Z     (s::ctx) Refl (ECons x env) = x
lookup (S i) (s::ctx) prf  (ECons x env) = lookup i ctx prf env



total primRec : Nat -> t -> (Nat -> t -> t) -> t
primRec Z     e0 e1 = e0
primRec (S n) e0 e1 = e1 n (primRec n e0 e1) 


total evalEnv : Env ctx -> 
                (e : Term) ->
                Typing ctx e t ->
                denoteType t
evalEnv env (TVar i) (TyVar prf) = lookup i _ prf env
evalEnv env (TAbs e) (TyAbs s ty) = \x => evalEnv (ECons x env) e ty
evalEnv env (TApp e1 e2) (TyApp ty1 ty2) = 
  (evalEnv env e1 ty1) (evalEnv env e2 ty2)
evalEnv env (TRec e1 e2 e3) (TyRec ty1 ty2 ty3) = 
  let n    = evalEnv env e1 ty1
      e0   = evalEnv env e2 ty2
      erec = evalEnv env e3 ty3
  in primRec n e0 erec
evalEnv env TZero TyZero = Z
evalEnv env (TSucc e) (TySucc ty) = S $ evalEnv env e ty
evalEnv env (TPred e) (TyPred ty) = 
  case evalEnv env e ty of
       Z     => Z
       (S k) => k
evalEnv env (TIfz e1 e2 e3) (TyIfz ty1 ty2 ty3) = 
  case evalEnv env e1 ty1 of
       Z     => evalEnv env e2 ty2
       (S k) => evalEnv env e3 ty3

-- End: ENVIRONMENT-BASED/DENOTATIONAL EVALUATOR
------------------------------------------------
