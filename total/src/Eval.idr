
module Eval

-- Evaluators for terms in the simply-typed
-- lambda calculus. 


import BigStep
import Equivalence
import Determinism
import Progress
import Step
import Subst
import Term


%access export


------------------------------------------------------------
-- Begin: EVALUATOR (FORMALLY) BASED ON SMALL-STEP SEMANTICS

eval : (e : Term [] t) -> (e' : Term [] t ** (Value e', TransStep e e'))
eval e = case progress e of
  Left v           => (e ** (v, TStRefl e))
  Right (e' ** s') => let (e'' ** (v'', s'')) = eval e'
                      in (e'' ** (v'', TStTrans s' s''))

-- End: EVALUATOR (FORMALLY) BASED ON SMALL-STEP SEMANTICS
----------------------------------------------------------



----------------------------------------------------------
-- Begin: EVALUATOR INFORMALLY BASED ON BIG-STEP SEMANTICS

eval' : Term [] t -> Term [] t
eval' (TVar i)       = absurd $ FinZAbsurd i
eval' (TAbs e)       = TAbs e
eval' (TApp e1 e2)   = let (TAbs e1v) = eval' e1
                           e2v        = eval' e2
                       in eval' $ subst e2v FZ e1v
eval' (TRec e e0 e1) = case eval' e of
                            TZero   => eval' e0
                            TSucc n => eval' $ (subst n FZ (subst (TRec n e0 e1) FZ e1))
eval' TZero          = TZero
eval' (TSucc e)      = TSucc (eval' e)
eval' (TPred e)      = case eval' e of 
                            TZero     => TZero
                            TSucc ev' => ev'
eval' (TIfz e1 e2 e3) = case eval' e1 of
                             TZero   => eval' e2
                             TSucc _ => eval' e3                                      

-- End: EVALUATOR INFORMALLY BASED ON BIG-STEP SEMANTICS
--------------------------------------------------------



--------------------------------------------------------
-- Begin: EVALUATOR FORMALLY BASED ON BIG-STEP SEMANTICS

evalBigStep : (e : Term [] t) -> (e' : Term [] t ** (Value e', BigStep e e'))
evalBigStep (TVar i)     = absurd $ FinZAbsurd i
evalBigStep (TAbs x)     = (TAbs x ** (VAbs, BStValue VAbs))
evalBigStep (TApp x y)   = case evalBigStep x of
  (ex ** (VZero  , bStx))   impossible
  (ex ** (VSucc _, bStx))   impossible
  (TAbs ex ** (VAbs, bStx)) => let (ey ** (_ , bSty)) = evalBigStep y
                                   (er ** (vr, bStr)) = evalBigStep (subst ey FZ ex)
                               in (er ** (vr, BStApp bStx bSty bStr))
evalBigStep (TRec x y z) = case evalBigStep x of
  (TZero    ** (_, bStx)) => let (ey ** (vy, bSty)) = evalBigStep y
                             in (ey ** (vy, BStRecZero bStx bSty))
  (TSucc ex ** (_, bStx)) => let (es ** (vs, bSts)) = evalBigStep (subst ex FZ (subst (TRec ex y z) FZ z))
                             in (es ** (vs, BStRecSucc bStx bSts))
evalBigStep TZero        = (TZero ** (VZero, BStValue VZero))
evalBigStep (TSucc x)    = let (ex ** (vx, bStx)) = evalBigStep x
                           in (TSucc ex ** (VSucc vx, BStSucc bStx))
evalBigStep (TPred x)    = case evalBigStep x of
  (TZero    ** (_, bStx)) => (TZero ** (VZero, BStPredZero bStx))
  (TSucc ex ** (VSucc vx, bStx)) => (ex ** (vx, BStPredSucc bStx))
evalBigStep (TIfz x y z) = case evalBigStep x of
  (TZero    ** (_, bStx)) => let (ey ** (vy, bSty)) = evalBigStep y
                             in (ey ** (vy, BStIfzZero bStx bSty))
  (TSucc ex ** (VSucc vx, bStx)) => let (ez ** (vz, bStz)) = evalBigStep z
                                    in (ez ** (vz, BStIfzSucc bStx bStz))

-- End: EVALUATOR FORMALLY BASED ON BIG-STEP SEMANTICS
------------------------------------------------------



-----------------------------------
-- Begin: EQUIVALENCE OF EVALUATORS

total equivEval : (eval e1) = (e2 ** (v2, tst2)) ->
                  (evalBigStep e1) = (e3 ** (v3, bSt3)) ->
                  e2 = e3                                     
equivEval {v2 = v2} {tst2 = tst2} {bSt3 = bSt3} _ _ = 
  let (tst3, v3) = bigStepToTransStep bSt3
  in transStepDeterministic v2 tst2 v3 tst3

-- End: EQUIVALENCE OF EVALUATORS
---------------------------------



--------------------------------------------------
-- Begin: ENVIRONMENT-BASED/DENOTATIONAL EVALUATOR

total denoteType : Ty -> Type
denoteType TyNat         = Nat
denoteType (TyFun t1 t2) = denoteType t1 -> denoteType t2


data Env : Context n -> Type where
  ENil  : Env []
  ECons : denoteType t -> Env ctx -> Env (t::ctx)


total lookup : {ctx : Context n} -> 
               (i : Fin n) -> Env ctx -> denoteType (index i ctx)
lookup FZ      (ECons x _)    = x
lookup (FS i') (ECons _ env') = lookup i' env'


total primRec : Nat -> t -> (Nat -> t -> t) -> t
primRec Z     e0 e1 = e0
primRec (S n) e0 e1 = e1 n (primRec n e0 e1) 


total evalEnv' : Env ctx -> Term ctx t -> denoteType t
evalEnv' env (TVar i {prf}) = rewrite (sym prf) in lookup i env
evalEnv' env (TAbs e)       = \x => evalEnv' (ECons x env) e 
evalEnv' env (TApp e1 e2)   = (evalEnv' env e1) (evalEnv' env e2)
evalEnv' env (TRec e e0 e1) = let e'  = evalEnv' env e
                                  e0' = evalEnv' env e0
                                  e1' = \n => \x => (evalEnv' (ECons x (ECons n env)) e1)
                              in primRec e' e0' e1'
evalEnv' env TZero          = Z
evalEnv' env (TSucc e)      = S (evalEnv' env e)
evalEnv' env (TPred e)      = case evalEnv' env e of
                                   Z   => Z
                                   S n => n
evalEnv' env (TIfz e1 e2 e3) = case evalEnv' env e1 of
                                    Z   => evalEnv' env e2
                                    S _ => evalEnv' env e3


total evalEnv : Term [] TyNat -> Nat
evalEnv = evalEnv' ENil

-- End: ENVIRONMENT-BASED/DENOTATIONAL EVALUATOR
------------------------------------------------
