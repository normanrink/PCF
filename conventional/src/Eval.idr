
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
eval' (TVar _)     impossible
eval' (TAbs e)     = TAbs e
eval' (TApp e1 e2) = let (TAbs e1v) = eval' e1
                         e2v        = eval' e2
                     in eval' $ subst e2v First e1v
eval' (TFix e)     = let (TAbs ev) = eval' e
                        in eval' $ subst (TFix (TAbs ev)) First ev
eval' TZero        = TZero
eval' (TSucc e)    = TSucc (eval' e)
eval' (TPred e)    = case eval' e of 
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
evalBigStep (TVar _)   impossible
evalBigStep (TAbs x)   = (TAbs x ** (VAbs, BStValue VAbs))
evalBigStep (TApp x y) = case evalBigStep x of
  (_ ** (VZero, _))         impossible
  (_ ** (VSucc _, _))       impossible
  (TAbs ex ** (VAbs, bStx)) => let (ey ** (_ , bSty)) = evalBigStep y
                                   (er ** (vr, bStr)) = evalBigStep (subst ey First ex)
                               in (er ** (vr, BStApp bStx bSty bStr))
evalBigStep (TFix x)   = case evalBigStep x of
  (_ ** (VZero, _))         impossible
  (_ ** (VSucc _, _))       impossible
  (TAbs ex ** (VAbs, bStx)) => let (er ** (vr, bStr)) = evalBigStep (subst (TFix (TAbs ex)) First ex)
                               in (er ** (vr, BStFix bStx bStr))
evalBigStep TZero      = (TZero ** (VZero, BStValue VZero))
evalBigStep (TSucc x)  = let (ex ** (vx, bStx)) = evalBigStep x
                         in (TSucc ex ** (VSucc vx, BStSucc bStx))
evalBigStep (TPred x)  = case evalBigStep x of
  (TZero    ** (_,        bStx)) => (TZero ** (VZero, BStPredZero bStx))
  (TSucc ex ** (VSucc vx, bStx)) => (ex    ** (vx, BStPredSucc bStx))
  (_        ** (VAbs, _))        impossible
evalBigStep (TIfz x y z) = case evalBigStep x of
  (TZero    ** (_,        bStx)) => let (ey ** (vy, bSty)) = evalBigStep y
                                    in (ey ** (vy, BStIfzZero bStx bSty))
  (TSucc ex ** (VSucc vx, bStx)) => let (ez ** (vz, bStz)) = evalBigStep z
                                    in (ez ** (vz, BStIfzSucc bStx bStz))
  (_ ** (VAbs, _))               impossible

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

