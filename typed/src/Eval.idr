
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
eval' (TVar i)     = absurd $ FinZAbsurd i
eval' (TAbs e)     = TAbs e
eval' (TApp e1 e2) = let (TAbs e1v) = eval' e1
                         e2v        = eval' e2
                     in eval' $ subst e2v FZ e1v
eval' (TFix e)     = let (TAbs ev) = eval' e
                        in eval' $ subst (TFix (TAbs ev)) FZ ev
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

evalBigStep : (e : Term [] t) -> (e' : Term [] t ** BigStep e e')
evalBigStep (TVar i)   = absurd $ FinZAbsurd i
evalBigStep (TAbs x)   = (TAbs x ** BStValue VAbs)
evalBigStep (TApp x y) = let (TAbs ex ** bStx) = evalBigStep x
                             (ey      ** bSty) = evalBigStep y
                             (er      ** bStr) = evalBigStep (subst ey FZ ex)
                         in (er ** BStApp bStx bSty bStr)
evalBigStep (TFix x)   = let (TAbs ex ** bStx) = evalBigStep x
                             (er      ** bStr) = evalBigStep (subst (TFix (TAbs ex)) FZ ex)
                         in (er ** BStFix bStx bStr)
evalBigStep TZero      = (TZero ** BStValue VZero)
evalBigStep (TSucc x)  = let (ex ** bStx) = evalBigStep x
                         in (TSucc ex ** BStSucc bStx)
evalBigStep (TPred x)  = case evalBigStep x of
  (TZero    ** bStx) => (TZero ** BStPredZero bStx)
  (TSucc ex ** bStx) => (ex    ** BStPredSucc bStx)
evalBigStep (TIfz x y z) = case evalBigStep x of
  (TZero    ** bStx) => let (ey ** bSty) = evalBigStep y
                        in (ey ** BStIfzZero bStx bSty)
  (TSucc ex ** bStx) => let (ez ** bStz) = evalBigStep z
                        in (ez ** BStIfzSucc bStx bStz)

-- End: EVALUATOR FORMALLY BASED ON BIG-STEP SEMANTICS
------------------------------------------------------



-----------------------------------
-- Begin: EQUIVALENCE OF EVALUATORS

total equivEval : (eval e1) = (e2 ** (v2, tst2)) ->
                  (evalBigStep e1) = (e3 ** bSt3) ->
                  e2 = e3                                     
equivEval {v2 = v2} {tst2 = tst2} {bSt3 = bSt3} _ _ = 
  let (tst3, v3) = bigStepToTransStep bSt3
  in transStepDeterministic v2 tst2 v3 tst3

-- End: EQUIVALENCE OF EVALUATORS
---------------------------------

