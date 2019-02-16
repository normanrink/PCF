
module Progress

-- Pseudo-progress theorem for the 'Step' relation
-- in the untyped lambda calculus.


import Step
import Subst
import Term


%access export


-------------------------
-- Begin: PSEUDO-PROGRESS

-- Function 'progress' looks like the usual progress theorem
-- but notice that 'progress' is not a total function.
--
-- (It is therefore not consistent to interpret the
--  definition of the function 'progress' as a proof.)
--
progress : (e : Term 0) -> Either (Value e) (e' : Term 0 ** (Step e e'))
-- Expressions that are variables cannot occur in an empty context:
-- (In other words, variables are not closed expressions.)
progress (TVar i) = absurd $ FinZAbsurd i
-- Abstractions are values already:
progress (TAbs _) = Left VAbs
-- Applications can reduce in three different ways, the most
-- interesting of which occurs when both arguments of 'App'
-- are values already: in this case, the function 'subst'
-- is required:
progress (TApp e1 e2) = case progress e1 of
  Right (e' ** st) => Right (TApp e' e2 ** StApp1 st)
  Left  v1         => 
    case progress e2 of
         Right (e' ** st) => Right (TApp e1 e' ** StApp2 v1 st)
         Left  v2         => case e1 of
                                  TAbs f => let e'' = subst e2 FZ f
                                            in Right (e'' ** StBeta v2)
-- The constant 'Zero' is a value already:
progress TZero = Left VZero
--
progress (TSucc e) = case progress e of
  Right (e' ** st) => Right (TSucc e' ** StSucc st)
  Left  v          => Left (VSucc v)
progress (TPred e) = case progress e of
  Right (e' ** st) => Right (TPred e' ** StPred st)
  Left v           => 
    case e of
         TZero    => Right (TZero ** StPredZero)
         TSucc e' => case v of 
                          VAbs     impossible
                          VZero    impossible
                          VSucc v' => Right (e' ** StPredSucc v')
--  
progress (TIfz e1 e2 e3) = case progress e1 of
  Right (e' ** st) => Right $ (TIfz e' e2 e3 ** StIfz st)
  Left v           => case v of
                           VZero    => Right (e2 ** StIfzZero)
                           VSucc v' => Right (e3 ** StIfzSucc v')

-- End: PSEUDO-PROGRESS
-----------------------

