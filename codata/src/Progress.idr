
module Progress

-- Progress theorem for the 'Step' relation.


import Step
import Subst
import Term


%default total
%access export


-------------------------------------
-- Begin: PROGRESS (AND PRESERVATION)

-- Function 'progress' proves the usual progress lemma.
--
-- Progress: a closed, well-typed term is either a value
--           or it can take a step in the reduction relation.
--
-- Preservation: after reducing a term of type 't' by one
--               step, the resulting term is again of type 't'.
--               
--   ***  Note that preservation is already built into     ***
--   ***  the relation 'Step' as defined in module "Step". ***
--
progress : (e : Term [] t) -> Either (Value e) (e' : Term [] t ** (Step e e'))
-- Expressions that are variables cannot occur in an empty context:
-- (In other words, variables are not closed expressions.)
progress (TVar _) impossible 
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
                                  TAbs f => let e'' = subst e2 First f
                                            in Right (e'' ** StBeta v2)
-- When the fix-point operator is applied to a value,
-- that value is necessarily an abstraction; hence
-- the function 'subst' is used in reducing 'Fix _':
progress (TFix e) = case progress e of
  Right (e' ** st) => Right (TFix e' ** StFix st)
  Left v           =>
    case e of
         TAbs f => let e'' = subst (TFix (TAbs f)) First f
                   in Right (e'' ** StFixBeta)
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
                           VAbs     impossible
                           VZero    => Right (e2 ** StIfzZero)
                           VSucc v' => Right (e3 ** StIfzSucc v')

-- End: PROGRESS (AND PRESERVATION)
-----------------------------------



-------------------------------
-- Begin: VALUE <=> IRREDUCIBLE

-- Establish that values cannot be further reduced under 'Step'.
valueIrreducible : (e : Term [] t) -> 
                   Value e -> 
                   {e' : Term [] t} -> Step e e' -> Void
valueIrreducible TZero     VZero     _           impossible
valueIrreducible (TSucc n) (VSucc v) (StSucc st) = valueIrreducible n v st
valueIrreducible (TAbs _)  VAbs      _           impossible


-- Establish that irreducible expressions (under 'Step') are values:
irreducibleValue : (e : Term [] t) -> 
                   ({e' : Term [] t} -> Step e e' -> Void) ->
                   Value e                  
irreducibleValue e notStep = case progress e of 
  Right (_ ** st) => absurd $ notStep st 
  Left v          => v


coTransStepValueIrreducible : CoTransStep e1 e2 -> Value e1 -> e1 = e2
coTransStepValueIrreducible (CoTStRefl e1)       v = Refl
coTransStepValueIrreducible (CoTStTrans st ctst) v = absurd $ valueIrreducible _ v st

-- End: VALUE <=> IRREDUCIBLE
-----------------------------



