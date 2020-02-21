
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

-- End: VALUE <=> IRREDUCIBLE
-----------------------------



------------------------------------------
-- Begin: DIVERGENCE OF TERM 'Subst.omega'

-- Term 'omega' steps to itself in one step:
stepOmega : Step Subst.omega Subst.omega
stepOmega = let st = StFixBeta {t=TVar {ctx=[TyNat]} First}
            in replace {P = \x => Step Subst.omega x} substOmega st


-- That 'omega' steps to itself under the reflexive,
-- transitive closure of 'Step' is trivial:
transStepOmega : TransStep Subst.omega Subst.omega
transStepOmega = TStRefl _


-- Term 'omega' steps to nothing but itself:
-- (This could also be derived as a consequence of determinism of 'Step'.)
stepOmegaOnly : (e : Term [] TyNat) -> Step Subst.omega e -> e = Subst.omega            
stepOmegaOnly (TFix _) (StFix st) = absurd $ valueIrreducible (TAbs $ TVar First) VAbs st
stepOmegaOnly (subst (TFix (TAbs (TVar First))) First (TVar First)) StFixBeta = substOmega


-- To extend the previous result 'stepOmegaOnly' to the transitive closure
-- of the 'Step' relation, an indexed version of 'TransStep' is needed:
data TransStepN : Nat -> Term [] t -> Term [] t -> Type where
   TStNRefl   : (e : Term [] t) -> TransStepN Z e e
   TStNTrans  : {e : Term [] t} -> {e' : Term [] t} -> {e'' : Term [] t} ->
                Step e e' -> TransStepN n e' e'' -> TransStepN (S n) e e''


transStepFromN : TransStepN n e1 e2 -> TransStep e1 e2
transStepFromN (TStNRefl e1)       = TStRefl e1
transStepFromN (TStNTrans st tstn) = TStTrans st (transStepFromN tstn)


transStepToN : TransStep e1 e2 -> (n : Nat ** TransStepN n e1 e2)
transStepToN (TStRefl e1)      = (Z ** TStNRefl e1)
transStepToN (TStTrans st tst) = let (m ** tstn) = transStepToN tst
                                 in ((S m) ** TStNTrans st tstn)


transStepNOmegaOnly : (e : Term [] TyNat) -> (n : Nat) -> 
                      TransStepN n Subst.omega e -> e = Subst.omega
transStepNOmegaOnly _ Z     (TStNRefl _)        = Refl
transStepNOmegaOnly e (S k) (TStNTrans st tstk) = 
  let eq    = stepOmegaOnly _ st 
      tstk' = replace {P = \x => TransStepN k x e} eq tstk
  in transStepNOmegaOnly _ k tstk'


-- Finally, the fact that 'omega' only steps to itself is proven
-- by appealing to the indexed version of the transitive closure:
-- (An induction argument analogous to the one in 'transStepNOmegaOnly'
-- is not accepted by Idris' totality checker. Induction would proceed on
-- the structure of the 'TransStep omega e' argument, and the induction
-- hypothesis would be applied to the second argument of the 'TStTrans'
-- constructor, which would again have the type 'TransStep omega e' but
-- only after rewriting with the equation obtained from 'stepOmegaOnly'.)
transStepOmegaOnly : (e : Term [] TyNat) -> TransStep Subst.omega e -> e = Subst.omega
transStepOmegaOnly e tst = let (n ** tstn) = transStepToN tst
                           in transStepNOmegaOnly e n tstn


divergenceOmega : TransStep Subst.omega e -> (Value e -> Void)
divergenceOmega {e} tst v = let eq = transStepOmegaOnly e tst
                            in case (replace {P = \x => Value x} eq v) of
                               VZero     impossible
                               (VSucc _) impossible
                               VAbs      impossible

-- End: DIVERGENCE OF TERM 'Subst.omega'
----------------------------------------
