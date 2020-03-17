
module Determinism



import BigStep
import Progress
import Step
import Subst
import Term
import Equivalence


%default total
%access export


------------------------------------------------------------------------------
-- Begin: DETERMINISM OF INDUCTIVELY DEFINED SMALL-STEP AND BIG-STEP SEMANTICS

stepDeterministic : (Step e1 e2) -> (Step e1 e3) ->
                    e2 = e3
-- case split in the following order: (Step e1 e2), (Step e1 e3)
stepDeterministic {e1 = TApp _ e11} (StApp1 x) (StApp1 y) = 
  cong {f = \e => TApp e e11} $ stepDeterministic x y
--
stepDeterministic (StApp1 x) (StApp2 y z) = absurd $ valueIrreducible _ y x
--  
stepDeterministic (StApp1 x) (StBeta y) = absurd $ valueIrreducible _ VAbs x
--
stepDeterministic (StApp2 x z) (StApp1 y) = absurd $ valueIrreducible _ x y
--
stepDeterministic {e1 = TApp e11 _} (StApp2 x z) (StApp2 y w) = 
  cong {f = \e => TApp e11 e} $ stepDeterministic z w
--  
stepDeterministic (StApp2 x z) (StBeta y) = absurd $ valueIrreducible _ y z
--
stepDeterministic (StBeta x) (StApp2 y z) = absurd $ valueIrreducible _ x z
--
stepDeterministic (StBeta x) (StBeta y) = Refl
--
stepDeterministic (StFix x) (StFix y) = cong $ stepDeterministic x y
--
stepDeterministic (StFix x) StFixBeta = absurd $ valueIrreducible _ VAbs x
--
stepDeterministic StFixBeta StFixBeta = Refl
--
stepDeterministic (StSucc x) (StSucc y) = cong $ stepDeterministic x y
--
stepDeterministic (StPred x) (StPred y) = cong $ stepDeterministic x y
--
stepDeterministic (StPred x) StPredZero = absurd $ valueIrreducible _ VZero x
--
stepDeterministic (StPred x) (StPredSucc y) = absurd $ valueIrreducible _ (VSucc y) x
--
stepDeterministic StPredZero (StPred x) = absurd $ valueIrreducible _ VZero x
--
stepDeterministic StPredZero StPredZero = Refl
--
stepDeterministic (StPredSucc x) (StPred y) = absurd $ valueIrreducible _ (VSucc x) y
--
stepDeterministic (StPredSucc x) (StPredSucc y) = Refl
--
stepDeterministic {e1 = TIfz _ e12 e13} (StIfz x) (StIfz y) = 
  cong {f = \e => TIfz e e12 e13} $ stepDeterministic x y
--  
stepDeterministic (StIfz x) StIfzZero = absurd $ valueIrreducible _ VZero x
--
stepDeterministic (StIfz x) (StIfzSucc y) = absurd $ valueIrreducible _ (VSucc y) x
--
stepDeterministic StIfzZero (StIfz x) = absurd $ valueIrreducible _ VZero x
--
stepDeterministic StIfzZero StIfzZero = Refl
--
stepDeterministic (StIfzSucc x) (StIfz y) = absurd $ valueIrreducible _ (VSucc x) y
--
stepDeterministic (StIfzSucc x) (StIfzSucc y) = Refl



transStepDeterministic : (v2 : Value e2) -> (TransStep e1 e2) ->
                         (v3 : Value e3) -> (TransStep e1 e3) ->
                         e2 = e3
transStepDeterministic v2 (TStRefl e3) v3 (TStRefl e3) = Refl
--
transStepDeterministic v2 (TStRefl e2) v3 (TStTrans x y) = 
  absurd $ valueIrreducible e2 v2 x
--
transStepDeterministic v2 (TStTrans x z) v3 (TStRefl e3) = 
  absurd $ valueIrreducible e3 v3 x
--
transStepDeterministic {e2 = e2} v2 (TStTrans x z) v3 (TStTrans y w) =
  let eq = stepDeterministic x y
      z' = replace {P = \x => x} (cong {f = \e => TransStep e e2} eq) z
  in transStepDeterministic v2 z' v3 w



-- The following proof of the determinism of 'BigStep'
-- relies on the equivalence of 'Step' and 'BigStep'.
bigStepDeterministic' : (BigStep e1 e2) ->
                        (BigStep e1 e3) ->
                        e2 = e3
bigStepDeterministic' x y = 
  let (tst2, v2) = bigStepToTransStep x
      (tst3, v3) = bigStepToTransStep y
  in transStepDeterministic v2 tst2 v3 tst3



injectiveAbs : (TAbs e1 = TAbs e2) -> e1 = e2
injectiveAbs Refl = Refl


injectiveSucc : (TSucc e1 = TSucc e2) -> e1 = e2
injectiveSucc Refl = Refl


zeroNotSucc : (TZero = TSucc _) -> Void
zeroNotSucc Refl impossible


pairEq : a = b -> c = d -> (a, c) = (b, d)
pairEq Refl Refl = Refl


valueBigStepEq : Value e1 -> BigStep e1 e2 -> e1 = e2
valueBigStepEq VZero (BStValue _)     = Refl
valueBigStepEq (VSucc x) (BStValue _) = Refl
valueBigStepEq (VSucc x) (BStSucc y)  = cong $ valueBigStepEq x y
valueBigStepEq VAbs (BStValue _)      = Refl


bigStepDeterministic : (BigStep e1 e2) -> (BigStep e1 e3) ->
                       e2 = e3
-- case split in the following order: (BigStep e1 e2), (BigStep e1 e3)
bigStepDeterministic (BStValue _) (BStValue _) = Refl
--
bigStepDeterministic (BStValue _) (BStApp z w t) impossible
--
bigStepDeterministic (BStValue _) (BStFix y z) impossible
--
bigStepDeterministic (BStValue v2) (BStSucc x) = case v2 of
  VAbs      impossible
  VZero     impossible
  VSucc v2' => cong $ valueBigStepEq v2' x
--  
bigStepDeterministic (BStValue _) (BStPredZero y) impossible
--
bigStepDeterministic (BStValue _) (BStPredSucc x) impossible
--
bigStepDeterministic (BStValue _) (BStIfzZero z w) impossible
--
bigStepDeterministic (BStValue _) (BStIfzSucc w s) impossible
--
bigStepDeterministic (BStApp w t u) (BStValue _) impossible
--
bigStepDeterministic {e2 = e2} (BStApp w t u) (BStApp z s v) = 
  let ih1 = injectiveAbs $ bigStepDeterministic w z
      ih2 = bigStepDeterministic t s
      peq = pairEq ih1 ih2
      u'  = replace {P = \x => BigStep (subst (snd x) First (fst x)) e2} peq u
  in bigStepDeterministic u' v
--
bigStepDeterministic (BStFix z w) (BStValue v3) impossible
--
bigStepDeterministic {e2 = e2} (BStFix z w) (BStFix y s) = 
  let ih = injectiveAbs $ bigStepDeterministic z y
      w' = replace {P = \x => BigStep (subst (TFix (TAbs x)) First x) e2} ih w
  in bigStepDeterministic w' s
--
bigStepDeterministic (BStSucc x) (BStValue v3) = case v3 of
  VAbs      impossible
  VZero     impossible
  VSucc v3' => cong . sym $ valueBigStepEq v3' x
--
bigStepDeterministic (BStSucc x) (BStSucc y) = cong $ bigStepDeterministic x y
--
bigStepDeterministic (BStPredZero z) (BStValue _) impossible
--
bigStepDeterministic (BStPredZero z) (BStPredZero y) = Refl
--
bigStepDeterministic (BStPredZero z) (BStPredSucc x) = 
  let ih = bigStepDeterministic z x
  in absurd $ zeroNotSucc ih
--
bigStepDeterministic (BStPredSucc x) (BStValue _) impossible
--
bigStepDeterministic (BStPredSucc x) (BStPredZero z) = 
  let ih = bigStepDeterministic x z
  in absurd . zeroNotSucc $ sym ih
--
bigStepDeterministic (BStPredSucc x) (BStPredSucc y) = 
  injectiveSucc $ bigStepDeterministic x y
--
bigStepDeterministic (BStIfzZero w s) (BStValue _) impossible
--
bigStepDeterministic (BStIfzZero w s) (BStIfzZero y z) = bigStepDeterministic s z
--
bigStepDeterministic (BStIfzZero w s) (BStIfzSucc z t) = 
  let ih = bigStepDeterministic w z
  in absurd $ zeroNotSucc ih
--
bigStepDeterministic (BStIfzSucc s t) (BStValue _) impossible
--
bigStepDeterministic (BStIfzSucc s t) (BStIfzZero y z) = 
  let ih = bigStepDeterministic s y
  in absurd . zeroNotSucc $ sym ih
--
bigStepDeterministic (BStIfzSucc s t) (BStIfzSucc z w) = bigStepDeterministic t w

-- End: DETERMINISM OF INDUCTIVELY DEFINED SMALL-STEP AND BIG-STEP SEMANTICS
----------------------------------------------------------------------------



----------------------------------------------------------------------------------
-- Begin: VERY RESTRICTED FROM OF DETERMINISM FOR CO-INDUCTIVELY DEFINED SEMANTICS

-- The coinductive relation 'CoBigStep' is not deterministic as, for example,
-- the term 'omega' can evaluate to anything. However, the following form of
-- determinism holds for terminating terms:
-- (cf. Lemma 35 in "Coinductive big-step operational semantics" by 
-- X. Leroy and H. Grall)
coBigStepDeterministic' : BigStep e1 e2 -> CoBigStep e1 e3 -> e2 = e3
--
coBigStepDeterministic' (BStValue v) cbst = coBigStepValueIrreducible cbst v
--
coBigStepDeterministic' (BStApp bst1 bst2 bst3) cbst = case cbst of
  (CoBStValue v)               impossible
  (CoBStApp cbst1 cbst2 cbst3) =>
    case coBigStepDeterministic' bst1 cbst1 of
         Refl => case coBigStepDeterministic' bst2 cbst2 of
                      Refl => case coBigStepDeterministic' bst3 cbst3 of
                                   Refl => Refl
--
coBigStepDeterministic' (BStFix bst1 bst2) cbst = case cbst of
  (CoBStValue v)         impossible
  (CoBStFix cbst1 cbst2) => 
    case coBigStepDeterministic' bst1 cbst1 of
         Refl => case coBigStepDeterministic' bst2 cbst2 of
                      Refl => Refl
--
coBigStepDeterministic' (BStSucc bst) cbst = case cbst of
  (CoBStValue (VSucc v)) => cong . sym $ bigStepValueIrreducible bst v
  (CoBStSucc cbst)       => case coBigStepDeterministic' bst cbst of
                                 Refl => Refl
--
coBigStepDeterministic' (BStPredZero bst) cbst = case cbst of 
  (CoBStValue v)       impossible
  (CoBStPredZero cbst) => case coBigStepDeterministic' bst cbst of
                               Refl => Refl
  (CoBStPredSucc cbst) => case coBigStepDeterministic' bst cbst of
                               Refl impossible
--
coBigStepDeterministic' (BStPredSucc bst) cbst = case cbst of
  (CoBStValue v)       impossible
  (CoBStPredZero cbst) => case coBigStepDeterministic' bst cbst of
                               Refl impossible
  (CoBStPredSucc cbst) => case coBigStepDeterministic' bst cbst of
                               Refl => Refl
--
coBigStepDeterministic' (BStIfzZero bst1 bst2) cbst = case cbst of
  (CoBStValue v)             impossible
  (CoBStIfzZero cbst1 cbst2) => coBigStepDeterministic' bst2 cbst2
  (CoBStIfzSucc cbst1 cbst2) => case coBigStepDeterministic' bst1 cbst1 of
                                     Refl impossible
--
coBigStepDeterministic' (BStIfzSucc bst1 bst2) cbst = case cbst of
  (CoBStValue v)             impossible
  (CoBStIfzZero cbst1 cbst2) => case coBigStepDeterministic' bst1 cbst1 of
                                     Refl impossible
  (CoBStIfzSucc cbst1 cbst2) => coBigStepDeterministic' bst2 cbst2


-- An analogous statement holds for terminating terms and the coinductive 
-- relation 'CoTransStep', which is generally not deterministic either:
coTransStepDeterministic' : Value e2 -> TransStep e1 e2 -> 
                            Value e3 -> CoTransStep e1 e3 -> 
                            e2 = e3
coTransStepDeterministic' v2 (TStRefl e1)       v3 (CoTStRefl e1)    = Refl
coTransStepDeterministic' v2 (TStRefl e1)       v3 (CoTStTrans st _) = 
  absurd $ valueIrreducible _ v2 st
coTransStepDeterministic' v2 (TStTrans st tst)  v3 (CoTStRefl e1)    = 
  absurd $ valueIrreducible _ v3 st
coTransStepDeterministic' v2 (TStTrans st1 tst) v3 (CoTStTrans st2 ctst) =
  case stepDeterministic st1 st2 of
       Refl => coTransStepDeterministic' v2 tst v3 ctst


-- The following statement can also be seen as a restricted
-- from of determinism of the 'CoTransStep' relation given
-- that 'TransStep' terminates:
coTransStepExtends : TransStep e1 e2 -> Value e2 -> 
                     CoTransStep e1 e3 -> CoTransStep e3 e2
coTransStepExtends (TStRefl e2)       v (CoTStRefl e2)       = CoTStRefl e2
coTransStepExtends (TStRefl e2)       v (CoTStTrans st ctst) = 
  absurd $ valueIrreducible _ v st
coTransStepExtends (TStTrans st tst)  v (CoTStRefl e1)   =
  CoTStTrans st $ transToCoTrans tst
coTransStepExtends (TStTrans st1 tst) v (CoTStTrans st2 ctst) = 
  case stepDeterministic st1 st2 of
       Refl => coTransStepExtends tst v ctst


coTransStepExtends' : TransStep e1 e2 -> Value e2 -> 
                      CoTransStep e1 e3 -> CoTransStep e1 e2
coTransStepExtends' tst v ctst = coTransStepTransitive ctst $ coTransStepExtends tst v ctst


-- Another result that relies on 
--   (a) irreducibility of values and
--   (b) determinism of the 'Step' relation:
coTransStepInterpolates : CoTransStep e1 e3 -> Value e3 -> Step e1 e2 -> CoTransStep e2 e3
coTransStepInterpolates (CoTStRefl e1)        v st = absurd $ valueIrreducible _ v st
coTransStepInterpolates (CoTStTrans st' ctst) v st = 
  let eq = stepDeterministic st st'
  in rewrite eq in ctst

-- End: VERY RESTRICTED FROM OF DETERMINISM FOR CO-INDUCTIVELY DEFINED SEMANTICS
--------------------------------------------------------------------------------



-----------------------------------------------------------
-- Begin: DIVERGENCE OF TERM 'Subst.omega' UNDER SMALL-STEP

-- Term 'omega' steps to itself in one step:
stepOmega : Step Subst.omega Subst.omega
stepOmega = StFixBeta


-- That 'omega' steps to itself under the reflexive,
-- transitive closure of 'Step' is trivial:
transStepOmega : TransStep Subst.omega Subst.omega
transStepOmega = TStRefl _


-- By determinism of 'Step', the term 'omega' steps to nothing but itself:
stepOmegaOnly : Step Subst.omega e -> e = Subst.omega            
stepOmegaOnly st = stepDeterministic st stepOmega


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


transStepNOmegaOnly : (n : Nat) -> TransStepN n Subst.omega e -> e = Subst.omega
transStepNOmegaOnly     Z     (TStNRefl _)        = Refl
transStepNOmegaOnly {e} (S k) (TStNTrans st tstk) = 
  let eq    = stepOmegaOnly st 
      tstk' = replace {P = \x => TransStepN k x e} eq tstk
  in transStepNOmegaOnly k tstk'


-- Finally, the fact that 'omega' only steps to itself is proven
-- by appealing to the indexed version of the transitive closure:
-- (An induction argument analogous to the one in 'transStepNOmegaOnly'
-- is not accepted by Idris' totality checker. Induction would proceed on
-- the structure of the 'TransStep omega e' argument, and the induction
-- hypothesis would be applied to the second argument of the 'TStTrans'
-- constructor, which would again have the type 'TransStep omega e' but
-- only after rewriting with the equation obtained from 'stepOmegaOnly'.)
transStepOmegaOnly : TransStep Subst.omega e -> e = Subst.omega
transStepOmegaOnly tst = let (n ** tstn) = transStepToN tst
                         in transStepNOmegaOnly n tstn


transStepDivergenceOmega : TransStep Subst.omega e -> (Value e -> Void)
transStepDivergenceOmega tst v = let eq = transStepOmegaOnly tst
                                 in case (replace {P = \x => Value x} eq v) of
                                          VZero     impossible
                                          (VSucc _) impossible
                                          VAbs      impossible


-- Instead of diverging, the term 'omega' can evaluate to anything
-- under the coinductive relation 'CoTransStep'. Hence evaluation
-- under 'CoTransStep' is not deterministic:
coTransStepOmegaAny : CoTransStep Subst.omega e
coTransStepOmegaAny = CoTStTrans StFixBeta (coTransStepOmegaAny)

-- End: DIVERGENCE OF TERM 'Subst.omega' UNDER SMALL-STEP
---------------------------------------------------------



---------------------------------------------------------
-- Begin: DIVERGENCE OF TERM 'Subst.omega' UNDER BIG-STEP

-- The following straightforward approach to proving
-- that 'omega' diverges does not pass Idris' totality
-- checker because of the rewriting of 'bst' in the
-- induction step:
--
-- divergenceOmega : BigStep Subst.omega e -> Void
-- divergenceOmega {e = _} (BStValue v) = case v of
--                                             VZero     impossible
--                                             (VSucc _) impossible
--                                             VAbs      impossible
-- divergenceOmega {e = e} (BStFix (BStValue v) bst) =
--   let bst' = replace {P = \x => BigStep x e} substOmega bst
--   in divergenceOmega bst'


-- To prove that 'omega' diverges under big-step semantics,
-- an indexed version of the 'BigStep' relation is introduced:
data BigStepN : Nat -> Term [] t -> (y: Term [] t) -> Type where
  BStValueN    : (v : Value e) -> BigStepN Z e e
  --
  BStAppN      : BigStepN k e1 (TAbs e1') ->
                 BigStepN m e2 e2' ->
                 BigStepN n (subst e2' First e1') e ->
                 BigStepN (S $ k+m+n) (TApp e1 e2) e
  --              
  BStFixN      : BigStepN m e (TAbs e') ->
                 BigStepN n (subst (TFix (TAbs e')) First e') e'' ->
                 BigStepN (S $ m+n) (TFix e) e''
  --           
  BStSuccN     : BigStepN n e e' ->
                 BigStepN (S n) (TSucc e) (TSucc e')
  --            
  BStPredZeroN : BigStepN n e TZero ->
                 BigStepN (S n) (TPred e) TZero
  --                
  BStPredSuccN : BigStepN n e (TSucc e') ->
                 BigStepN (S n) (TPred e) e'
  --                
  BStIfzZeroN  : BigStepN m e1 TZero ->
                 BigStepN n e2 e ->
                 BigStepN (S $ m+n) (TIfz e1 e2 _) e
  --              
  BStIfzSuccN  : BigStepN m e1 (TSucc _) ->
                 BigStepN n e3 e ->
                 BigStepN (S $ m+n) (TIfz e1 _ e3) e


bigStepToN : BigStep e1 e2 -> (n : Nat ** BigStepN n e1 e2)
bigStepToN (BStValue v) = (Z ** BStValueN v)
--
bigStepToN (BStApp bst1 bst2 bst3) = let (n1 ** bstn1) = bigStepToN bst1
                                         (n2 ** bstn2) = bigStepToN bst2
                                         (n3 ** bstn3) = bigStepToN bst3
                                     in ((S $ n1+n2+n3) ** BStAppN bstn1 bstn2 bstn3)
--                                     
bigStepToN (BStFix bst1 bst2) = let (n1 ** bstn1) = bigStepToN bst1
                                    (n2 ** bstn2) = bigStepToN bst2
                                in ((S $ n1+n2) ** BStFixN bstn1 bstn2) 
--                            
bigStepToN (BStSucc bst) = let (n ** bstn) = bigStepToN bst
                           in ((S n) ** BStSuccN bstn)
--                            
bigStepToN (BStPredZero bst) = let (n ** bstn) = bigStepToN bst
                               in ((S n) ** BStPredZeroN bstn)
--                               
bigStepToN (BStPredSucc bst) = let (n ** bstn) = bigStepToN bst
                               in ((S n) ** BStPredSuccN bstn)
--
bigStepToN (BStIfzZero bst1 bst2) = let (n1 ** bstn1) = bigStepToN bst1
                                        (n2 ** bstn2) = bigStepToN bst2
                                    in ((S $ n1+n2) ** BStIfzZeroN bstn1 bstn2) 
--                            
bigStepToN (BStIfzSucc bst1 bst2) = let (n1 ** bstn1) = bigStepToN bst1
                                        (n2 ** bstn2) = bigStepToN bst2
                                    in ((S $ n1+n2) ** BStIfzSuccN bstn1 bstn2) 


bigStepFromN : BigStepN n e1 e2 -> BigStep e1 e2
bigStepFromN (BStValueN v) = BStValue v
--
bigStepFromN (BStAppN bstn1 bstn2 bstn3) = let bst1 = bigStepFromN bstn1
                                               bst2 = bigStepFromN bstn2
                                               bst3 = bigStepFromN bstn3
                                           in BStApp bst1 bst2 bst3
--                                     
bigStepFromN (BStFixN bstn1 bstn2) = let bst1 = bigStepFromN bstn1
                                         bst2 = bigStepFromN bstn2
                                     in BStFix bst1 bst2
--                                     
bigStepFromN (BStSuccN bstn) = let bst = bigStepFromN bstn
                               in BStSucc bst
--
bigStepFromN (BStPredZeroN bstn) = let bst = bigStepFromN bstn
                                   in BStPredZero bst
--
bigStepFromN (BStPredSuccN bstn) = let bst = bigStepFromN bstn
                                   in BStPredSucc bst
--
bigStepFromN (BStIfzZeroN bstn1 bstn2) = let bst1 = bigStepFromN bstn1
                                             bst2 = bigStepFromN bstn2
                                         in BStIfzZero bst1 bst2
--
bigStepFromN (BStIfzSuccN bstn1 bstn2) = let bst1 = bigStepFromN bstn1
                                             bst2 = bigStepFromN bstn2
                                         in BStIfzSucc bst1 bst2


-- Divergence of 'omega' under the indexed version of big-step semantics:
bigStepDivergenceOmega' : (n : Nat) -> BigStepN n Subst.omega e -> Void
bigStepDivergenceOmega' Z (BStValueN v) = case v of
                                               VZero     impossible
                                               (VSucc _) impossible
                                               VAbs      impossible
bigStepDivergenceOmega' {e} (S n) bstn = case bstn of
  (BStFixN (BStValueN v) bstn2) => let bstn2' = replace {P = \x => BigStepN n x e}
                                                        substOmega bstn2
                                   in bigStepDivergenceOmega' n bstn2'


bigStepDivergenceOmega : BigStep Subst.omega e -> Void
bigStepDivergenceOmega bst = let (n ** bstn) = bigStepToN bst
                             in bigStepDivergenceOmega' n bstn


-- Instead of diverging, the term 'omega' can evaluate to anything
-- under the coinductive relation 'CoBigStep'. Hence, evaluation
-- under 'CoBigStep' is non-deterministic:
coBigStepOmegaAny : CoBigStep Subst.omega e
coBigStepOmegaAny = CoBStFix (CoBStValue VAbs) Determinism.coBigStepOmegaAny 

-- End: DIVERGENCE OF TERM 'Subst.omega' UNDER BIG-STEP
-------------------------------------------------------
