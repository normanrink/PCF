
module PCF

-- Re-export modules that define terms and
-- evaluation in the simply-typed lambda calculus.
--
-- Also introduce simplified syntax for lambda calculus
-- terms and utility functions for converting between 
-- Idris' built-in natural numbers and natural numbers
-- in the lambda calculus.


import public BigStep
import public Determinism
import public Equivalence
import public Eval
import public Term
import public Step


%access export


------------------------------------------------------------------
-- Begin: SIMPLIFIED SYNTAX FOR EXPRESSIONS IN THE LAMBDA CALCULUS

-- Simplified syntax for abstraction (viz. "Lambda"):
L : Term (s::ctx) t -> Term ctx (s :->: t)
L = TAbs


-- Simplified syntac for application:
infixl 10 @.
(@.) : Term ctx (s :->: t) -> Term ctx s -> Term ctx t
(@.) = TApp


-- More natural syntax for 'Ifz':
syntax "ifz" [e1] "then" [e2] "else" [e3] = TIfz e1 e2 e3;


-- Constants for the variables with the lowest
-- the de-Bruijn indices (i.e. indices 0--2):
v0 : Term (t::ctx) t
v0 = TVar First

v1 : Term (s::t::ctx) t
v1 = TVar (Next First)

v2 : Term (u::s::t::ctx) t
v2 = TVar (Next (Next First))

-- End: SIMPLIFIED SYNTAX FOR EXPRESSIONS IN THE LAMBDA CALCULUS
----------------------------------------------------------------



---------------------------------
-- Begin: EXAMPLES OF EXPRESSIONS       
        
add : Term ctx (TyNat :->: TyNat :->: TyNat)
add = TFix (L (L (L (ifz v0
                         then v1
                         else v2 @.(TSucc v1) @.(TPred v0) ))))

mul : Term ctx (TyNat :->: TyNat :->: TyNat)
mul = TFix (L (L (L (ifz v0
                         then TZero
                         else add @.(v2 @.v1 @.(TPred v0)) @.v1 ))))

fact : Term ctx (TyNat :->: TyNat)
fact = TFix (L (L (ifz v0
                       then TSucc TZero
                       else mul @.(v1 @.(TPred v0)) @.v0 )))

fact' : Term ctx (TyNat :->: TyNat)
fact' = (L (TFix v0)) @.(L (L (ifz v0
                                   then TSucc TZero
                                   else mul @.(v1 @.(TPred v0)) @.v0 )))

id : Term ctx (t :->: t)
id = L v0
 
first : Term ctx (t :->: t :->: t)
first = L (L v1)
 
second : Term ctx (t :->: t :->: t)
second = L (L v0)

two : Term ctx TyNat
two = TSucc $ TSucc TZero

double : Term ctx (TyNat :->: TyNat)
double = mul @.two

-- End: EXAMPLES OF EXPRESSIONS       
-------------------------------



----------------------------------------
-- Begin: CONVERSIONS FOR NATURAL NUMBER

natToTerm : Nat -> Term ctx TyNat
natToTerm Z     = TZero
natToTerm (S n) = TSucc (natToTerm n)

  
termToNat : Term ctx TyNat -> Nat
termToNat TZero     = Z
termToNat (TSucc n) = S (termToNat n)

-- End: CONVERSIONS FOR NATURAL NUMBER
--------------------------------------

