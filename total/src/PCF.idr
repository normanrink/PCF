
module PCF

-- Re-export modules that define expressions and
-- evaluation in the simply-typed lambda calculus.
--
-- Also introduce simplified syntax for lambda calculus
-- expressions and utility functions for converting
-- between Idris' built-in natural numbers and natural
-- numbers in the lambda calculus.


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
v0 : {ctx : Context (S n)} ->
     {auto p : index 0 ctx = t} -> Term ctx t
v0 = TVar 0

v1 : {ctx : Context (S (S n))} ->
     {auto p : index 1 ctx = t} -> Term ctx t
v1 = TVar 1

v2 : {ctx : Context (S (S (S n)))} ->
     {auto p : index 2 ctx = t} -> Term ctx t
v2 = TVar 2

v3 : {ctx : Context (S (S (S (S n))))} ->
     {auto p : index 3 ctx = t} -> Term ctx t
v3 = TVar 3

-- End: SIMPLIFIED SYNTAX FOR EXPRESSIONS IN THE LAMBDA CALCULUS
----------------------------------------------------------------



---------------------------------
-- Begin: EXAMPLES OF EXPRESSIONS       
        
add : Term ctx (TyNat :->: TyNat :->: TyNat)
add = (L (L (TRec v0 
                  v1
                  (TSucc v0) )))

mul : Term ctx (TyNat :->: TyNat :->: TyNat)
mul = (L (L (TRec v0
                  TZero
                  (add @.v0 @.v3 ) )))


fact : Term ctx (TyNat :->: TyNat)
fact = (L (TRec v0
                (TSucc TZero)
                (mul @.v0 @.(TSucc v1)) ))
                
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


