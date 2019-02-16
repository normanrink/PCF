
module PCF

-- Re-export modules that define expressions and
-- evaluation in the untyped lambda calculus.
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
L : Term (S n) -> Term n
L = TAbs


-- Simplified syntac for application:
infixl 10 @.
(@.) : Term n -> Term n -> Term n
(@.) = TApp


-- More natural syntax for 'Ifz':
syntax "ifz" [e1] "then" [e2] "else" [e3] = TIfz e1 e2 e3;


-- Constants for the variables with the lowest
-- the de-Bruijn indices (i.e. indices 0--2):
v0 : Term (S n)
v0 = TVar 0

v1 : Term (S (S n))
v1 = TVar 1

v2 : Term (S (S (S n)))
v2 = TVar 2

v3 : Term (S (S (S (S n))))
v3 = TVar 3


-- Fix-point operator:
Fix : Term n
Fix = (L $
         (L $ v1 @.(L $ v1 @.v1 @.v0)) @.
         (L $ v1 @.(L $ v1 @.v1 @.v0))    )

-- End: SIMPLIFIED SYNTAX FOR EXPRESSIONS IN THE LAMBDA CALCULUS
----------------------------------------------------------------



---------------------------------
-- Begin: EXAMPLES OF EXPRESSIONS       

                
add : Term n
add = Fix @.(L (L (L (ifz v0
                          then v1
                          else v2 @.(TSucc v1) @.(TPred v0) ))))

mul : Term n
mul = Fix @.(L (L (L (ifz v0
                          then TZero
                          else add @.(v2 @.v1 @.(TPred v0)) @.v1 ))))

fact : Term n
fact = Fix @.(L (L (ifz v0
                        then TSucc TZero
                        else mul @.(v1 @.(TPred v0)) @.v0 )))

fact' : Term n
fact' = (L (Fix @.v0)) @.(L (L (ifz v0
                                    then TSucc TZero
                                    else mul @.(v1 @.(TPred v0)) @.v0 )))
                                                   
id : Term n
id = L v0
 
first : Term n
first = L (L v1)
 
second : Term k
second = L (L v0)

two : Term n
two = TSucc $ TSucc TZero

double : Term n
double = mul @.two

-- End: EXAMPLES OF EXPRESSIONS       
-------------------------------



----------------------------------------
-- Begin: CONVERSIONS FOR NATURAL NUMBER

natToTerm : Nat -> Term n
natToTerm Z     = TZero
natToTerm (S n) = TSucc (natToTerm n)

  
termToNat : Term n -> Nat
termToNat TZero     = Z
termToNat (TSucc n) = S (termToNat n)

-- End: CONVERSIONS FOR NATURAL NUMBER
--------------------------------------

          
