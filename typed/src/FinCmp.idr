
module FinCmp

-- Decidable comparison of finite numbers less 
-- than a given bound (i.e. "ordinals").


import public Data.Fin


%default total
%access public export


-------------------------------------------
-- Begin: DECIDABLE COMPARISONS OF ORDINALS

-- Data type for evidence that "i < j".
data FinLT : Fin n -> Fin n -> Type where
  LtZ : FinLT FZ (FS i)
  LtS : FinLT i j -> FinLT (FS i) (FS j)


-- Simplified symtax:
infixl 6 :<:
(:<:) : Fin n -> Fin n -> Type
(:<:) = FinLT


-- Data type for evidence of which of the
-- following holds between ordinals 'i' and 'j':
--
--    (a) i < j
--    (b) i = j
--    (c) i < j
--
data FinCMP : Fin n -> Fin n -> Type where
  CmpEq : (i = j) -> FinCMP i j
  CmpLt : i :<: j -> FinCMP i j
  CmpGt : j :<: i -> FinCMP i j 


-- Function 'finNotLtZ' yields a proof of the following:
--
--    "There is no ordinal less than zero."
--     (In other words, given a proof that 'i' is
--     less than zero, the function 'finNotLtZ' yields
--     a member of the uninhabited type 'Void'.)
--
finNotLtZ : i :<: FZ -> Void
finNotLtZ _ impossible


-- Function 'finCmpDec' decides whether
--
--    (a) i < j, or 
--    (b) i = j, or
--    (c) i > j  holds,
--
-- and yields evidence in the form of a value
-- of type 'FinCMP i j'.
finCmpDec : (i : Fin n) -> (j : Fin n) -> (FinCMP i j)
finCmpDec i j = case i of
  FZ => case j of
             FZ    => CmpEq Refl
             FS j' => CmpLt LtZ
  FS i' => case j of
                FZ    => CmpGt LtZ
                FS j' => case finCmpDec i' j' of
                              CmpEq eq => CmpEq (rewrite eq in Refl)
                              CmpLt lt => CmpLt (LtS lt)
                              CmpGt lt => CmpGt (LtS lt) 


-- Function 'finLtPred' yields a proof of the following:
--
--    "Given (FS i) < (FS j)m then i < j".
--
finLtPred : (FS i) :<: (FS j) -> i :<: j
finLtPred lt = case lt of LtS lt' => lt'

-- End: DECIDABLE COMPARISONS OF ORDINALS
-----------------------------------------
