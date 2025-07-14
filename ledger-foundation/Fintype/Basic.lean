/-
  Fintype/Basic.lean - Fin injectivity proof using mathlib
  Uses mathlib for type cardinality reasoning
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace MiniFintype

-- Type Constructor Injectivity Theorem
-- This is a fundamental metatheoretical property: type constructors are injective
-- In type theory, if T(a) = T(b) then a = b for any type constructor T
-- Proved using mathlib's cardinality reasoning
theorem fin_eq_of_type_eq {n m : Nat} : (Fin n = Fin m) → n = m := by
  intro h
  -- Since Fin n and Fin m are equal types, they must have equal cardinalities
  have h_card : Fintype.card (Fin n) = Fintype.card (Fin m) := by
    simp [h]
  -- Since |Fin n| = n and |Fin m| = m, we get n = m
  simp [Fintype.card_fin] at h_card
  exact h_card

end MiniFintype
