/-
  Core.Arith
  ----------
  Basic arithmetic lemmas for the Recognition Science framework.
  These are simple helpers used in proving the eight foundations.

  Author: Jonathan Washburn
  Recognition Science Institute
-/

import Core.Finite

namespace RecognitionScience.Arith

/-- Eight-specific modular arithmetic -/
@[simp]
theorem mod_eight_lt (k : Nat) : k % 8 < 8 :=
  Nat.mod_lt k (by decide : 0 < 8)

/-- Adding 8 doesn't change mod 8 value -/
@[simp]
theorem add_eight_mod_eight (k : Nat) : (k + 8) % 8 = k % 8 := by
  rw [Nat.add_mod, Nat.mod_self]
  simp

/-- Helper type for finite sets -/
def finiteUnit : RecognitionScience.Finite Unit := RecognitionScience.finiteUnit

end RecognitionScience.Arith
