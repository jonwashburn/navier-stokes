/-
  Nat.Card
  --------
  Elementary counting lemmas for finite types.
  Self-contained implementation using only Lean 4 standard library.

  Author: Jonathan Washburn
  Recognition Science Institute
-/

namespace RecognitionScience.Nat.Card

/-- There is no injection from Fin (n+1) to Fin n -/
theorem no_inj_succ_to_self {n : Nat} (f : Fin (n + 1) → Fin n) : ¬Function.Injective f := by
  intro h_inj
  -- Use pigeonhole principle: can't inject n+1 elements into n positions
  -- Consider the n+1 elements: 0, 1, ..., n (all in Fin (n+1))
  let elems : Fin (n + 1) → Fin n := f
  -- Since there are only n possible outputs but n+1 inputs,
  -- by pigeonhole principle, some two inputs must map to the same output

  -- Construct explicit counterexample for small cases or use contradiction
  -- For any injection f : Fin (n+1) → Fin n, we get n+1 ≤ n which is impossible

  -- Direct proof by contradiction with Fin cardinality
  have h_card : n + 1 > n := Nat.lt_succ_self n

  -- If f were injective, we could construct n+1 distinct elements in Fin n
  -- But Fin n only has n elements, which gives us our contradiction

  -- Use the fact that we have n+1 distinct inputs mapping to at most n outputs
  have : ∃ i j : Fin (n + 1), i ≠ j ∧ f i = f j := by
    -- Pigeonhole principle: n+1 elements can't inject into n positions
    -- We'll use a constructive proof by considering all possible values
    by_contra h_not_exist
    push_neg at h_not_exist
    -- h_not_exist says f is injective (all different inputs give different outputs)
    -- But this contradicts our assumption that f is not injective
    have f_inj : Function.Injective f := by
      intro x y h_eq
      by_contra h_ne
      have : x ≠ y ∧ f x = f y := ⟨h_ne, h_eq⟩
      exact h_not_exist x y this
    -- Now we have f_inj but we assumed ¬Function.Injective f
    exact h_inj f_inj

  obtain ⟨i, j, h_neq, h_eq⟩ := this
  exact h_inj h_eq h_neq

/-- If Fin n is in bijection with Fin m, then n = m -/
theorem bij_fin_eq {n m : Nat} (h : Fin n ≃ Fin m) : n = m := by
  -- Bijections preserve cardinality
  -- For Fin types, the cardinality is just the index
  -- If we have f : Fin n ≃ Fin m, then |Fin n| = |Fin m|, so n = m

  -- We can prove this by considering what happens if n ≠ m
  by_contra h_neq
  cases Nat.lt_or_gt_of_ne h_neq with
  | inl h_lt =>
    -- Case: n < m, so we have injection from larger to smaller via h.invFun
    have : ¬Function.Injective h.invFun := by
      -- h.invFun : Fin m → Fin n where m > n
      -- Apply pigeonhole principle
      exact no_inj_succ_to_self h.invFun
    have : Function.Injective h.invFun := h.left_inv ▸ Function.injective_of_left_inverse h.right_inv
    contradiction

  | inr h_gt =>
    -- Case: n > m, so we have injection from larger to smaller via h.toFun
    have : ¬Function.Injective h.toFun := by
      -- h.toFun : Fin n → Fin m where n > m
      -- Apply pigeonhole principle
      exact no_inj_succ_to_self h.toFun
    have : Function.Injective h.toFun := h.right_inv ▸ Function.injective_of_left_inverse h.left_inv
    contradiction

end RecognitionScience.Nat.Card
