import Mathlib.Tactic

lemma pow_eq_one_iff_of_nonneg {R : Type*} [LinearOrderedRing R] (x : R) (hx : 0 ≤ x)
    (n : ℕ) (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 := by
  constructor
  · intro h
    exact le_antisymm ((pow_le_one_iff_of_nonneg hx hn).mp h.le)
      ((one_le_pow_iff_of_nonneg hx hn).mp h.ge)
  · rintro rfl
    exact one_pow _

lemma ZMod.exists_pos_unit_pow_eq_one : (n : ℕ) → ∃ m : ℕ, 0 < m ∧ ∀ a : (ZMod n)ˣ, a ^ m = 1 := by
  intro n
  sorry
