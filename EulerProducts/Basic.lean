import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.Normed.Field.Basic

section DirichletChar

variable {F : Type} [NormedField F]

lemma ZMod.exists_pos_unit_pow_eq_one (n : ℕ) : ∃ m : ℕ, 0 < m ∧ ∀ a : (ZMod n)ˣ, a ^ m = 1 :=
  match n with
  | 0     => ⟨2, zero_lt_two, Int.units_sq⟩
  | n + 1 => ⟨n.succ.totient, Nat.totient_pos n.succ_pos, ZMod.pow_totient⟩

-- This will eventually show up in Mathlib (future PR by Yaël Dillies)
lemma pow_eq_one_iff_of_nonneg {R : Type*} [LinearOrderedRing R] {x : R} (hx : 0 ≤ x)
    {n : ℕ} (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 := by
  constructor
  · intro h
    exact le_antisymm ((pow_le_one_iff_of_nonneg hx hn).mp h.le)
      ((one_le_pow_iff_of_nonneg hx hn).mp h.ge)
  · rintro rfl
    exact one_pow _

lemma DirichletCharacter.norm_eq_one {n : ℕ} (χ : DirichletCharacter F n) (m : (ZMod n)ˣ) :
    ‖χ m‖ = 1 := by
  obtain ⟨e, he₀, he₁⟩ := ZMod.exists_pos_unit_pow_eq_one n
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) he₀.ne').mp ?_
  rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, he₁ m, Units.val_one, map_one, norm_one]

lemma DirichletCharacter.norm_le_one {n : ℕ} (χ : DirichletCharacter F n) (m : ZMod n) :
    ‖χ m‖ ≤ 1 := by
  by_cases h : IsUnit m
  · exact (DirichletCharacter.norm_eq_one χ h.unit).le
  · rw [χ.map_nonunit h, norm_zero]
    exact zero_le_one

end DirichletChar
