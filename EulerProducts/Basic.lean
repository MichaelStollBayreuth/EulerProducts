import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.Normed.Field.Basic

section DirichletChar

example : Fintype.card ℤˣ = 2 := by rw [Fintype.card_units_int]

example : ZMod 0 = ℤ := rfl

/-- For each `n ≥ 0`, the unit group of `ZMod n` is finite. -/
instance finiteZModUnits : (n : ℕ) → Finite (ZMod n)ˣ
| 0     => Finite.of_fintype ℤˣ
| _ + 1 => instFiniteUnits

-- Mathlib.Algebra.GroupPower.Order
lemma pow_eq_one_iff_of_nonneg {R : Type*} [LinearOrderedRing R] {x : R} (hx : 0 ≤ x)
    {n : ℕ} (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 :=
  ⟨fun h ↦ le_antisymm ((pow_le_one_iff_of_nonneg hx hn).mp h.le)
            ((one_le_pow_iff_of_nonneg hx hn).mp h.ge),
   fun h ↦ by rw [h]; exact one_pow _⟩

variable {F : Type*} [NormedField F]

namespace DirichletCharacter

/-- The value at a unit of a Dirichlet character with target a normed field has norm `1`. -/
lemma unit_norm_eq_one {n : ℕ} (χ : DirichletCharacter F n) (m : (ZMod n)ˣ) :
    ‖χ m‖ = 1 := by
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.card_pos (α := (ZMod n)ˣ)).ne').mp ?_
  rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one,
    norm_one]

/-- The values of a Dirichlet character with target a normed field have norm bounded by `1`. -/
lemma norm_le_one {n : ℕ} (χ : DirichletCharacter F n) (m : ZMod n) :
    ‖χ m‖ ≤ 1 := by
  by_cases h : IsUnit m
  · exact (unit_norm_eq_one χ h.unit).le
  · rw [χ.map_nonunit h, norm_zero]
    exact zero_le_one

end DirichletCharacter

end DirichletChar
