import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.Normed.Field.Basic

section DirichletChar

example : Fintype.card ℤˣ = 2 := by rw [Fintype.card_units_int]

example : ZMod 0 = ℤ := rfl

-- lemma Int.natCard_units : Nat.card ℤˣ = 2 :=
--   Nat.card_eq_two_iff.mpr ⟨1, -1, Int.units_ne_neg_self 1, Set.toFinset_eq_univ.mp rfl⟩

-- instance FintypeZModUnits (n : ℕ) : Fintype (ZMod n)ˣ := by
--   match n with
--   | 0 => change Fintype ℤˣ; infer_instance
--   | n + 1 => exact instFintypeUnits

instance FiniteZModUnits : (n : ℕ) → Finite (ZMod n)ˣ
| 0     => Finite.of_fintype ℤˣ
| _ + 1 => instFiniteUnits


-- Mathlib.FieldTheory.Finite.Basic
lemma ZMod.exists_pos_unit_pow_eq_one (n : ℕ) : ∃ m : ℕ, 0 < m ∧ ∀ a : (ZMod n)ˣ, a ^ m = 1 :=
  ⟨Nat.card (ZMod n)ˣ, Nat.card_pos, fun _ ↦ pow_card_eq_one'⟩

  -- match n with
  -- | 0     => ⟨2, zero_lt_two, Int.units_sq⟩
  -- | n + 1 => ⟨n.succ.totient, Nat.totient_pos n.succ_pos, ZMod.pow_totient⟩


-- This will eventually show up in Mathlib (future PR by Yaël Dillies)
-- Mathlib.Algebra.GroupPower.Order
lemma pow_eq_one_iff_of_nonneg {R : Type*} [LinearOrderedRing R] {x : R} (hx : 0 ≤ x)
    {n : ℕ} (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 :=
  ⟨fun h ↦ le_antisymm ((pow_le_one_iff_of_nonneg hx hn).mp h.le)
            ((one_le_pow_iff_of_nonneg hx hn).mp h.ge),
   fun h ↦ by rw [h]; exact one_pow _⟩

-- TODO: change to `{F : Type*}` when this is done in `DirichletCharacter.Basic`
variable {F : Type} [NormedField F]

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

variable {R : Type*} [CommMonoidWithZero R] {n : ℕ} {χ : DirichletCharacter R n}

lemma conductor_le_conductor_mem_conductorSet {d : ℕ} (hd : d ∈ conductorSet χ) :
    χ.conductor ≤ (Classical.choose hd.2 ).conductor := by
  refine Nat.sInf_le <| (mem_conductorSet_iff χ).mpr <|
    ⟨dvd_trans (conductor_dvd_level _) hd.1,
     (factorsThrough_conductor (Classical.choose hd.2)).2.choose, ?_⟩
  rw [changeLevel_trans _ (conductor_dvd_level _) (FactorsThrough.dvd _ hd),
      ← (factorsThrough_conductor (Classical.choose hd.2)).2.choose_spec]
  exact FactorsThrough.eq_changeLevel χ hd

variable (χ)

/-- The primitive character associated to a Dirichlet character. -/
noncomputable def primitiveCharacter : DirichletCharacter R χ.conductor :=
  Classical.choose (factorsThrough_conductor χ).choose_spec

lemma reduction_isPrimitive : isPrimitive (χ.primitiveCharacter) := by
  by_cases h : χ.conductor = 0
  · rw [isPrimitive_def]
    convert conductor_eq_zero_iff_level_eq_zero.mpr h
  · exact le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero h) (conductor_dvd_level _)) <|
      conductor_le_conductor_mem_conductorSet <| conductor_mem_conductorSet χ
  -- refine (eq_or_ne χ.conductor 0).elim (fun h ↦ (isPrimitive_def _).mpr ?_) <|
  --   fun h ↦ le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero h) (conductor_dvd_level _)) <|
  --     conductor_le_conductor_mem_conductorSet _ <| conductor_mem_conductorSet χ
  -- convert conductor_eq_zero_iff_level_eq_zero.mpr h


lemma reduction_one (hn : n ≠ 0) : (1 : DirichletCharacter R n).primitiveCharacter = 1 := by
  rw [eq_one_iff_conductor_eq_one <| (@conductor_one R _ _ hn) ▸ Nat.one_ne_zero,
      (isPrimitive_def _).1 (1 : DirichletCharacter R n).reduction_isPrimitive,
      conductor_one hn]

end DirichletCharacter

end DirichletChar
