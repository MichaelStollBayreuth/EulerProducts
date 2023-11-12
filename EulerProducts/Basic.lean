import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Int.Order.Units
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

section tsum

open BigOperators

variable {α β : Type*} [AddCommMonoid α] [TopologicalSpace α]

-- these should go into `Mathlib.Topology.Algebra.InfiniteSum.Basic`
open Set in
lemma tsum_setElem_eq_tsum_setElem_diff [T2Space α] {f : β → α} (s t : Set β)
    (hf₀ : ∀ b ∈ t, f b = 0) :
    ∑' a : s, f a = ∑' a : (s \ t : Set β), f a := by
  simp_rw [tsum_subtype]
  refine tsum_congr fun b' ↦ ?_
  by_cases hs : b' ∈ s \ t
  · rw [indicator_of_mem hs f, indicator_of_mem (mem_of_mem_diff hs) f]
  · rw [indicator_of_not_mem hs f]
    rw [mem_diff, not_and, not_not_mem] at hs
    by_cases h₁ : b' ∈ s
    · simpa [indicator_of_mem h₁] using hf₀ b' <| hs h₁
    · exact indicator_of_not_mem h₁ f

open Set in
/-- If `f b = 0`, then the sum over all `f a` is the same as the sum over `f a` for `a ≠ b`. -/
lemma tsum_eq_tsum_diff_singleton [T2Space α] {f : β → α} (s : Set β) {b : β} (hf₀ : f b = 0) :
    ∑' a : s, f a = ∑' a : (s \ {b} : Set β), f a :=
  tsum_setElem_eq_tsum_setElem_diff s {b} fun _ ha ↦ ha ▸ hf₀

lemma hasSum_singleton (m : β) (f : β → α) : HasSum (({m} : Set β).restrict f) (f m) := by
  convert_to HasSum (fun x : ({m} : Set β) ↦ f x) (f (⟨m, rfl⟩ : ({m} : Set β)))
  exact hasSum_single (α := α) _ <| fun m' h ↦ False.elim <| h <| Subtype.ext m'.2

end tsum

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
