import Mathlib.Analysis.Complex.Circle
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
### Auxiliary lemmas
-/

-- [Mathlib.Data.ZMod.Basic]
lemma ZMod.inv_mul_eq_one_of_isUnit {n : ℕ} {a : ZMod n} (ha : IsUnit a) (b : ZMod n) :
    a⁻¹ * b = 1 ↔ a = b := by
  -- ideally, this would be `ha.inv_mul_eq_one`, but `ZMod n` is not a `DivisionMonoid`...
  refine ⟨fun H ↦ ?_, fun H ↦ H ▸ a.inv_mul_of_unit ha⟩
  apply_fun (a * ·) at H
  rwa [← mul_assoc, a.mul_inv_of_unit ha, one_mul, mul_one, eq_comm] at H

-- not needed below, but seems to be missing
@[to_additive]
instance Monoid.neZero_card_of_finite {M : Type*} [Monoid M] [Finite M] : NeZero (Nat.card M) := by
  refine ⟨Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩

@[simp, norm_cast] lemma Circle.coe_pow (z : Circle) (n : ℕ) : (↑(z ^ n) : ℂ) = z ^ n := rfl

@[simp] lemma mem_unitSphere {R} {x} [NormedDivisionRing R] :
    x ∈ Submonoid.unitSphere R ↔ ‖x‖ = 1 := by simp [Submonoid.unitSphere]

/-- The canonical isomorphisms of the group of `n`th roots of unity on the unit circle
with the group of `n`th roots of unity of `ℂ`. -/
noncomputable def Circle.rootsOfUnityMulEquiv {n : ℕ} [NeZero n] :
    rootsOfUnity n Circle ≃* rootsOfUnity n ℂ where
  __ := restrictRootsOfUnity coeHom n
  invFun ζ := rootsOfUnity.mkOfPowEq ⟨(ζ : ℂˣ),
      mem_unitSphere.2 (Complex.norm_eq_one_of_mem_rootsOfUnity ζ.2)⟩
      (by aesop (add simp Units.ext_iff))
  left_inv ζ := by ext; simp
  right_inv ζ := by ext; simp


/-!
### Results for Dirichlet characters

The main goal of this section is to show that `∑ χ : DirichletCharacter R n, χ a` vanishes
if `a ≠ 1` and takes the value `n.totient` otherwise.
-/

namespace DirichletCharacter

section general

noncomputable
instance inhabited (R : Type*) [CommMonoidWithZero R] (n : ℕ) :
    Inhabited (DirichletCharacter R n) where
  default := 1

variable {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]

instance finite : Finite (DirichletCharacter R n) :=
  -- case split since we need different instances `Finite (ZMod n)ˣ`
  n.casesOn (MulChar.finite ..) (fun _ ↦ MulChar.finite ..)

-- This is needed to be able to write down sums over characters.
noncomputable instance fintype : Fintype (DirichletCharacter R n) := .ofFinite _

end general

variable (R : Type*) [CommRing R] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity R n.totient]

private lemma HasEnoughRootsOfUnity.of_totient :
    HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ) :=
  HasEnoughRootsOfUnity.of_dvd R (ZMod.card_units_eq_totient n ▸ Group.exponent_dvd_card)

/-- The group of Dirichlet characters mod `n` with values in a ring `R` that has enough
roots of unity is (noncanonically) isomorphic to `(ZMod n)ˣ`. -/
lemma mulEquiv_units : Nonempty (DirichletCharacter R n ≃* (ZMod n)ˣ) :=
  have := HasEnoughRootsOfUnity.of_totient R n
  MulChar.mulEquiv_units ..

/-- There are `n.totient` Dirichlet characters mod `n` with values in a ring that has enough
roots of unity. -/
lemma card_eq_totient_of_hasEnoughRootsOfUnity :
    Nat.card (DirichletCharacter R n) = n.totient := by
  rw [← ZMod.card_units_eq_totient n, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (mulEquiv_units R n).some.toEquiv

variable {n}

/-- If `R` is a ring that has enough roots of unity and `n ≠ 0`, then for each
`a ≠ 1` in `ZMod n`, there exists a Dirichlet character `χ` mod `n` with values in `R`
such that `χ a ≠ 1`. -/
theorem exists_apply_ne_one_of_hasEnoughRootsOfUnity [Nontrivial R] ⦃a : ZMod n⦄ (ha : a ≠ 1) :
    ∃ χ : DirichletCharacter R n, χ a ≠ 1 :=
  have := HasEnoughRootsOfUnity.of_totient R n
  MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (ZMod n) R ha

variable [IsDomain R]

/-- If `R` is an integral domain that has enough roots of unity and `n ≠ 0`, then
for each `a ≠ 1` in `ZMod n`, the sum of `χ a` over all Dirichlet characters mod `n`
with values in `R` vanishes. -/
theorem sum_characters_eq_zero ⦃a : ZMod n⦄ (ha : a ≠ 1) :
    ∑ χ : DirichletCharacter R n, χ a = 0 := by
  obtain ⟨χ, hχ⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity R ha
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' ↦ rfl

/-- If `R` is an integral domain that has enough roots of unity and `n ≠ 0`, then
for `a` in `ZMod n`, the sum of `χ a` over all Dirichlet characters mod `n`
with values in `R` vanishes if `a ≠ 1` and has the value `n.totient` if `a = 1`. -/
theorem sum_characters_eq (a : ZMod n) :
    ∑ χ : DirichletCharacter R n, χ a = if a = 1 then (n.totient : R) else 0 := by
  split_ifs with ha
  · simpa only [ha, map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card]
      using congrArg Nat.cast <| card_eq_totient_of_hasEnoughRootsOfUnity R n
  · exact sum_characters_eq_zero R ha

/-- If `R` is an integral domain that has enough roots of unity and `n ≠ 0`, then for `a` and `b`
in `ZMod n` with `a` a unit, the sum of `χ a⁻¹ * χ b` over all Dirichlet characters
mod `n` with values in `R` vanishes if `a ≠ b` and has the value `n.totient` if `a = b`. -/
theorem sum_char_inv_mul_char_eq {a : ZMod n} (ha : IsUnit a) (b : ZMod n) :
    ∑ χ : DirichletCharacter R n, χ a⁻¹ * χ b = if a = b then (n.totient : R) else 0 := by
  simp only [← map_mul, sum_characters_eq, ZMod.inv_mul_eq_one_of_isUnit ha]

end DirichletCharacter
