import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Field.UnitBall
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
### Auxiliary lemmas
-/

/-
-- not needed below, but seems to be missing
@[to_additive]
instance Monoid.neZero_card_of_finite {M : Type*} [Monoid M] [Finite M] : NeZero (Nat.card M) := by
  refine ⟨Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩
-/

-- [Mathlib.Analysis.Complex.Circle]
@[simp, norm_cast] lemma Circle.coe_pow (z : Circle) (n : ℕ) : (↑(z ^ n) : ℂ) = z ^ n := rfl

-- [Mathlib.Analysis.Normed.Field.UnitBall]
@[simp] lemma Submonoid.mem_unitSphere {R : Type*} [NormedDivisionRing R] {x : R} :
    x ∈ unitSphere R ↔ ‖x‖ = 1 := by
  simp only [unitSphere, mem_mk, Subsemigroup.mem_mk, mem_sphere_iff_norm, sub_zero]

/-- The canonical isomorphisms of the group of `n`th roots of unity on the unit circle
with the group of `n`th roots of unity of `ℂ`. -/
--. TODO: Generalize to `NormedField 𝕜` in place of `ℂ`.
noncomputable def Circle.rootsOfUnityMulEquiv (n : ℕ) [NeZero n] :
    rootsOfUnity n Circle ≃* rootsOfUnity n ℂ where
  __ := restrictRootsOfUnity coeHom n
  invFun ζ := rootsOfUnity.mkOfPowEq ⟨(ζ : ℂˣ),
      Submonoid.mem_unitSphere.mpr (Complex.norm_eq_one_of_mem_rootsOfUnity ζ.prop)⟩
      (ext <| by simp only [coe_pow, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity ..).mp ζ.prop,
                   Units.val_one, OneMemClass.coe_one])
  left_inv ζ := by ext; simp
  right_inv ζ := by ext; simp

/- lemma HasEnoughRootsOfUnity.of_mulEquiv {M M' : Type*} [CommMonoid M] [CommMonoid M'] {n : ℕ}
    [NeZero n] [HasEnoughRootsOfUnity M n] (equiv : rootsOfUnity n M ≃* rootsOfUnity n M') :
    HasEnoughRootsOfUnity M' n where
      prim := by
        obtain ⟨ζ, hζ⟩ := exists_primitiveRoot M n
        refine ⟨(equiv hζ.toRootsOfUnity : M'ˣ), ?_⟩
        rw [IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.coe_submonoidClass_iff]
        rw [IsPrimitiveRoot.iff_def]
        simp only [← map_pow]
        refine ⟨?_, fun l hl ↦ ?_⟩
        · simp? [hζ]
      cyc := sorry -/

open Complex Real in
instance Circle.hasEnoghRootsOfUnity {n : ℕ} [NeZero n] : HasEnoughRootsOfUnity Circle n where
  prim := by
    refine ⟨⟨cexp ((2 * π / n :) * I), ?_⟩, ?_⟩
    · simpa only [Submonoid.mem_unitSphere] using norm_exp_ofReal_mul_I (2 * π / ↑n)
    · refine IsPrimitiveRoot.of_map_of_injective (f := coeHom) ?_
        ((Set.injective_codRestrict Subtype.property).mp fun ⦃_ _⦄ a ↦ a)
      simp only [coeHom_apply]
      convert Complex.isPrimitiveRoot_exp n (NeZero.ne n) using 2
      push_cast
      ring
  cyc := by
    sorry

-- #min_imports
