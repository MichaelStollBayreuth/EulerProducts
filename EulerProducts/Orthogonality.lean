import Mathlib.GroupTheory.FiniteAbelian
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
### Commutative monoids that have enough roots of unity
-/

lemma ZMod.inv_mul_eq_one_of_isUnit {n : ℕ} {a : ZMod n} (ha : IsUnit a) (b : ZMod n) :
    a⁻¹ * b = 1 ↔ a = b := by
  -- ideally, this would be `ha.inv_mul_eq_one`, but `ZMod n` is not a `DivisionMonoid`...
  refine ⟨fun H ↦ ?_, fun H ↦ H ▸ a.inv_mul_of_unit ha⟩
  apply_fun (a * ·) at H
  rwa [← mul_assoc, a.mul_inv_of_unit ha, one_mul, mul_one, eq_comm] at H

namespace IsAlgClosed

/-- An algebraically closed field of characteristic zero satisfies `HasEnoughRootsOfUnity`
for all `n`. -/
instance hasEnoughRootsOfUnity (F : Type*) [Field F] [IsAlgClosed F] [CharZero F] (n : ℕ)
    [NeZero n] :
    HasEnoughRootsOfUnity F n where
  prim := Subtype.coe_mk n (NeZero.pos n) ▸ IsCyclotomicExtension.exists_prim_root F rfl
  cyc := rootsOfUnity.isCyclic F n

end IsAlgClosed

/-!
### Results for general finite abelian groups
-/

namespace CommGroup

open MonoidHom

private
lemma dvd_exponent {ι G : Type*} [Finite ι] [CommGroup G] {n : ι → ℕ}
    (e : G ≃* ((i : ι) → Multiplicative (ZMod (n i)))) (i : ι) :
  n i ∣ Monoid.exponent G := by
  classical -- to get `DecidableEq ι`
  have : n i = orderOf (e.symm <| Pi.mulSingle i <| .ofAdd 1) := by
    simpa only [MulEquiv.orderOf_eq, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf]
      using (ZMod.addOrderOf_one (n i)).symm
  exact this ▸ Monoid.order_dvd_exponent _

variable (G M : Type*) [CommGroup G] [Finite G] [CommMonoid M]

private
lemma exists_apply_ne_one_aux (H : ∀ n : ℕ, n ∣ Monoid.exponent G → ∀ a : ZMod n, a ≠ 0 →
       ∃ φ : Multiplicative (ZMod n) →* M, φ (.ofAdd a) ≠ 1)
    {a : G} (ha : a ≠ 1) :
    ∃ φ : G →* M, φ a ≠ 1 := by
  obtain ⟨ι, _, n, _, h⟩ := CommGroup.equiv_prod_multiplicative_zmod G
  let e := h.some
  obtain ⟨i, hi⟩ : ∃ i : ι, e a i ≠ 1 := by
    contrapose! ha
    exact (MulEquiv.map_eq_one_iff e).mp <| funext ha
  have hi : Multiplicative.toAdd (e a i) ≠ 0 := by
    simp only [ne_eq, toAdd_eq_zero, hi, not_false_eq_true]
  obtain ⟨φi, hφi⟩ := H (n i) (dvd_exponent e i) (Multiplicative.toAdd <| e a i) hi
  use (φi.comp (Pi.evalMonoidHom (fun (i : ι) ↦ Multiplicative (ZMod (n i))) i)).comp e
  simpa only [coe_comp, coe_coe, Function.comp_apply, Pi.evalMonoidHom_apply, ne_eq] using hφi

variable  [HasEnoughRootsOfUnity M (Monoid.exponent G)]

/-- If `G` is a finite commutative group of exponent `n` and `M` is a commutative monoid
with enough `n`th roots of unity, then for each `a ≠ 1` in `G`, there exists a
group homomorphism `φ : G → Mˣ` such that `φ a ≠ 1`. -/
theorem exists_apply_ne_one_of_hasEnoughRootsOfUnity {a : G} (ha : a ≠ 1) :
    ∃ φ : G →* Mˣ, φ a ≠ 1 := by
  refine exists_apply_ne_one_aux G Mˣ (fun n hn a ha₀ ↦ ?_) ha
  have : NeZero n := ⟨fun H ↦ NeZero.ne _ <| Nat.eq_zero_of_zero_dvd (H ▸ hn)⟩
  have := HasEnoughRootsOfUnity.of_dvd M hn
  exact ZMod.exists_monoidHom_apply_ne_one (HasEnoughRootsOfUnity.exists_primitiveRoot M n) ha₀

/-- A finite commutative group `G` is (noncanonically) isomorphic to the group `G →* Mˣ`
of `M`-valued characters when `M` is a commutative monoid with enough `n`th roots of unity,
where `n` is the exponent of `G`. -/
theorem monoidHom_mulEquiv_self_of_hasEnoughRootsOfUnity : Nonempty (G ≃* (G →* Mˣ)) := by
  classical -- to get `DecidableEq ι`
  obtain ⟨ι, _, n, ⟨h₁, h₂⟩⟩ := equiv_prod_multiplicative_zmod G
  let e := h₂.some
  let e' := Pi.monoidHomMulEquiv (fun i ↦ Multiplicative (ZMod (n i))) Mˣ
  let e'' := MulEquiv.monoidHomCongr e (.refl Mˣ)
  have : ∀ i, NeZero (n i) := fun i ↦ NeZero.of_gt (h₁ i)
  have inst i : HasEnoughRootsOfUnity M <| Nat.card <| Multiplicative <| ZMod (n i) := by
    have hdvd : Nat.card (Multiplicative (ZMod (n i))) ∣ Monoid.exponent G := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
        using dvd_exponent e i
    exact HasEnoughRootsOfUnity.of_dvd M hdvd
  let E i := (monoidHom_equiv_self (Multiplicative (ZMod (n i))) M).some
  exact ⟨e.trans (MulEquiv.piCongrRight E).symm|>.trans e'.symm|>.trans e''.symm⟩

end CommGroup


/-!
### Results for multiplicative characters

We provide instances for `Finite (MulChar M R)` and `Fintype (MulChar M R)`
when `M` is a finite commutative monoid and `R` is an integral domain.

We also show that `MulChar M R` and `Mˣ` have the same cardinality when `R` has
enough roots of unity.
-/

namespace MulChar

variable {M R : Type*} [CommMonoid M] [CommRing R]

instance finite [Finite Mˣ] [IsDomain R] : Finite (MulChar M R) := by
  have : Finite (Mˣ →* Rˣ) := by
    have : Fintype Mˣ := .ofFinite _
    let S := rootsOfUnity (Fintype.card Mˣ) R
    let F := Mˣ →* S
    have fF : Finite F := .of_injective _ DFunLike.coe_injective
    refine .of_surjective (fun f : F ↦ (Subgroup.subtype _).comp f) fun f ↦ ?_
    have H a : f a ∈ S := by simp only [mem_rootsOfUnity, ← map_pow, pow_card_eq_one, map_one, S]
    refine ⟨.codRestrict f S H, MonoidHom.ext fun _ ↦ ?_⟩
    simp only [MonoidHom.coe_comp, Subgroup.coeSubtype, Function.comp_apply,
      MonoidHom.codRestrict_apply]
  exact .of_equiv _ MulChar.equivToUnitHom.symm

noncomputable instance fintype [Finite M] [IsDomain R] :
    Fintype (MulChar M R) := .ofFinite _

lemma exists_apply_ne_one_iff_exists_monoidHom (a : Mˣ) :
    (∃ χ : MulChar M R, χ a ≠ 1) ↔ ∃ φ : Mˣ →* Rˣ, φ a ≠ 1 := by
  refine ⟨fun ⟨χ, hχ⟩ ↦ ⟨χ.toUnitHom, ?_⟩, fun ⟨φ, hφ⟩ ↦ ⟨ofUnitHom φ, ?_⟩⟩
  · contrapose! hχ
    rwa [Units.ext_iff, coe_toUnitHom] at hχ
  · contrapose! hφ
    simpa only [ofUnitHom_eq, equivToUnitHom_symm_coe, Units.val_eq_one] using hφ

variable (M R)
variable [Finite M] [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)]

/-- If `M` is a finite commutative monoid and `R` is a ring that has enough roots of unity,
then for each `a ≠ 1` in `M`, there exists a multiplicative character `χ : M → R` such that
`χ a ≠ 1`. -/
theorem exists_apply_ne_one_of_hasEnoughRootsOfUnity [Nontrivial R] {a : M} (ha : a ≠ 1) :
    ∃ χ : MulChar M R, χ a ≠ 1 := by
  by_cases hu : IsUnit a
  . refine (exists_apply_ne_one_iff_exists_monoidHom hu.unit).mpr ?_
    refine CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Mˣ R ?_
    contrapose! ha
    rw [← hu.unit_spec, ha, Units.val_eq_one]
  · exact ⟨1, by simpa only [map_nonunit _ hu] using zero_ne_one⟩

/-- The group of `R`-valued multiplicative characters on a finite commutative monoid `M` is
(noncanonically) isomorphic to its unit group `Mˣ` when `R` is a ring that has enough roots
of unity. -/
lemma mulEquiv_units : Nonempty (MulChar M R ≃* Mˣ) :=
  ⟨mulEquivToUnitHom.trans
    (CommGroup.monoidHom_mulEquiv_self_of_hasEnoughRootsOfUnity Mˣ R).some.symm⟩

/-- The cardinality of the group of `R`-valued multiplicative characters on a finite commutative
monoid `M` is the same as that of its unit group `Mˣ` when `R` is a ring that has enough roots
of unity. -/
lemma card_eq_card_units_of_hasEnoughRootsOfUnity : Nat.card (MulChar M R) = Nat.card Mˣ :=
  Nat.card_congr (mulEquiv_units M R).some.toEquiv

end MulChar


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
  letI : Finite (ZMod n)ˣ := n.casesOn inferInstance inferInstance
  MulChar.finite ..

noncomputable instance fintype : Fintype (DirichletCharacter R n) := .ofFinite _

lemma sum_characters_eq_zero_aux {a : ZMod n} (h : ∃ χ : DirichletCharacter R n, χ a ≠ 1) :
    ∑ χ : DirichletCharacter R n, χ a = 0 := by
  obtain ⟨χ, hχ⟩ := h
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' ↦ rfl

lemma sum_characters_eq_zero_iff_aux {a : ZMod n} [CharZero R]
    (h : ∀ a : ZMod n, a ≠ 1 → ∃ χ : DirichletCharacter R n, χ a ≠ 1) :
    ∑ χ : DirichletCharacter R n, χ a = 0 ↔ a ≠ 1 := by
  refine ⟨fun H ha ↦ ?_, fun H ↦ sum_characters_eq_zero_aux <| h a H⟩
  simp only [ha, map_one, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_eq_zero,
    Finset.card_eq_zero, Finset.univ_eq_empty_iff] at H
  exact (not_isEmpty_of_nonempty <| DirichletCharacter R n) H

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

/-- There are `n.totient` Dirichlet characters mod `n` with values in a ring that has all
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
    ∑ χ : DirichletCharacter R n, χ a = 0 :=
  sum_characters_eq_zero_aux <| exists_apply_ne_one_of_hasEnoughRootsOfUnity R ha

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
mod `n` with values in `R` vanihses if `a ≠ b` and has the value `n.totient` if `a = b`. -/
theorem sum_char_inv_mul_char_eq {a : ZMod n} (ha : IsUnit a) (b : ZMod n) :
    ∑ χ : DirichletCharacter R n, χ a⁻¹ * χ b = if a = b then n.totient else 0 := by
  simp only [← map_mul, sum_characters_eq, ZMod.inv_mul_eq_one_of_isUnit ha, Nat.cast_ite,
    Nat.cast_zero]

end DirichletCharacter
