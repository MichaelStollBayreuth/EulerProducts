import Mathlib.GroupTheory.FiniteAbelian
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
### The multiplicative version of the classification theorem for finite abelian groups
-/

/-- The canonical isomorphism of a finite direct sum of additive commutative monoids
and the corresponding finite product. -/
def DirectSum.equivProd {ι : Type*} [Fintype ι] (G : ι → Type*) [(i : ι) → AddCommMonoid (G i)] :
    DirectSum ι G ≃+ ((i : ι) → G i) :=
  ⟨DFinsupp.equivFunOnFintype, fun g h ↦ by
    ext
    simp only [DFinsupp.equivFunOnFintype, Equiv.toFun_as_coe, Equiv.coe_fn_mk, add_apply,
      Pi.add_apply]⟩

/-- Taking products is compatible with switching from additive to multiplicative and back. -/
def additiveProdMultiplicativeAddEquivProd {ι : Type*} (G : ι → Type*)
    [(i : ι) → AddMonoid (G i)] :
    Additive ((i : ι) → Multiplicative (G i)) ≃+ ((i : ι) → G i) where
  toFun g i := Multiplicative.toAdd <| (Additive.toMul g) i
  invFun g := Additive.ofMul fun i ↦ Multiplicative.ofAdd <| g i
  left_inv g := rfl
  right_inv g := rfl
  map_add' g h := by ext; simp only [toMul_add, Pi.mul_apply, toAdd_mul, Pi.add_apply]

/-- The **Classification Theorem For Finite Abelian Groups** in a multiplicative version:
A finite commutative group `G` is isomorphic to a finite product of finite cyclic groups. -/
theorem CommGroup.equiv_prod_multiplicative_zmod (G : Type*) [CommGroup G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ),
       (∀ (i : ι), 1 < n i) ∧ Nonempty (G ≃* ((i : ι) → Multiplicative (ZMod (n i)))) := by
  obtain ⟨ι, inst, n, h₁, h₂⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' (Additive G)
  let inst' := inst
  exact ⟨ι, inst, n, h₁, ⟨MulEquiv.toAdditive.symm <|
    h₂.some.trans ((additiveProdMultiplicativeAddEquivProd (fun i ↦ ZMod (n i))).trans
      (DirectSum.equivProd (fun i ↦ ZMod (n i))).symm).symm⟩⟩


/-!
### Results specific for cyclic groups
-/

namespace IsCyclic

/-- The isomorphism from the group of group homomorphisms from a finite cyclic group `G` of order
`n` into another group `G'` to the group of `n`th roots of unity in `G'` determined by a generator
of `G`. -/
noncomputable
def monoidHomMulEquivRootsOfUnityOfGenerator {G : Type*} [CommGroup G] [Fintype G] {g : G}
    (hg : ∀ (x : G), x ∈ Subgroup.zpowers g) (G' : Type*) [CommGroup G'] :
    (G →* G') ≃* rootsOfUnity ⟨Fintype.card G, Fintype.card_pos⟩ G' where
  toFun φ := ⟨(IsUnit.map φ <| Group.isUnit _ : IsUnit <| φ g).unit, by
    simp only [mem_rootsOfUnity, PNat.mk_coe, Units.ext_iff, Units.val_pow_eq_pow_val,
      IsUnit.unit_spec, ← map_pow, pow_card_eq_one, map_one, Units.val_one]⟩
  invFun ζ := monoidHomOfForallMemZpowers hg (g' := (ζ.val : G')) <| by
    simpa only [orderOf_eq_card_of_forall_mem_zpowers hg, orderOf_dvd_iff_pow_eq_one, ←
      Units.val_pow_eq_pow_val, Units.val_eq_one] using ζ.prop
  left_inv φ := (MonoidHom.eq_iff_eq_on_generator hg _ φ).mpr <| by
    simp only [IsUnit.unit_spec, monoidHomOfForallMemZpowers_apply_gen]
  right_inv φ := by
    ext1
    simp only [monoidHomOfForallMemZpowers_apply_gen, IsUnit.unit_of_val_units]
  map_mul' x y := by
    simp only [MonoidHom.mul_apply, MulMemClass.mk_mul_mk, Subtype.mk.injEq, Units.ext_iff,
      IsUnit.unit_spec, Units.val_mul]

/-- The group of group homomorphisms from a finite cyclic group `G` of order `n` into another
group `G'` is isomorphic to the group of `n`th roots of unity in `G'`. -/
lemma monoidHom_mulEquiv_rootsOfUnity  (G : Type*) [CommGroup G] [Fintype G]
    [inst_cyc : IsCyclic G] (G' : Type*) [CommGroup G'] :
    Nonempty <| (G →* G') ≃* rootsOfUnity ⟨Fintype.card G, Fintype.card_pos⟩ G' := by
  obtain ⟨g, hg⟩ := inst_cyc.exists_generator
  exact ⟨monoidHomMulEquivRootsOfUnityOfGenerator hg G'⟩

end IsCyclic

-- #######################################################################

lemma MonoidHom.exists_apply_ne_one (G R : Type*) [CommGroup G] [Finite G] [CommMonoid R]
    (H : ∀ n : ℕ, n ≠ 0 → ∀ a : ZMod n, a ≠ 0 →
       ∃ φ : Multiplicative (ZMod n) →* R, φ (Multiplicative.ofAdd a) ≠ 1)
    {a : G} (ha : a ≠ 1) :
    ∃ φ : G →* R, φ a ≠ 1 := by
  obtain ⟨ι, _, n, h₁, h₂⟩ := CommGroup.equiv_prod_multiplicative_zmod G
  let e := h₂.some
  obtain ⟨i, hi⟩ : ∃ i : ι, e a i ≠ 1 := by
    contrapose! ha
    suffices e a = 1 from (MulEquiv.map_eq_one_iff e).mp this
    exact funext ha
  have hi' : Multiplicative.toAdd (e a i) ≠ 0 := by
    simp only [ne_eq, toAdd_eq_zero, hi, not_false_eq_true]
  obtain ⟨φi, hφi⟩ := H (n i) (Nat.not_eq_zero_of_lt (h₁ i)) (Multiplicative.toAdd <| e a i) hi'
  simp only [ofAdd_toAdd] at hφi
  let x := φi.comp (Pi.evalMonoidHom (fun (i : ι) ↦ Multiplicative (ZMod (n i))) i)
  use x.comp e
  simpa only [coe_comp, coe_coe, Function.comp_apply, Pi.evalMonoidHom_apply, ne_eq, x]

lemma MonoidHom.exists_apply_ne_one_of_isCyclic (G R : Type*) [CommGroup G] [IsCyclic G]
    [Fintype G] [CommGroup R] ⦃ζ : R⦄ (hζ : IsPrimitiveRoot ζ (Fintype.card G)) ⦃a : G⦄
    (ha : a ≠ 1) :
    ∃ φ  : G →* R, φ a ≠ 1 := by
  -- pick a generator `g` of `G`
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hζg : orderOf ζ ∣ orderOf g := by
    rw [← hζ.eq_orderOf, orderOf_eq_card_of_forall_mem_zpowers hg]
  -- use the homomorphism `φ` given by `g ↦ ζ`
  let φ := monoidHomOfForallMemZpowers hg hζg
  have hφg : IsPrimitiveRoot (φ g) (Fintype.card G) := by
    rwa [monoidHomOfForallMemZpowers_apply_gen hg hζg]
  use φ
  contrapose! ha
  specialize hg a
  rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hg
  obtain ⟨k, hk⟩ := hg
  rw [← hk, map_pow] at ha
  obtain ⟨l, rfl⟩ := (hφg.pow_eq_one_iff_dvd k).mp ha
  rw [← hk, pow_mul, pow_card_eq_one, one_pow]

class HasAllRootsOfUnity (R : Type*) [CommRing R] [IsDomain R] where
  hasAllRootsOfUnity (n : ℕ) [NeZero n] : ∃ ζ : R, IsPrimitiveRoot ζ n

lemma HasAllRootsOfUnity.exists_prim_root (R : Type*) [CommRing R] [IsDomain R]
    [HasAllRootsOfUnity R] (n : ℕ) [NeZero n] :
    ∃ ζ : R, IsPrimitiveRoot ζ n :=
  HasAllRootsOfUnity.hasAllRootsOfUnity n

namespace IsAlgClosed

lemma exists_primitiveRoot (F : Type*) [Field F] [IsAlgClosed F] [CharZero F] (n : ℕ) [NeZero n] :
    ∃ ζ : F, IsPrimitiveRoot ζ n :=
  have : (⟨n, Nat.pos_of_ne_zero <| NeZero.ne n⟩ : ℕ+) = n := rfl
  this ▸ IsCyclotomicExtension.exists_prim_root F rfl

instance hasAllRootsOfUnity (F : Type*) [Field F] [IsAlgClosed F] [CharZero F] :
    HasAllRootsOfUnity F where
  hasAllRootsOfUnity n inst :=
    have : NeZero n := inst
    have : (⟨n, Nat.pos_of_ne_zero <| NeZero.ne n⟩ : ℕ+) = n := rfl
    this ▸ IsCyclotomicExtension.exists_prim_root F rfl

end IsAlgClosed

lemma exists_monoidHom_apply_ne_one (R : Type*) [CommRing R] [IsDomain R] [HasAllRootsOfUnity R]
    (n : ℕ) [NeZero n] {a : ZMod n} (ha : a ≠ 0) :
    ∃ φ : Multiplicative (ZMod n) →* Rˣ, φ (Multiplicative.ofAdd a) ≠ 1 := by
  have hn : n ≠ 0 := NeZero.ne n
  obtain ⟨ζ, hζ⟩ := HasAllRootsOfUnity.exists_prim_root R n
  let nn : ℕ+ := ⟨n, Nat.pos_of_ne_zero hn⟩
  have hnn : nn = n := rfl
  let ζ' := (hnn ▸ hζ).toRootsOfUnity.1 -- `ζ` as a unit
  have hζ' : IsPrimitiveRoot ζ' n := IsPrimitiveRoot.coe_units_iff.mp hζ
  have hc : Fintype.card (Multiplicative (ZMod n)) = n := by
    simp only [Fintype.card_multiplicative, ZMod.card]
  exact MonoidHom.exists_apply_ne_one_of_isCyclic (Multiplicative (ZMod n)) Rˣ (hc ▸ hζ') <|
    by simp only [ne_eq, ofAdd_eq_one, ha, not_false_eq_true]

/-- If `G` is a finite commutative group and `R` is a ring with all roots of unity,
then for each `a ≠ 1` in `G`, there exists a group homomorphism
`φ : G → Rˣ` such that `φ a ≠ 1`. -/
theorem MonoidHom.exists_apply_ne_one_of_hasAllRootsOfUnity (G R : Type*) [CommGroup G] [Finite G]
    [CommRing R] [IsDomain R] [HasAllRootsOfUnity R] {a : G} (ha : a ≠ 1) :
    ∃ φ : G →* Rˣ, φ a ≠ 1 :=
  exists_apply_ne_one G Rˣ
    (fun n hn _ ↦ have : NeZero n := ⟨hn⟩; exists_monoidHom_apply_ne_one R n) ha

/-- The canonical isomorphism from the `n`th roots of unity im `Mˣ`
to the `n`th roots of unity in `M`. -/
def rootsOfUnityUnitsMulEquiv (M : Type*) [CommMonoid M] (n : ℕ+) :
    rootsOfUnity n Mˣ ≃* rootsOfUnity n M where
      toFun ζ := ⟨ζ.val, (mem_rootsOfUnity ..).mpr <| (mem_rootsOfUnity' ..).mp ζ.prop⟩
      invFun ζ := ⟨toUnits ζ.val, by
        simp only [mem_rootsOfUnity, ← map_pow, MulEquivClass.map_eq_one_iff]
        exact (mem_rootsOfUnity ..).mp ζ.prop⟩
      left_inv ζ := by simp only [toUnits_val_apply, Subtype.coe_eta]
      right_inv ζ := by simp only [val_toUnits_apply, Subtype.coe_eta]
      map_mul' ζ ζ' := by simp only [Subgroup.coe_mul, Units.val_mul, MulMemClass.mk_mul_mk]

/-- The group of group homomorphims from a finite cyclic group `G` of order `n` into the
group of units of a ring `R` with all roots of unity is isomorphic to `G` -/
lemma CommGroup.monoidHom_equiv_self_of_isCyclic (G R : Type*) [CommGroup G] [Finite G]
    [IsCyclic G] [CommRing R] [IsDomain R] [HasAllRootsOfUnity R] :
    Nonempty ((G →* Rˣ) ≃* G) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  let n : ℕ+ := ⟨Fintype.card G, Fintype.card_pos⟩
  let e := (IsCyclic.monoidHom_mulEquiv_rootsOfUnity G Rˣ).some
  have hcyc := rootsOfUnity.isCyclic R n
  have hord : Fintype.card (rootsOfUnity n R) = Fintype.card G := by
    obtain ⟨ζ, hζ⟩ := HasAllRootsOfUnity.exists_prim_root R (Fintype.card G)
    have hζ' : IsPrimitiveRoot ζ n := by
      simp only [PNat.mk_coe, hζ, n]
    exact hζ'.card_rootsOfUnity
  simp only [← Nat.card_eq_fintype_card] at hord
  let e' := mulEquivOfCyclicCardEq hord
  let e'' := rootsOfUnityUnitsMulEquiv R n
  exact ⟨(e.trans e'').trans e'⟩

/-- The canonical isomoorphism between the monoid of homomorphisms from a finite product of
commutative monoids to another commutative monoid and the product of the homomrphism monoids. -/
def Pi.monoidHomMulEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ι → Type*)
    [(i : ι) → CommMonoid (M i)] (M' : Type*) [CommMonoid M'] :
    (((i : ι) → M i) →* M') ≃* ((i : ι) → (M i →* M')) where
      toFun φ i := φ.comp <| MonoidHom.mulSingle M i
      invFun φ := ∏ (i : ι), (φ i).comp (Pi.evalMonoidHom M i)
      left_inv φ := by
        ext
        simp only [MonoidHom.finset_prod_apply, MonoidHom.coe_comp, Function.comp_apply,
          evalMonoidHom_apply, MonoidHom.mulSingle_apply, ← map_prod]
        refine congrArg _ ?_
        ext1
        rw [Fintype.prod_apply]
        exact Fintype.prod_pi_mulSingle ..
      right_inv φ := by
        ext i m
        simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mulSingle_apply,
          MonoidHom.finset_prod_apply, evalMonoidHom_apply, ]
        let φ' i : M i → M' := ⇑(φ i)
        conv =>
          enter [1, 2, j]
          rw [show φ j = φ' j from rfl, Pi.apply_mulSingle φ' (fun i ↦ map_one (φ i))]
        rw [show φ' i = φ i from rfl]
        exact Fintype.prod_pi_mulSingle' ..
      map_mul' φ ψ := by
        ext
        simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mulSingle_apply,
          MonoidHom.mul_apply, mul_apply]

/-- A finite commutative group `G` is (noncanonically) isomorphic to the group `G →* Rˣ`
of `R`-valued characters when `R` is a ring that has all roots of unity. -/
theorem CommGroup.monoidHom_equiv_self_of_hasAllRootsOfUnity (G R : Type*) [CommGroup G] [Finite G]
    [CommRing R] [IsDomain R] [HasAllRootsOfUnity R] :
    Nonempty (G ≃* (G →* Rˣ)) := by
  classical
  obtain ⟨ι, _, n, ⟨h₁, h₂⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod G
  let e := h₂.some
  let e' := Pi.monoidHomMulEquiv (fun i ↦ Multiplicative (ZMod (n i))) Rˣ
  let e'' := MulEquiv.monoidHomCongr e (MulEquiv.refl Rˣ)
  have : ∀ i, NeZero (n i) := fun i ↦ NeZero.of_gt (h₁ i)
  let E i := (CommGroup.monoidHom_equiv_self_of_isCyclic (Multiplicative (ZMod (n i))) R).some
  let E' := MulEquiv.piCongrRight E
  exact ⟨e.trans E'.symm|>.trans e'.symm|>.trans e''.symm⟩

namespace MulChar

instance finite (M R : Type*) [CommMonoid M] [Fintype Mˣ] [DecidableEq M] [CommRing R]
    [IsDomain R] :
    Finite (MulChar M R) := by
  have : Finite (Mˣ →* Rˣ) := by
    let S := rootsOfUnity ⟨Fintype.card Mˣ, Fintype.card_pos⟩ R
    let F := Mˣ →* S
    have fF : Finite F :=
      Finite.of_injective (fun f : F ↦ (f : Mˣ → S)) DFunLike.coe_injective
    refine Finite.of_surjective (fun f : F ↦ (Subgroup.subtype _).comp f) (fun f ↦ ?_)
    have H (a : Mˣ) : f a ∈ S := by
      simp only [mem_rootsOfUnity, PNat.mk_coe, ← map_pow, pow_card_eq_one, map_one, S]
    use MonoidHom.codRestrict f S H
    ext
    simp only [MonoidHom.coe_comp, Subgroup.coeSubtype, Function.comp_apply,
      MonoidHom.codRestrict_apply]
  exact Finite.of_equiv _ MulChar.equivToUnitHom.symm

noncomputable instance fintype (M R : Type*) [CommMonoid M] [Fintype M] [DecidableEq M]
    [CommRing R] [IsDomain R] :
    Fintype (MulChar M R) := Fintype.ofFinite _

lemma exists_apply_ne_one_iff_exists_monoidHom {M R : Type*} [CommMonoid M]
    [Fintype M] [DecidableEq M] [CommRing R] (a : Mˣ) :
    (∃ χ : MulChar M R, χ a ≠ 1) ↔ ∃ φ : Mˣ →* Rˣ, φ a ≠ 1 := by
  refine ⟨fun ⟨χ, hχ⟩ ↦ ⟨χ.toUnitHom, ?_⟩, fun ⟨φ, hφ⟩ ↦ ⟨ofUnitHom φ, ?_⟩⟩
  · contrapose! hχ
    rwa [Units.ext_iff, show χ.toUnitHom a = χ a from rfl] at hχ
  · contrapose! hφ
    simpa only [ofUnitHom_eq, equivToUnitHom_symm_coe, Units.val_eq_one] using hφ

/-- If `M` is a finite commutative monoid and `R` is a ring that has all roots of unity,
then for each `a ≠ 1` in `M`, there exists a multiplicative
character `χ : M → R` such that `χ a ≠ 1`. -/
theorem exists_apply_ne_one_of_hasAllRootsOfUnity (M R : Type*) [CommMonoid M] [Fintype M]
    [DecidableEq M] [CommRing R] [IsDomain R] [HasAllRootsOfUnity R] {a : M} (ha : a ≠ 1) :
    ∃ χ : MulChar M R, χ a ≠ 1 := by
  by_cases hu : IsUnit a
  . let a' : Mˣ := hu.unit -- `a` as a unit
    have ha' : a = a' := rfl
    refine (exists_apply_ne_one_iff_exists_monoidHom (R := R) a').mpr ?_
    refine MonoidHom.exists_apply_ne_one_of_hasAllRootsOfUnity Mˣ R ?_
    contrapose! ha
    rw [ha', ha, Units.val_eq_one]
  · use 1
    rw [map_nonunit _ hu]
    exact zero_ne_one

/-- The cardinality of the group of `R` valued multiplicative characters on a finite commutative
monoid `M` is the same as that of its unit group `Mˣ` when `R` is a ring that has all roots
of unity. -/
lemma card_mulChar_eq_card_units_of_hasAllRootsOfUnity (M R : Type*) [CommMonoid M] [Fintype M]
    [DecidableEq M] [CommRing R] [IsDomain R] [HasAllRootsOfUnity R] :
    Fintype.card (MulChar M R) = Fintype.card Mˣ := by
  let e := (CommGroup.monoidHom_equiv_self_of_hasAllRootsOfUnity Mˣ R).some.toEquiv
  have : Finite (Mˣ →* Rˣ) := Finite.of_equiv _ e
  have : Fintype (Mˣ →* Rˣ) := Fintype.ofFinite (Mˣ →* Rˣ)
  exact (Fintype.card_congr <| MulChar.equivToUnitHom (R := M) (R' := R)).trans (Fintype.card_congr e).symm

end MulChar

namespace ZMod

instance units_fintype (n : ℕ) : Fintype (ZMod n)ˣ := by
  match n with
  | 0 =>     exact UnitsInt.fintype
  | m + 1 => infer_instance

end ZMod

namespace DirichletCharacter

section general

variable {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]

instance finite : Finite (DirichletCharacter R n) := MulChar.finite ..

noncomputable instance fintype : Fintype (DirichletCharacter R n) := Fintype.ofFinite _

noncomputable
instance inhabited : Inhabited (DirichletCharacter R n) where
  default := 1

lemma sum_characters_eq_zero_aux {a : ZMod n} (h : ∃ χ : DirichletCharacter R n, χ a ≠ 1) :
    ∑ χ : DirichletCharacter R n, χ a = 0 := by
  obtain ⟨χ, hχ⟩ := h
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  refine Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ (fun χ' ↦ ?_)
  simp only [MulChar.coeToFun_mul, Pi.mul_apply]

lemma sum_characters_eq_zero_iff {a : ZMod n} [CharZero R]
    (h : ∀ a : ZMod n, a ≠ 1 → ∃ χ : DirichletCharacter R n, χ a ≠ 1) :
    ∑ χ : DirichletCharacter R n, χ a = 0 ↔ a ≠ 1 := by
  refine ⟨fun H ha ↦ ?_, fun H ↦ sum_characters_eq_zero_aux <| h a H⟩
  simp only [ha, isUnit_one, not_true_eq_false, map_one, Finset.sum_const, nsmul_eq_mul, mul_one,
    Nat.cast_eq_zero, Finset.card_eq_zero, Finset.univ_eq_empty_iff] at H
  exact (not_isEmpty_of_nonempty <| DirichletCharacter R n) H

end general

variable {R : Type*} [CommRing R] [IsDomain R] [HasAllRootsOfUnity R] {n : ℕ} [NeZero n]

variable (n) in
/-- There are `φ(n)` Dirichlet characters mod `n` with values in a ring that has all
roots of unity. -/
lemma card_eq_totient_of_hasAllRootsOfUnity :
    Fintype.card (DirichletCharacter R n) = n.totient := by
  rw [← ZMod.card_units_eq_totient n]
  convert MulChar.card_mulChar_eq_card_units_of_hasAllRootsOfUnity (ZMod n) R

/-- If `R` is a ring that has all roots of unity and `n ≠ 0`, then for each
`a ≠ 1` in `ZMod n`, there exists a Dirichlet character `χ` mod `n` wiht values in `R`
such that `χ a ≠ 1`. -/
theorem exists_apply_ne_one_of_hasAllRootsOfUnity ⦃a : ZMod n⦄ (ha : a ≠ 1) :
    ∃ χ : DirichletCharacter R n, χ a ≠ 1 :=
  MulChar.exists_apply_ne_one_of_hasAllRootsOfUnity (ZMod n) R ha

/-- If `R` is ring that has all roots of unity and `n ≠ 0`, then for each
`a ≠ 1` in `ZMod n`, the sum of `χ a` over all Dirichlet characters mod `n` with values
in `R` vanishes. -/
theorem sum_characters_eq_zero ⦃a : ZMod n⦄ (ha : a ≠ 1) :
    ∑ χ : DirichletCharacter R n, χ a = 0 :=
  sum_characters_eq_zero_aux <| exists_apply_ne_one_of_hasAllRootsOfUnity ha

/-- If `R` is ring that has all roots of unity and `n ≠ 0`, then for
`a` in `ZMod n`, the sum of `χ a` over all Dirichlet characters mod `n` with values
in `R` vanishes if `a ≠ 1` and has the value `φ(n)` if `a = 1`. -/
theorem sum_characters_eq (a : ZMod n) :
    ∑ χ : DirichletCharacter R n, χ a = if a = 1 then (n.totient : R) else 0 := by
  split_ifs with ha
  · simpa only [ha, map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      using congrArg Nat.cast <| card_eq_totient_of_hasAllRootsOfUnity n
  · exact sum_characters_eq_zero ha

/-- If `R` is ring that has all roots of unity and `n ≠ 0`, then for `a` and `b`
in `ZMod n` with `a` a unit, the sum of `χ a⁻¹ * χ b` over all Dirichlet characters
mod `n` with values in `R` vanihses if `a ≠ b` and has the value `φ(n)` if `a = b`. -/
theorem sum_char_inv_mul_char_eq {a : ZMod n} (ha : IsUnit a) (b : ZMod n) :
    ∑ χ : DirichletCharacter R n, χ a⁻¹ * χ b = if a = b then n.totient else 0 := by
  convert sum_characters_eq (a⁻¹ * b) using 2 with χ
  · rw [map_mul]
  · simp only [Nat.cast_ite, Nat.cast_zero]
    refine ite_congr (eq_iff_iff.mpr ⟨fun H ↦ ?_, fun H ↦ ?_⟩) (fun _ ↦ rfl) (fun _ ↦ rfl)
    · rw [← H, a.inv_mul_of_unit ha]
    · apply_fun (a * ·) at H
      rwa [← mul_assoc, a.mul_inv_of_unit ha, one_mul, mul_one, eq_comm] at H
  · infer_instance

end DirichletCharacter
