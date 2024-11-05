import Mathlib.GroupTheory.FiniteAbelian
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
### Auxiliary results
-/

-- [Mathlib.RingTheory.RootsOfUnity.Basic] ?
/-- The canonical isomorphism from the `n`th roots of unity in`Mˣ`
to the `n`th roots of unity in `M`. -/
def rootsOfUnityUnitsMulEquiv (M : Type*) [CommMonoid M] (n : ℕ) :
    rootsOfUnity n Mˣ ≃* rootsOfUnity n M where
      toFun ζ := ⟨ζ.val, (mem_rootsOfUnity ..).mpr <| (mem_rootsOfUnity' ..).mp ζ.prop⟩
      invFun ζ := ⟨toUnits ζ.val, by
        simp only [mem_rootsOfUnity, ← map_pow, MulEquivClass.map_eq_one_iff]
        exact (mem_rootsOfUnity ..).mp ζ.prop⟩
      left_inv ζ := by simp only [toUnits_val_apply, Subtype.coe_eta]
      right_inv ζ := by simp only [val_toUnits_apply, Subtype.coe_eta]
      map_mul' ζ ζ' := by simp only [Subgroup.coe_mul, Units.val_mul, MulMemClass.mk_mul_mk]

-- [Mathlib.Algebra.BigOperators.Group.Finset] ?
/-- The canonical isomoorphism between the monoid of homomorphisms from a finite product of
commutative monoids to another commutative monoid and the product of the homomorphism monoids. -/
@[to_additive]
def Pi.monoidHomMulEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ι → Type*)
    [(i : ι) → CommMonoid (M i)] (M' : Type*) [CommMonoid M'] :
    (((i : ι) → M i) →* M') ≃* ((i : ι) → (M i →* M')) where
      toFun φ i := φ.comp <| MonoidHom.mulSingle M i
      invFun φ := ∏ (i : ι), (φ i).comp (Pi.evalMonoidHom M i)
      left_inv φ := by
        ext
        simp only [MonoidHom.finset_prod_apply, MonoidHom.coe_comp, Function.comp_apply,
          evalMonoidHom_apply, MonoidHom.mulSingle_apply, ← map_prod]
        refine congrArg _ <| funext fun _ ↦ ?_
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

lemma Pi.mulSingle_multiplicativeOfAdd_eq {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [(i : ι) → AddMonoid (M i)] (i : ι) (a : M i) (j : ι) :
    Pi.mulSingle (f := fun i ↦ Multiplicative (M i)) i (Multiplicative.ofAdd a) j =
      Multiplicative.ofAdd ((Pi.single i a) j) := by
  rcases eq_or_ne j i with rfl | h
  · simp only [mulSingle_eq_same, single_eq_same]
  · simp only [mulSingle, ne_eq, h, not_false_eq_true, Function.update_noteq, one_apply, single,
      zero_apply, ofAdd_zero]

lemma Pi.single_additiveOfMul_eq {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [(i : ι) → Monoid (M i)] (i : ι) (a : M i) (j : ι) :
    Pi.single (f := fun i ↦ Additive (M i)) i (Additive.ofMul a) j =
      Additive.ofMul ((Pi.mulSingle i a) j) := by
  rcases eq_or_ne j i with rfl | h
  · simp only [mulSingle_eq_same, single_eq_same]
  · simp only [single, ne_eq, h, not_false_eq_true, Function.update_noteq, zero_apply, mulSingle,
      one_apply, ofMul_one]

@[to_additive]
lemma orderOf_piMulSingle {ι : Type*} [DecidableEq ι] {M : ι → Type*} [(i : ι) → Monoid (M i)]
    (i : ι) (g : M i) :
    orderOf (Pi.mulSingle i g) = orderOf g := by
  rcases Nat.eq_zero_or_pos (orderOf g) with hg | hg
  · rw [hg]
    rw [orderOf_eq_zero_iff] at hg ⊢
    contrapose! hg
    simpa only [Pi.evalMonoidHom_apply, Pi.mulSingle_eq_same]
      using MonoidHom.isOfFinOrder (Pi.evalMonoidHom _ i) hg
  · rw [orderOf_eq_iff hg]
    refine ⟨funext fun j ↦ ?_, fun m hm₁ hm₂ H ↦ ?_⟩
    · simp only [Pi.pow_apply, Pi.one_apply]
      rcases eq_or_ne j i with rfl | hij
      · simp only [Pi.mulSingle_eq_same, pow_orderOf_eq_one]
      · simp only [ne_eq, hij, not_false_eq_true, Pi.mulSingle_eq_of_ne, one_pow]
    · apply_fun (· i) at H
      simp only [Pi.pow_apply, Pi.mulSingle_eq_same, Pi.one_apply] at H
      exact pow_ne_one_of_lt_orderOf hm₂.ne' hm₁ H

@[to_additive]
lemma Subgroup.isCyclic_of_le {G : Type*} [Group G] {H H' : Subgroup G} (h : H ≤ H')
    [IsCyclic H'] :
    IsCyclic H := by
  let e := Subgroup.subgroupOfEquivOfLe h
  obtain ⟨g, hg⟩ := Subgroup.isCyclic <| H.subgroupOf H'
  refine ⟨e g, fun x ↦ ?_⟩
  obtain ⟨n, hn⟩ := hg (e.symm x)
  exact ⟨n, by simp only at hn ⊢; rw [← map_zpow, hn, MulEquiv.apply_symm_apply]⟩

instance Monoid.neZero_exponent_of_finite {G : Type u} [LeftCancelMonoid G] [Finite G] :
    NeZero <| Monoid.exponent G :=
  ⟨Monoid.exponent_ne_zero_of_finite⟩

instance Nat.neZero_totient {n : ℕ} [NeZero n] : NeZero n.totient :=
  ⟨(Nat.totient_pos.mpr <| NeZero.pos n).ne'⟩

/-!
### Commutative monoids that have enough roots of unity
-/

/-- This is a type class recording that a commutative monoid `M` contains primitive `n`th
roots of unity and such that the group of `n`th roots of unity is cyclic.

Such monoids are suitable targets in the context of duality statements for groups
of exponent `n`. -/
class HasEnoughRootsOfUnity (M : Type*) [CommMonoid M] (n : ℕ) where
  prim : ∃ m : M, IsPrimitiveRoot m n
  cyc : IsCyclic <| rootsOfUnity n M

namespace HasEnoughRootsOfUnity

lemma exists_primitiveRoot (M : Type*) [CommMonoid M] (n : ℕ) [HasEnoughRootsOfUnity M n] :
    ∃ ζ : M, IsPrimitiveRoot ζ n :=
  HasEnoughRootsOfUnity.prim

instance rootsOfUnity_isCyclic (M : Type*) [CommMonoid M] (n : ℕ) [HasEnoughRootsOfUnity M n] :
    IsCyclic (rootsOfUnity n M) :=
  HasEnoughRootsOfUnity.cyc

/-- If `HasEnoughRootsOfUnity M n` and `m ∣ n`, then also `HasEnoughRootsOfUnity M m`. -/
lemma of_dvd (M : Type*) [CommMonoid M] {m n : ℕ} [NeZero n] (hmn : m ∣ n)
    [HasEnoughRootsOfUnity M n] :
    HasEnoughRootsOfUnity M m where
  prim :=
    have ⟨ζ, hζ⟩ := exists_primitiveRoot M n
    have ⟨k, hk⟩ := hmn
    ⟨ζ ^ k, IsPrimitiveRoot.pow (NeZero.pos n) hζ (mul_comm m k ▸ hk)⟩
  cyc := Subgroup.isCyclic_of_le <| rootsOfUnity_le_of_dvd hmn

/-- If `M` satisfies `HasEnoughRootsOfUnity`, then the group of `n`th roots of unity
in `M` is finite. -/
instance finite_rootsOfUnity (M : Type*) [CommMonoid M] (n : ℕ) [NeZero n]
    [HasEnoughRootsOfUnity M n] :
    Finite <| rootsOfUnity n M := by
  have := rootsOfUnity_isCyclic M n
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity n M)
  have hg' : g ^ n = 1 := OneMemClass.coe_eq_one.mp g.prop
  let f (j : ZMod n) : rootsOfUnity n M := g ^ (j.val : ℤ)
  refine Finite.of_surjective f fun x ↦ ?_
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp <| hg x
  refine ⟨k, ?_⟩
  simp only [ZMod.natCast_val, ← hk, f, ZMod.coe_intCast]
  exact (zpow_eq_zpow_emod' k hg').symm

/-- If `M` satisfies `HasEnoughRootsOfUnity`, then the group of `n`th roots of unity
in `M` (is cyclic and) has order `n`. -/
lemma natCard_rootsOfUnity (M : Type*) [CommMonoid M] (n : ℕ) [NeZero n]
    [HasEnoughRootsOfUnity M n] :
    Nat.card (rootsOfUnity n M) = n := by
  obtain ⟨ζ, h⟩ := exists_primitiveRoot M n
  have : Fintype <| rootsOfUnity n M := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, ← IsCyclic.exponent_eq_card]
  refine dvd_antisymm ?_ ?_
  · exact Monoid.exponent_dvd_of_forall_pow_eq_one fun g ↦ OneMemClass.coe_eq_one.mp g.prop
  · nth_rewrite 1 [h.eq_orderOf]
    rw [← (h.isUnit <| NeZero.pos n).unit_spec, orderOf_units]
    let ζ' : rootsOfUnity n M := ⟨(h.isUnit <| NeZero.pos n).unit, ?_⟩
    · rw [← Subgroup.orderOf_mk]
      exact Monoid.order_dvd_exponent ζ'
    simp only [mem_rootsOfUnity, PNat.mk_coe]
    rw [← Units.eq_iff, Units.val_pow_eq_pow_val, IsUnit.unit_spec, h.pow_eq_one, Units.val_one]

end HasEnoughRootsOfUnity

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
### The multiplicative version of the classification theorem for finite abelian groups
-/

-- [Mathlib.Algebra.DirectSum.Basic] ?
/-- The canonical isomorphism of a finite direct sum of additive commutative monoids
and the corresponding finite product. -/
def DirectSum.addEquivProd {ι : Type*} [Fintype ι] (G : ι → Type*) [(i : ι) → AddCommMonoid (G i)] :
    DirectSum ι G ≃+ ((i : ι) → G i) :=
  ⟨DFinsupp.equivFunOnFintype, fun g h ↦ funext fun _ ↦ by
    simp only [DFinsupp.equivFunOnFintype, Equiv.toFun_as_coe, Equiv.coe_fn_mk, add_apply,
      Pi.add_apply]⟩

/-- The **Classification Theorem For Finite Abelian Groups** in a multiplicative version:
A finite commutative group `G` is isomorphic to a finite product of finite cyclic groups. -/
theorem CommGroup.equiv_prod_multiplicative_zmod (G : Type*) [CommGroup G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ),
       (∀ (i : ι), 1 < n i) ∧ Nonempty (G ≃* ((i : ι) → Multiplicative (ZMod (n i)))) := by
  obtain ⟨ι, inst, n, h₁, h₂⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' (Additive G)
  exact ⟨ι, inst, n, h₁, ⟨MulEquiv.toAdditive.symm <| h₂.some.trans <|
    (DirectSum.addEquivProd _).trans <| MulEquiv.toAdditive'' <| MulEquiv.piMultiplicative _⟩⟩

/-!
### Results specific for cyclic groups
-/

namespace IsCyclic

/-- The isomorphism from the group of group homomorphisms from a finite cyclic group `G` of order
`n` into another group `G'` to the group of `n`th roots of unity in `G'` determined by a generator
`g` of `G`. It sends `φ : G →* G'` to `φ g`. -/
noncomputable
def monoidHomMulEquivRootsOfUnityOfGenerator {G : Type*} [CommGroup G] [Fintype G] {g : G}
    (hg : ∀ (x : G), x ∈ Subgroup.zpowers g) (G' : Type*) [CommGroup G'] :
    (G →* G') ≃* rootsOfUnity (Fintype.card G) G' where
  toFun φ := ⟨(IsUnit.map φ <| Group.isUnit g).unit, by
    simp only [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, IsUnit.unit_spec,
      ← map_pow, pow_card_eq_one, map_one, Units.val_one]⟩
  invFun ζ := monoidHomOfForallMemZpowers hg (g' := (ζ.val : G')) <| by
    simpa only [orderOf_eq_card_of_forall_mem_zpowers hg, orderOf_dvd_iff_pow_eq_one,
      ← Units.val_pow_eq_pow_val, Units.val_eq_one] using ζ.prop
  left_inv φ := (MonoidHom.eq_iff_eq_on_generator hg _ φ).mpr <| by
    simp only [IsUnit.unit_spec, monoidHomOfForallMemZpowers_apply_gen]
  right_inv φ := Subtype.ext <| by
    simp only [monoidHomOfForallMemZpowers_apply_gen, IsUnit.unit_of_val_units]
  map_mul' x y := by
    simp only [MonoidHom.mul_apply, MulMemClass.mk_mul_mk, Subtype.mk.injEq, Units.ext_iff,
      IsUnit.unit_spec, Units.val_mul]

/-- The group of group homomorphisms from a finite cyclic group `G` of order `n` into another
group `G'` is (noncanonically) isomorphic to the group of `n`th roots of unity in `G'`. -/
lemma monoidHom_mulEquiv_rootsOfUnity (G : Type*) [CommGroup G] [Finite G] [IsCyclic G]
    (G' : Type*) [CommGroup G'] :
    Nonempty <| (G →* G') ≃* rootsOfUnity (Nat.card G) G' := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have : Fintype G := Fintype.ofFinite _
  exact ⟨Nat.card_eq_fintype_card (α  := G) ▸ monoidHomMulEquivRootsOfUnityOfGenerator hg G'⟩

/-- If `G` is cyclic of order `n` and `G'` contains a primitive `n`th root of unity,
then for each `a : G` with `a ≠ 1` there is a homomorphism `φ : G →* G'` such that `φ a ≠ 1`. -/
lemma exists_apply_ne_one {G G' : Type*} [CommGroup G] [IsCyclic G] [Finite G] [CommGroup G']
    (hG' : ∃ ζ : G', IsPrimitiveRoot ζ (Nat.card G)) ⦃a : G⦄ (ha : a ≠ 1) :
    ∃ φ  : G →* G', φ a ≠ 1 := by
  let inst : Fintype G := Fintype.ofFinite _
  obtain ⟨ζ, hζ⟩ := hG'
  -- pick a generator `g` of `G`
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hζg : orderOf ζ ∣ orderOf g := by
    rw [← hζ.eq_orderOf, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  -- use the homomorphism `φ` given by `g ↦ ζ`
  let φ := monoidHomOfForallMemZpowers hg hζg
  have hφg : IsPrimitiveRoot (φ g) (Nat.card G) := by
    rwa [monoidHomOfForallMemZpowers_apply_gen hg hζg]
  use φ
  contrapose! ha
  specialize hg a
  rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hg
  obtain ⟨k, hk⟩ := hg
  rw [← hk, map_pow] at ha
  obtain ⟨l, rfl⟩ := (hφg.pow_eq_one_iff_dvd k).mp ha
  rw [← hk, pow_mul, Nat.card_eq_fintype_card, pow_card_eq_one, one_pow]

/-- The group of group homomorphims from a finite cyclic group `G` of order `n` into the
group of units of a ring `M` with all roots of unity is isomorphic to `G` -/
lemma monoidHom_equiv_self (G M : Type*) [CommGroup G] [Finite G]
    [IsCyclic G] [CommMonoid M] [HasEnoughRootsOfUnity M (Nat.card G)] :
    Nonempty ((G →* Mˣ) ≃* G) := by
  have : Fintype G := Fintype.ofFinite G
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  have hord := HasEnoughRootsOfUnity.natCard_rootsOfUnity M (Nat.card G)
  let e := (IsCyclic.monoidHom_mulEquiv_rootsOfUnity G Mˣ).some
  exact ⟨e.trans (rootsOfUnityUnitsMulEquiv M (Nat.card G)) |>.trans (mulEquivOfCyclicCardEq hord)⟩

end IsCyclic

/-- If `M` is a commutative group that contains a primitive `n`th root of unity
and `a : ZMod n` is nonzero, then there exists a group homomorphism `φ` from the
additive group `ZMod n` to the multiplicative group `Mˣ` such that `φ a ≠ 1`. -/
lemma ZMod.exists_monoidHom_apply_ne_one {M : Type*} [CommMonoid M] {n : ℕ} [NeZero n]
    (hG : ∃ ζ : M, IsPrimitiveRoot ζ n) {a : ZMod n} (ha : a ≠ 0) :
    ∃ φ : Multiplicative (ZMod n) →* Mˣ, φ (Multiplicative.ofAdd a) ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := hG
  have hc : n = Nat.card (Multiplicative (ZMod n)) := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, card]
  exact IsCyclic.exists_apply_ne_one
    (hc ▸ ⟨hζ.toRootsOfUnity.val, IsPrimitiveRoot.coe_units_iff.mp hζ⟩) <|
    by simp only [ne_eq, ofAdd_eq_one, ha, not_false_eq_true]

/-!
### Results for general finite abelian groups
-/

namespace CommGroup

open MonoidHom

private
lemma dvd_exponent {ι G : Type*} [Fintype ι] [CommGroup G] {n : ι → ℕ}
    (e : G ≃* ((i : ι) → Multiplicative (ZMod (n i)))) (i : ι) :
  n i ∣ Monoid.exponent G := by
  classical
  have : n i = orderOf (e.symm <| Pi.mulSingle i <| Multiplicative.ofAdd 1) := by
    rw [MulEquiv.orderOf_eq, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf]
    exact (ZMod.addOrderOf_one (n i)).symm
  exact this ▸ Monoid.order_dvd_exponent _

private
lemma exists_apply_ne_one_aux (G M : Type*) [CommGroup G] [Finite G] [CommMonoid M]
    (H : ∀ n : ℕ, n ∣ Monoid.exponent G → ∀ a : ZMod n, a ≠ 0 →
       ∃ φ : Multiplicative (ZMod n) →* M, φ (Multiplicative.ofAdd a) ≠ 1)
    {a : G} (ha : a ≠ 1) :
    ∃ φ : G →* M, φ a ≠ 1 := by
  obtain ⟨ι, _, n, _, h⟩ := CommGroup.equiv_prod_multiplicative_zmod G
  let e := h.some
  obtain ⟨i, hi⟩ : ∃ i : ι, e a i ≠ 1 := by
    contrapose! ha
    suffices e a = 1 from (MulEquiv.map_eq_one_iff e).mp this
    exact funext ha
  have hi : Multiplicative.toAdd (e a i) ≠ 0 := by
    simp only [ne_eq, toAdd_eq_zero, hi, not_false_eq_true]
  obtain ⟨φi, hφi⟩ := H (n i) (dvd_exponent e i) (Multiplicative.toAdd <| e a i) hi
  simp only [ofAdd_toAdd] at hφi
  let x := φi.comp (Pi.evalMonoidHom (fun (i : ι) ↦ Multiplicative (ZMod (n i))) i)
  use x.comp e
  simpa only [coe_comp, coe_coe, Function.comp_apply, Pi.evalMonoidHom_apply, ne_eq, x]

/-- If `G` is a finite commutative group of exponent `n` and `M` is a commutative monoid
with cyclic `n`-torsion of order `n`, then for each `a ≠ 1` in `G`, there exists a
group homomorphism `φ : G → Mˣ` such that `φ a ≠ 1`. -/
theorem exists_apply_ne_one_of_hasEnoughRootsOfUnity (G M : Type*) [CommGroup G] [Finite G]
    [CommMonoid M] [HasEnoughRootsOfUnity M (Monoid.exponent G)] {a : G} (ha : a ≠ 1) :
    ∃ φ : G →* Mˣ, φ a ≠ 1 := by
  refine exists_apply_ne_one_aux G Mˣ (fun n hn a ha₀ ↦ ?_) ha
  have : NeZero n := ⟨fun H ↦ NeZero.ne _ <| Nat.eq_zero_of_zero_dvd (H ▸ hn)⟩
  refine ZMod.exists_monoidHom_apply_ne_one ?_ ha₀
  have : HasEnoughRootsOfUnity M n := HasEnoughRootsOfUnity.of_dvd M hn
  exact HasEnoughRootsOfUnity.exists_primitiveRoot M n

/-- A finite commutative group `G` is (noncanonically) isomorphic to the group `G →* Mˣ`
of `M`-valued characters when `M` is a commutative monoid with cyclic `n`-torsion of order `n`,
where `n` is the exponent of `G`. -/
theorem monoidHom_mulEquiv_self_of_hasEnoughRootsOfUnity (G M : Type*) [CommGroup G] [Finite G]
    [CommMonoid M] [HasEnoughRootsOfUnity M (Monoid.exponent G)] :
    Nonempty (G ≃* (G →* Mˣ)) := by
  classical
  obtain ⟨ι, _, n, ⟨h₁, h₂⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod G
  let e := h₂.some
  let e' := Pi.monoidHomMulEquiv (fun i ↦ Multiplicative (ZMod (n i))) Mˣ
  let e'' := MulEquiv.monoidHomCongr e (MulEquiv.refl Mˣ)
  have : ∀ i, NeZero (n i) := fun i ↦ NeZero.of_gt (h₁ i)
  have inst i : HasEnoughRootsOfUnity M (Nat.card (Multiplicative (ZMod (n i)))) := by
    have hdvd : Nat.card (Multiplicative (ZMod (n i))) ∣ Monoid.exponent G := by
      convert dvd_exponent e i
      simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    exact HasEnoughRootsOfUnity.of_dvd M hdvd
  let E i := (IsCyclic.monoidHom_equiv_self (Multiplicative (ZMod (n i))) M).some
  let E' := MulEquiv.piCongrRight E
  exact ⟨e.trans E'.symm|>.trans e'.symm|>.trans e''.symm⟩

end CommGroup


/-!
### Results for multiplicative characters

We provide instances for `Finite (MulChar M R)` and `Fintype (MulChar M R)`
when `M` is a finite commutative monoid and `R` is an integral domain.

We also show that `MulChar M R` and `Mˣ` have the same cardinality when `R` has
all roots of unity.
-/

namespace MulChar

instance finite (M R : Type*) [CommMonoid M] [Fintype Mˣ] [DecidableEq M] [CommRing R]
    [IsDomain R] :
    Finite (MulChar M R) := by
  have : Finite (Mˣ →* Rˣ) := by
    let S := rootsOfUnity (Fintype.card Mˣ) R
    let F := Mˣ →* S
    have fF : Finite F := .of_injective (fun f ↦ (f : Mˣ → S)) DFunLike.coe_injective
    refine Finite.of_surjective (fun f : F ↦ (Subgroup.subtype _).comp f) (fun f ↦ ?_)
    have H (a : Mˣ) : f a ∈ S := by
      simp only [mem_rootsOfUnity, PNat.mk_coe, ← map_pow, pow_card_eq_one, map_one, S]
    use MonoidHom.codRestrict f S H
    ext1
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

/-- If `M` is a finite commutative monoid and `R` is a ring that has enough roots of unity,
then for each `a ≠ 1` in `M`, there exists a multiplicative character `χ : M → R` such that
`χ a ≠ 1`. -/
theorem exists_apply_ne_one_of_hasEnoughRootsOfUnity (M R : Type*) [CommMonoid M] [Fintype M]
    [DecidableEq M] [CommRing R] [Nontrivial R] [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)]
    {a : M} (ha : a ≠ 1) :
    ∃ χ : MulChar M R, χ a ≠ 1 := by
  by_cases hu : IsUnit a
  . let a' : Mˣ := hu.unit -- `a` as a unit
    have ha' : a = a' := rfl
    refine (exists_apply_ne_one_iff_exists_monoidHom (R := R) a').mpr ?_
    refine CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Mˣ R ?_
    contrapose! ha
    rw [ha', ha, Units.val_eq_one]
  · use 1
    rw [map_nonunit _ hu]
    exact zero_ne_one

/-- The cardinality of the group of `R` valued multiplicative characters on a finite commutative
monoid `M` is the same as that of its unit group `Mˣ` when `R` is a ring that has enough roots
of unity. -/
lemma card_eq_card_units_of_hasEnoughRootsOfUnity (M R : Type*) [CommMonoid M] [Fintype M]
    [DecidableEq M] [CommRing R] [IsDomain R] [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)] :
    Fintype.card (MulChar M R) = Fintype.card Mˣ :=
  let e := (CommGroup.monoidHom_mulEquiv_self_of_hasEnoughRootsOfUnity Mˣ R).some.toEquiv
  have : Finite (Mˣ →* Rˣ) := Finite.of_equiv _ e
  have : Fintype (Mˣ →* Rˣ) := Fintype.ofFinite (Mˣ →* Rˣ)
  (Fintype.card_congr <| MulChar.equivToUnitHom).trans (Fintype.card_congr e).symm

end MulChar


/-!
### Results for Dirichlet characters

The goal of this section is to show that `∑ χ : DirichletCharacter R n, χ a` vanishes
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
  letI : Fintype (ZMod n)ˣ := n.casesOn UnitsInt.fintype inferInstance
  MulChar.finite ..

noncomputable instance fintype : Fintype (DirichletCharacter R n) := Fintype.ofFinite _

lemma sum_characters_eq_zero_aux {a : ZMod n} (h : ∃ χ : DirichletCharacter R n, χ a ≠ 1) :
    ∑ χ : DirichletCharacter R n, χ a = 0 := by
  obtain ⟨χ, hχ⟩ := h
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  refine Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ (fun χ' ↦ ?_)
  simp only [MulChar.coeToFun_mul, Pi.mul_apply]

lemma sum_characters_eq_zero_iff_aux {a : ZMod n} [CharZero R]
    (h : ∀ a : ZMod n, a ≠ 1 → ∃ χ : DirichletCharacter R n, χ a ≠ 1) :
    ∑ χ : DirichletCharacter R n, χ a = 0 ↔ a ≠ 1 := by
  refine ⟨fun H ha ↦ ?_, fun H ↦ sum_characters_eq_zero_aux <| h a H⟩
  simp only [ha, map_one, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_eq_zero,
    Finset.card_eq_zero, Finset.univ_eq_empty_iff] at H
  exact (not_isEmpty_of_nonempty <| DirichletCharacter R n) H

end general

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} [NeZero n]

variable (R n) in
omit [IsDomain R] in
private lemma HasEnoughRootsOfUnity.of_totient [HasEnoughRootsOfUnity R n.totient] :
    HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ) :=
  HasEnoughRootsOfUnity.of_dvd R (ZMod.card_units_eq_totient n ▸  Group.exponent_dvd_card)

variable (n) in
/-- There are `n.totient` Dirichlet characters mod `n` with values in a ring that has all
roots of unity. -/
lemma card_eq_totient_of_hasEnoughRootsOfUnity [inst : HasEnoughRootsOfUnity R n.totient] :
    Fintype.card (DirichletCharacter R n) = n.totient := by
  rw [← ZMod.card_units_eq_totient n]
  have := HasEnoughRootsOfUnity.of_totient R n
  exact MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity (ZMod n) R

/-- If `R` is a ring that has enough roots of unity and `n ≠ 0`, then for each
`a ≠ 1` in `ZMod n`, there exists a Dirichlet character `χ` mod `n` with values in `R`
such that `χ a ≠ 1`. -/
theorem exists_apply_ne_one_of_hasEnoughRootsOfUnity [HasEnoughRootsOfUnity R n.totient]
    ⦃a : ZMod n⦄ (ha : a ≠ 1) :
    ∃ χ : DirichletCharacter R n, χ a ≠ 1 :=
  have := HasEnoughRootsOfUnity.of_totient R n
  MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (ZMod n) R ha

/-- If `R` is ring that has enough roots of unity and `n ≠ 0`, then for each `a ≠ 1` in `ZMod n`,
the sum of `χ a` over all Dirichlet characters mod `n` with values in `R` vanishes. -/
theorem sum_characters_eq_zero [HasEnoughRootsOfUnity R n.totient] ⦃a : ZMod n⦄ (ha : a ≠ 1) :
    ∑ χ : DirichletCharacter R n, χ a = 0 :=
  sum_characters_eq_zero_aux <| exists_apply_ne_one_of_hasEnoughRootsOfUnity ha

/-- If `R` is ring that has enough roots of unity and `n ≠ 0`, then for `a` in `ZMod n`,
the sum of `χ a` over all Dirichlet characters mod `n` with values in `R` vanishes if `a ≠ 1`
and has the value `n.totient` if `a = 1`. -/
theorem sum_characters_eq [HasEnoughRootsOfUnity R n.totient] (a : ZMod n) :
    ∑ χ : DirichletCharacter R n, χ a = if a = 1 then (n.totient : R) else 0 := by
  split_ifs with ha
  · simpa only [ha, map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      using congrArg Nat.cast <| card_eq_totient_of_hasEnoughRootsOfUnity n
  · exact sum_characters_eq_zero ha

/-- If `R` is ring that has all roots of unity and `n ≠ 0`, then for `a` and `b`
in `ZMod n` with `a` a unit, the sum of `χ a⁻¹ * χ b` over all Dirichlet characters
mod `n` with values in `R` vanihses if `a ≠ b` and has the value `n.totient` if `a = b`. -/
theorem sum_char_inv_mul_char_eq [HasEnoughRootsOfUnity R n.totient] {a : ZMod n}
    (ha : IsUnit a) (b : ZMod n) :
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
