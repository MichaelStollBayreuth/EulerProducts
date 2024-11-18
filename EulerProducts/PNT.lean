import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

open scoped LSeries.notation

open Complex

/-!
### The logarithmic derivative of the L-function of a trivial character

We show that `s ↦ -L'(χ) s / L(χ) s + 1 / (s - 1)` is continuous outside the zeros of `L(χ)`
when `χ` is a trivial Dirichlet character.
-/

namespace DirichletCharacter

-- probably should add the attribute where defined
attribute [local fun_prop] differentiableAt_LFunction

section trivial

variable (n : ℕ) [NeZero n]

/-- The function obtained by "multiplying away" the pole of `L(χ)` for a trivial Dirichlet
character `χ`. Its (negative) logarithmic derivative is used in the Wiener-Ikehara Theorem
to prove the Prime Number Theorem version of Dirichlet's Theorem on primes in arithmetic
progressions. -/
noncomputable abbrev LFunctionTrivChar₁ : ℂ → ℂ :=
  Function.update (fun z ↦ LFunctionTrivChar n z * (z - 1)) 1
    (∏ p ∈ n.primeFactors, (1 - (p : ℂ)⁻¹))

lemma LFunctionTrivChar₁_apply_of_ne_one {z : ℂ} (hz : z ≠ 1) :
    LFunctionTrivChar₁ n z = LFunctionTrivChar n z * (z - 1) := by
  simp only [ne_eq, hz, not_false_eq_true, Function.update_noteq]

lemma LFunctionTrivChar₁_apply_one_ne_zero : LFunctionTrivChar₁ n 1 ≠ 0 := by
  simp only [Function.update_same]
  refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_
  rw [sub_ne_zero, ne_eq, one_eq_inv]
  exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_one

lemma LFunctionTrivChar₁_differentiable : Differentiable ℂ (LFunctionTrivChar₁ n) := by
  rw [← differentiableOn_univ,
    ← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
  refine ⟨DifferentiableOn.congr (f := fun z ↦ LFunctionTrivChar n z * (z - 1))
    (fun _ hz ↦ DifferentiableAt.differentiableWithinAt <| by fun_prop (disch := simp_all [hz]))
    fun _ hz ↦ ?_,
    continuousWithinAt_compl_self.mp ?_⟩
  · simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and] at hz
    simp only [ne_eq, hz, not_false_eq_true, Function.update_noteq]
  · simpa only [mul_comm (LFunctionTrivChar ..), continuousWithinAt_compl_self,
      continuousAt_update_same] using LFunctionTrivChar_residue_one

lemma deriv_LFunctionTrivChar₁_apply_of_ne_one  {z : ℂ} (hz : z ≠ 1) :
    deriv (LFunctionTrivChar₁ n) z =
      deriv (LFunctionTrivChar n) z * (z - 1) + LFunctionTrivChar n z := by
  have H : deriv (LFunctionTrivChar₁ n) z =
      deriv (fun w ↦ LFunctionTrivChar n w * (w - 1)) z := by
    refine Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨{w | w ≠ 1}, IsOpen.mem_nhds isOpen_ne hz, fun w hw ↦ ?_⟩
    simp only [ne_eq, Set.mem_setOf.mp hw, not_false_eq_true, Function.update_noteq]
  rw [H, deriv_mul (differentiableAt_LFunction _ z (.inl hz)) <| by fun_prop, deriv_sub_const,
    deriv_id'', mul_one]

lemma continuousOn_neg_logDeriv_LFunctionTrivChar₁ :
    ContinuousOn (fun z ↦ -deriv (LFunctionTrivChar₁ n) z / LFunctionTrivChar₁ n z)
      {z | z = 1 ∨ LFunctionTrivChar n z ≠ 0} := by
  simp_rw [neg_div]
  refine (((LFunctionTrivChar₁_differentiable n).contDiff.continuous_deriv le_rfl).continuousOn.div
    (LFunctionTrivChar₁_differentiable n).continuous.continuousOn fun w hw ↦ ?_).neg
  rcases eq_or_ne w 1 with rfl | hw'
  · exact LFunctionTrivChar₁_apply_one_ne_zero _
  · rw [LFunctionTrivChar₁_apply_of_ne_one n hw', mul_ne_zero_iff]
    exact ⟨(Set.mem_setOf.mp hw).resolve_left hw', sub_ne_zero_of_ne hw'⟩

end trivial

section nontrivial

variable {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n}

/-- The negative logarithmic derivative of the L-function of a nontrivial Dirichlet character
is continuous away from the zeros of the L-function. -/
lemma continuousOn_neg_logDeriv_LFunction_of_nontriv (hχ : χ ≠ 1) :
    ContinuousOn (fun z ↦ -deriv (LFunction χ) z / LFunction χ z) {z | LFunction χ z ≠ 0} := by
  simp_rw [neg_div]
  have h := differentiable_LFunction hχ
  exact ((h.contDiff.continuous_deriv le_rfl).continuousOn.div
    h.continuous.continuousOn fun _ hw ↦ hw).neg

end nontrivial

end DirichletCharacter


/-!
### The L-function of Λ restricted to a residue class
-/

section arith_prog

namespace ArithmeticFunction

open DirichletCharacter

variable {q : ℕ} [NeZero q] {a : ZMod q}

namespace vonMangoldt

variable (a) in
/-- The von Mangoldt function restricted to the prime residue class `a` mod `q`. -/
noncomputable abbrev residue_class : ℕ → ℂ :=
  {n : ℕ | (n : ZMod q) = a}.indicator (vonMangoldt ·)

lemma residue_class_apply (ha : IsUnit a) (n : ℕ) :
    residue_class a n =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ n * vonMangoldt n := by
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp only [residue_class, Set.indicator_apply, Set.mem_setOf_eq, mul_ite, mul_zero,
    ← Finset.sum_mul, sum_char_inv_mul_char_eq ℂ ha n, eq_comm (a := a), ite_mul, zero_mul]

lemma residue_class_eq (ha : IsUnit a) :
    residue_class a = (q.totient : ℂ)⁻¹ •
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ • (fun n : ℕ ↦ χ n * vonMangoldt n) := by
  ext1 n
  simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, ← mul_assoc]
    using residue_class_apply ha n

/-- The L-series of the von Mangoldt function restricted to the prime residue class `a` mod `q`
is a linear combination of logarithmic derivatives of L-functions of the Dirichlet characters
mod `q` (on `re s ≥ 1`). -/
lemma LSeries_residue_class_eq (ha : IsUnit a) {s : ℂ} (hs : 1 < s.re) :
    LSeries (residue_class a) s =
      -(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ *
        (deriv (LFunction χ) s / LFunction χ s) := by
  simp only [deriv_LFunction_eq_deriv_LSeries _ hs, LFunction_eq_LSeries _ hs, neg_mul, ← mul_neg,
    ← Finset.sum_neg_distrib, ← neg_div, ← LSeries_twist_vonMangoldt_eq _ hs]
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp_rw [← LSeries_smul,
    ← LSeries_sum <| fun χ _ ↦ (LSeriesSummable_twist_vonMangoldt χ hs).smul _]
  refine LSeries_congr s fun {n} _ ↦ ?_
  simp only [Pi.smul_apply, residue_class_apply ha, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel_of_invertible, one_mul, Finset.sum_apply, Pi.mul_apply]

lemma abscissaOfAbsConv_vonMangoldt_residue_class_le_one (ha : IsUnit a) :
    LSeries.abscissaOfAbsConv (vonMangoldt.residue_class a) ≤ 1:= by
  rw [vonMangoldt.residue_class_eq ha]
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun h hy ↦ ?_
  refine (LSeriesSummable.sum fun χ _ ↦ LSeriesSummable.smul _ ?_).smul _
  exact χ.LSeriesSummable_mul <| ArithmeticFunction.LSeriesSummable_vonMangoldt <|
    by simp only [ofReal_re, hy]

end vonMangoldt

namespace DirichletsThm

variable (a) in
open Classical in
/-- The function `F` used in the Wiener-Ikehara Theorem to prove Dirichlet's Theorem. -/
noncomputable
abbrev auxFun (s : ℂ) : ℂ :=
  (q.totient : ℂ)⁻¹ * (-deriv (LFunctionTrivChar₁ q) s / LFunctionTrivChar₁ q s -
    ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)), χ a⁻¹ * deriv (LFunction χ) s / LFunction χ s)

lemma auxFun_prop (ha : IsUnit a) :
    Set.EqOn (auxFun a)
      (fun s ↦ L (vonMangoldt.residue_class a) s - (q.totient : ℂ)⁻¹ / (s - 1))
      {s | 1 < s.re} := by
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  simp only [vonMangoldt.LSeries_residue_class_eq ha hs, auxFun]
  rw [neg_div, ← neg_add', mul_neg, ← neg_mul,  div_eq_mul_one_div (q.totient : ℂ)⁻¹,
    sub_eq_add_neg, ← neg_mul, ← mul_add]
  congrm (_ * ?_)
  -- this should be easier, but `IsUnit.inv ha` does not work here
  have ha' : IsUnit a⁻¹ := isUnit_of_dvd_one ⟨a, (ZMod.inv_mul_of_unit a ha).symm⟩
  classical -- for `Fintype.sum_eq_add_sum_compl`
  rw [Fintype.sum_eq_add_sum_compl 1, MulChar.one_apply ha', one_mul, add_right_comm]
  simp only [mul_div_assoc]
  congrm (?_ + _)
  have hs₁ : s ≠ 1 := fun h ↦ ((h ▸ hs).trans_eq one_re).false
  rw [deriv_LFunctionTrivChar₁_apply_of_ne_one _ hs₁, LFunctionTrivChar₁_apply_of_ne_one _ hs₁]
  simp only [LFunctionTrivChar]
  rw [add_div, mul_div_mul_right _ _ (sub_ne_zero_of_ne hs₁)]
  conv_lhs => enter [2, 1]; rw [← mul_one (LFunction ..)]
  rw [mul_div_mul_left _ _ <| LFunction_ne_zero_of_one_le_re 1 (.inr hs₁) hs.le]

lemma auxFun_prop' (ha : IsUnit a) :
    Set.EqOn (L (vonMangoldt.residue_class a) - auxFun a) (fun s ↦ (q.totient : ℂ)⁻¹ / (s - 1))
    {s | 1 < s.re} := by
  intro s hs
  simp only [Pi.sub_apply, auxFun_prop ha hs, sub_sub_cancel]

variable (a) in
lemma continuousOn_auxFun' :
    ContinuousOn (auxFun a) {s | s = 1 ∨ ∀ χ : DirichletCharacter ℂ q, LFunction χ s ≠ 0} := by
  rw [show auxFun a = fun s ↦ _ from rfl]
  simp only [auxFun, sub_eq_add_neg]
  refine continuousOn_const.mul <| ContinuousOn.add ?_ ?_
  · refine (continuousOn_neg_logDeriv_LFunctionTrivChar₁ q).mono fun s hs ↦ ?_
    have := LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ q) (s := s)
    simp only [ne_eq, Set.mem_setOf_eq] at hs
    tauto
  · simp only [← Finset.sum_neg_distrib, mul_div_assoc, ← mul_neg, ← neg_div]
    refine continuousOn_finset_sum _ fun χ hχ ↦ continuousOn_const.mul ?_
    replace hχ : χ ≠ 1 := by simpa only [ne_eq, Finset.mem_compl, Finset.mem_singleton] using hχ
    refine (continuousOn_neg_logDeriv_LFunction_of_nontriv hχ).mono fun s hs ↦ ?_
    simp only [ne_eq, Set.mem_setOf_eq] at hs
    rcases hs with rfl | hs
    · simp only [ne_eq, Set.mem_setOf_eq, one_re, le_refl,
        LFunction_ne_zero_of_one_le_re χ (.inl hχ), not_false_eq_true]
    · exact hs χ

variable (a) in
/-- The L-series of the von Mangoldt function restricted to the prime residue class `a` mod `q`
is continuous on `re s ≥ 1` except for a single pole at `s = 1` with residue `(q.totient)⁻¹`. -/
lemma continuousOn_auxFun : ContinuousOn (auxFun a) {s | 1 ≤ s.re} := by
  refine (continuousOn_auxFun' a).mono fun s hs ↦ ?_
  rcases eq_or_ne s 1 with rfl | hs₁
  · simp only [ne_eq, Set.mem_setOf_eq, true_or]
  · simp only [ne_eq, Set.mem_setOf_eq, hs₁, false_or]
    exact fun χ ↦ LFunction_ne_zero_of_one_le_re χ (.inr hs₁) <| Set.mem_setOf.mp hs

variable (a) in
noncomputable abbrev vonMangoldt.residue_class_real : ℕ → ℝ :=
  {n : ℕ | (n : ZMod q) = a}.indicator (vonMangoldt ·)

variable (a) in
omit [NeZero q] in
lemma vonMangoldt.residue_class_coe (n : ℕ) :
    vonMangoldt.residue_class a n = residue_class_real a n := by
  simp +contextual only [vonMangoldt.residue_class, Set.indicator_apply, Set.mem_setOf_eq,
    residue_class_real, apply_ite, ofReal_zero, ↓reduceIte, ite_self]


variable (a) in
lemma exists_nhds_one_continuousOn_auxFun : ∃ U ∈ nhds (1 : ℂ), ContinuousOn (auxFun a) U := by
  obtain ⟨U, hU⟩ : ∃ U ∈ nhdsWithin (1 : ℂ) {1}ᶜ,
      ∀ s ∈ U, ∀ χ : DirichletCharacter ℂ q, LFunction χ s ≠ 0 := by
    have H {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
        ∃ Uχ ∈ nhds (1 : ℂ), ∀ s ∈ Uχ, LFunction χ s ≠ 0 := by
      have H' := (differentiable_LFunction hχ).continuous.continuousAt (x := 1)
      exact Filter.eventually_iff_exists_mem.mp <| H'.eventually_ne <|
        LFunction_apply_one_ne_zero hχ
    obtain ⟨U₁, hU₁⟩ : ∃ U ∈ nhdsWithin (1 : ℂ) {1}ᶜ,
        ∀ s ∈ U, LFunction (1 : DirichletCharacter ℂ q) s ≠ 0 := by
      have H' := (LFunctionTrivChar₁_differentiable q).continuous.continuousAt (x := 1)
      obtain ⟨U', hU'⟩ := Filter.eventually_iff_exists_mem.mp <| H'.eventually_ne <|
        LFunctionTrivChar₁_apply_one_ne_zero q
      refine ⟨U' \ {1}, diff_mem_nhdsWithin_compl hU'.1 {1}, fun s hs ↦ ?_⟩
      replace hU' := hU'.2 s <| Set.mem_of_mem_diff hs
      have hs₁ := Set.not_mem_singleton_iff.mp <| Set.not_mem_of_mem_diff hs
      exact left_ne_zero_of_mul <| LFunctionTrivChar₁_apply_of_ne_one q hs₁ ▸ hU'
    let U' := (⋂ (χ : {χ : DirichletCharacter ℂ q // χ ≠ 1}), (H χ.prop).choose)
    have hU' : U' ∈ nhds 1 := by
      have : Finite {χ : DirichletCharacter ℂ q // χ ≠ 1} := inferInstance
      -- missing a more direct lemma
      refine mem_nhds_iff.mpr ?_
      have H' (χ :  {χ : DirichletCharacter ℂ q // χ ≠ 1}) :
          ∃ V ⊆ (H χ.prop).choose, IsOpen V ∧ 1 ∈ V :=
        eventually_nhds_iff.mp (H χ.prop).choose_spec.1
      refine ⟨⋂ (χ : {χ : DirichletCharacter ℂ q // χ ≠ 1}), (H' χ).choose, ?_, ?_, ?_⟩
      · exact Set.iInter_mono fun χ ↦ (H' χ).choose_spec.1
      · exact isOpen_iInter_of_finite fun χ ↦ (H' χ).choose_spec.2.1
      · exact Set.mem_iInter_of_mem fun χ ↦ (H' χ).choose_spec.2.2
    have hU₂ : ∀ s ∈ U', ∀ {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1), LFunction χ s ≠ 0 :=
      fun s hs χ hχ ↦ (H hχ).choose_spec.2 s <| Set.mem_iInter.mp hs ⟨χ, hχ⟩
    refine ⟨(U' \ {1}) ∩ U₁, ?_, fun s hs χ ↦ ?_⟩
    · exact Filter.inter_mem (diff_mem_nhdsWithin_compl hU' {1}) hU₁.1
    · rcases eq_or_ne χ 1 with rfl | hχ
      · exact hU₁.2 s <| Set.mem_of_mem_inter_right hs
      · exact hU₂ s (Set.mem_of_mem_diff <| Set.mem_of_mem_inter_left hs) hχ
  refine ⟨insert 1 U, insert_mem_nhds_iff.mpr hU.1, ?_⟩
  replace hU :
      ∀ s ∈ insert 1 U, s = 1 ∨ ∀ χ : DirichletCharacter ℂ q, LFunction χ s ≠ 0 := by
    intro s hs
    simp only [Set.union_singleton, Set.mem_insert_iff, ne_eq] at hs ⊢
    exact hs.imp_right fun hs ↦ hU.2 s hs
  exact (continuousOn_auxFun' a).mono fun s hs ↦ hU s hs

lemma auxFun_real (ha : IsUnit a) {x : ℝ} (hx : 1 < x) : auxFun a x = (auxFun a x).re := by
  replace hx : (x : ℂ) ∈ {s | 1 < s.re} := by
    simp only [Set.mem_setOf_eq, ofReal_re, hx]
  rw [auxFun_prop ha hx]
  simp only [sub_re, ofReal_sub]
  congr 1
  · rw [LSeries, re_tsum ?_]
    · push_cast
      refine tsum_congr fun n ↦ ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.term_zero, zero_re, ofReal_zero]
      · simp only [ne_eq, hn, not_false_eq_true, LSeries.term_of_ne_zero,
          vonMangoldt.residue_class_coe, ← ofReal_natCast n, ← ofReal_cpow n.cast_nonneg]
        norm_cast
    · refine LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
      refine (vonMangoldt.abscissaOfAbsConv_vonMangoldt_residue_class_le_one ha).trans_lt ?_
      simp only [Set.mem_setOf_eq, ofReal_re] at hx ⊢
      norm_cast
  · rw [show (q.totient : ℂ) = (q.totient : ℝ) from rfl]
    norm_cast

open Topology Filter in
lemma LSeries_vonMangoldt_residue_class_tendsto_atTop (ha : IsUnit a) :
    Tendsto (fun x : ℝ ↦ ∑' n, vonMangoldt.residue_class_real a n * (n : ℝ) ^ (-x))
      (𝓝[>] 1) atTop := by
  have H {x : ℝ} (hx : 1 < x) :
      ∑' n, vonMangoldt.residue_class_real a n * (n : ℝ) ^ (-x) =
        (auxFun a x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
    apply_fun ((↑) : ℝ → ℂ) using ofReal_injective
    push_cast
    simp_rw [← vonMangoldt.residue_class_coe, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast]
    convert_to L (vonMangoldt.residue_class a) x = _
    · simp only [ofReal_neg, cpow_neg, LSeries, LSeries.term, div_eq_mul_inv]
      refine tsum_congr fun n ↦ ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [Nat.cast_zero, ↓reduceIte, mul_eq_zero, Set.indicator_apply_eq_zero,
          Set.mem_setOf_eq, map_zero, ofReal_zero, implies_true, inv_eq_zero, cpow_eq_zero_iff,
          ne_eq, ofReal_eq_zero, true_and, true_or]
      · simp only [hn, ↓reduceIte]
    · rw [← sub_eq_iff_eq_add', ← auxFun_real ha hx, ← Pi.sub_apply]
      exact auxFun_prop' ha <| Set.mem_setOf.mpr hx
  refine Tendsto.congr' (eventuallyEq_nhdsWithin_of_eqOn fun ⦃x⦄ hx ↦ H hx).symm ?_
  have : ContinuousAt (fun x : ℝ ↦ (auxFun a x).re) 1 := by
    refine continuous_re.continuousAt.comp' <| ContinuousAt.comp' ?_ continuous_ofReal.continuousAt
    obtain ⟨U, hU⟩ := exists_nhds_one_continuousOn_auxFun a
    exact ContinuousOn.continuousAt hU.2 hU.1
  refine tendsto_atTop_add_left_of_le' (𝓝[>] 1) ((auxFun a 1).re - 1) ?_ ?_
  · exact eventually_nhdsWithin_of_eventually_nhds <|
      eventually_ge_of_tendsto_gt (by simp) this.tendsto
  · conv => enter [1, x]; rw [div_eq_mul_inv]
    refine Tendsto.comp (y := atTop) ?_ ?_
    · refine tendsto_atTop_atTop.mpr fun x ↦ ⟨q.totient * x, fun y hy ↦ ?_⟩
      exact (le_inv_mul_iff₀' <| mod_cast q.totient.pos_of_neZero).mpr hy
    · refine tendsto_inv_zero_atTop.comp (y := 𝓝[>] 0) ?_
      convert ContinuousWithinAt.tendsto_nhdsWithin_image ?_
      · exact (sub_self _).symm
      · simp only [Set.image_sub_const_Ioi, sub_self]
      · exact (continuous_add_right (-1)).continuousWithinAt

variable (a) in
lemma vonMangoldt_non_primes_residue_class_bound :
    ∃ C : ℝ, ∀ {x : ℝ} (hx : x > 1), ∑' n : ℕ,
      (if n.Prime then (0 : ℝ) else vonMangoldt.residue_class_real a n) * (n : ℝ) ^ (-x) ≤ C := by
  have hC₁ {p : ℕ} (hp : p.Prime) :
     Real.log p / (1 - (p : ℝ)⁻¹) ≤ 4 * (p : ℝ) ^ (1 / 2 : ℝ) := by
    have : 0 < 1 - (p : ℝ)⁻¹ := by
      simp only [sub_pos, inv_lt_one_iff₀, Nat.one_lt_cast, hp.one_lt, or_true]
    rw [div_le_iff₀ this]
    have : 1 ≤ 2 * (1 - (p : ℝ)⁻¹) := by
      have : (p : ℝ)⁻¹ ≤ 2⁻¹ :=
        (inv_le_inv₀ (mod_cast hp.pos) zero_lt_two).mpr <| mod_cast hp.two_le
      linarith
    calc Real.log p
      _ ≤ (p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) := Real.log_le_rpow_div p.cast_nonneg one_half_pos
      _ = 2 * (p : ℝ) ^ (1 / 2 : ℝ) := by field_simp; ring
      _ ≤ 2 * (p : ℝ) ^ (1 / 2 : ℝ) * (2 * (1 - (p : ℝ)⁻¹)) := by
        nth_rw 1 [← mul_one (2 * _ ^ _)]
        gcongr
      _ = 4 * (p : ℝ) ^ (1 / 2 : ℝ) * (1 - (p : ℝ)⁻¹) := by ring
  replace hC₁ {p : ℕ} (hp : p.Prime) :
      Real.log p * (p : ℝ) ^ (-2 : ℤ) / (1 - (p : ℝ)⁻¹) ≤ 4 * (p : ℝ) ^ (-2 + 1 / 2 : ℝ) := by
    have hp₁ : 0 < (p : ℝ) := mod_cast hp.pos
    rw [mul_div_right_comm, add_comm, Real.rpow_add hp₁, ← mul_assoc,
      show (-2 : ℝ) = (-2 : ℤ) by norm_cast, Real.rpow_intCast]
    have := hC₁ hp
    gcongr
  obtain ⟨C₂, hC₂⟩ : ∃ C : ℝ, ∑' p : Nat.Primes, (p : ℝ) ^ (-2 + 1 / 2 : ℝ) ≤ C := by
    norm_num
    use ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))
    convert tsum_subtype_le (γ := ℝ) _ {p : ℕ | p.Prime} (fun n ↦ ?_) ?_ using 3 with e p
    · rfl
    · positivity
    · exact Real.summable_nat_rpow.mpr <| by norm_num
  use 4 * C₂
  intro x hx
  have H : ∑' (n : ℕ), (if Nat.Prime n then 0 else vonMangoldt.residue_class_real a n) * (n : ℝ) ^ (-x) =
      ∑' (p : Nat.Primes), ∑' k : ℕ, Real.log p * (p : ℝ) ^ (-(k + 2) : ℤ) := by
    simp only [vonMangoldt.residue_class_real, Set.indicator, Set.mem_setOf_eq, vonMangoldt_apply,
      ite_mul, zero_mul]
    sorry
  rw [H]; clear H
  calc _
    _ = ∑' (p : Nat.Primes), Real.log p * ∑' (k : ℕ), (p : ℝ) ^ (-(k + 2 : ℤ)) := by
      simp_rw [tsum_mul_left]
    _ = ∑' (p : Nat.Primes), Real.log p * (p : ℝ) ^ (-2 : ℤ) / (1 - (p : ℝ)⁻¹) := by
      refine tsum_congr fun p ↦ ?_
      rw [mul_div_assoc]
      congrm (_ * ?_)
      simp only [neg_add_rev]
      conv => enter [1, 1, k]; rw [zpow_add₀ (mod_cast p.prop.ne_zero)]
      rw [tsum_mul_left, div_eq_mul_inv]
      congrm (_ * ?_)
      simp only [zpow_neg, ← inv_zpow]
      refine tsum_geometric_of_lt_one (by positivity) ?_
      simp only [inv_lt_one_iff₀, Nat.one_lt_cast, p.prop.one_lt, or_true]
    _ ≤ ∑' (p : Nat.Primes), 4 * (p : ℝ) ^ (- 2 + 1 / 2 : ℝ) := by
      refine tsum_le_tsum (fun p : Nat.Primes ↦ hC₁ p.prop) ?_ ?_
      · sorry
      · sorry
    _ ≤ 4 * C₂ := by
      rw [tsum_mul_left]
      gcongr


open Topology Filter in
lemma LSeries_vonMangoldt_primes_residue_class_tendsto_atTop (ha : IsUnit a) :
    Tendsto (fun x : ℝ ↦ ∑' n : ℕ,
      (if n.Prime then vonMangoldt.residue_class_real a n else 0) * (n : ℝ) ^ (-x))
      (𝓝[<] 1) atTop := by

  sorry

/- lemma abscissaOfAbsConv_vonMangoldt_residue_class (ha : IsUnit a) :
    LSeries.abscissaOfAbsConv (vonMangoldt.residue_class a) = 1 := by
  refine le_antisymm ?_ ?_
  · exact vonMangoldt.abscissaOfAbsConv_vonMangoldt_residue_class_le_one ha
  · by_contra! H
    change LSeries.abscissaOfAbsConv (vonMangoldt.residue_class a) < (1 : ℂ).re at H
    exact not_continuousAt_LSeries_residue_class ha <|
      HasDerivAt.continuousAt <| LSeries_hasDerivAt H -/

end DirichletsThm

end ArithmeticFunction

end arith_prog

namespace LSeries

/- lemma analyticOn_term (f : ℕ → ℂ) (n : ℕ) :
    AnalyticOn ℂ (fun s ↦ term f s n) Set.univ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa only [term_zero] using analyticOn_const
  · have : NeZero n := ⟨hn⟩
    simp only [term_of_ne_zero hn]
    exact AnalyticOn.div analyticOn_const
      (analyticOn_univ_iff_differentiable.mpr <| differentiable_const_cpow_of_neZero n)
      fun s _ ↦ by rw [cpow_def_of_ne_zero (mod_cast hn)]; exact exp_ne_zero _

/-- The L-series of a function with finite support is entire. -/
lemma analyticOn_of_finite_support {f : ℕ → ℂ} (hf : ∃ n, ∀ m ≥ n, f m = 0) :
    AnalyticOn ℂ (LSeries f) Set.univ := by
  obtain ⟨n, hn⟩ := hf
  have : LSeries f = fun s ↦ ∑ m ∈ Finset.range n, term f s m := by
    refine funext fun s ↦ tsum_eq_sum fun m hm ↦ ?_
    refine (eq_or_ne m 0).casesOn (fun H ↦ H ▸ term_zero ..) (fun H ↦ ?_)
    simp only [Finset.mem_range, not_lt] at hm
    simp only [term_of_ne_zero H, hn m hm, zero_div]
  exact this ▸ Finset.analyticOn_sum _ fun m _ ↦ analyticOn_term f m -/

end LSeries

open LSeries

-- We need a statement along the lines of:
-- if `f n = 0` for all large enough `n` *that are not perfect powers*, then
-- `LSeries f` is holomorphic at `s = 1`.

/-- **Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positive
integer and `a : ZMod q` is a unit, then there are infintely many prime numbers `p`
such that `(p : ZMod q) = a`. -/
theorem dirchlet_primes_in_arith_progression (q : ℕ) [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ∀ n : ℕ, ∃ p > n, p.Prime ∧ (p : ZMod q) = a := by
  have H₁ := ArithmeticFunction.DirichletsThm.auxFun_prop ha
  have H₂ := ArithmeticFunction.DirichletsThm.continuousOn_auxFun a
  by_contra! H
  obtain ⟨n, hn⟩ := H
  -- have key : abscissaOfAbsConv
  have H₃ : ∃ n : ℕ, ∀ m ≥ n,
      ({(n : ℕ) | (n : ZMod q) = a}.indicator ↗ArithmeticFunction.vonMangoldt) m = 0 := by
    refine ⟨n + 1, fun m hm ↦ ?_⟩
    by_cases H₀ : (m : ZMod q) = a
    · simp only [Set.mem_setOf_eq, H₀, Set.indicator_of_mem, ofReal_eq_zero]
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
      sorry
    · simp only [Set.mem_setOf_eq, H₀, not_false_eq_true, Set.indicator_of_not_mem]
  sorry

/-!
### Statement of a version of the Wiener-Ikehara Theorem
-/

open Filter Topology Nat ArithmeticFunction in
/-- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/
def WienerIkeharaTheorem : Prop :=
  ∀ {f : ℕ → ℝ} {A : ℝ} {F : ℂ → ℂ}, (∀ n, 0 ≤ f n) →
    Set.EqOn F (fun s ↦ L ↗f s - A / (s - 1)) {s | 1 < s.re} →
    ContinuousOn F {s | 1 ≤ s.re} →
    Tendsto (fun N : ℕ ↦ ((Finset.range N).sum f) / N) atTop (𝓝 A)

/-!
### Derivation of the Prime Number Theorem and Dirichlet's Theorem from the Wiener-Ikehara Theorem
-/

open Filter ArithmeticFunction Topology ArithmeticFunction.DirichletsThm

/--  The *Wiener-Ikehara Theorem* implies *Dirichlet's Theorem* in the form that
`ψ x ∼ q.totient⁻¹ * x`, where `ψ x = ∑ n < x ∧ n ≡ a mod q, Λ n`
and `Λ` is the von Mangoldt function.

This is Theorem 2 in Section 2 of PNT+ (but using the `WIT` stub defined here). -/
theorem Dirichlet_vonMangoldt (WIT : WienerIkeharaTheorem) {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) :
    Tendsto (fun N : ℕ ↦ (((Finset.range N).filter (fun n : ℕ ↦ (n : ZMod q) = a)).sum Λ) / N)
      atTop (𝓝 <| (q.totient : ℝ)⁻¹) := by
  classical
  have H N : ((Finset.range N).filter (fun n : ℕ ↦ (n : ZMod q) = a)).sum Λ =
      (Finset.range N).sum ({n : ℕ | (n : ZMod q) = a}.indicator Λ) :=
    (Finset.sum_indicator_eq_sum_filter _ _ (fun _ ↦ {n : ℕ | n = a}) _).symm
  simp only [H]
  refine WIT (F := auxFun a) (fun n ↦ ?_) ?_ ?_
  · exact Set.indicator_apply_nonneg fun _ ↦ vonMangoldt_nonneg
  · convert auxFun_prop ha with s n
    · by_cases hn : n = a
      · simp only [Set.mem_setOf_eq, hn, Set.indicator_of_mem]
      · simp only [Set.mem_setOf_eq, hn, not_false_eq_true, Set.indicator_of_not_mem, ofReal_zero]
    · rw [ofReal_inv, ofReal_natCast]
  · exact continuousOn_auxFun a

/-- The *Wiener-Ikehara Theorem* implies the *Prime Number Theorem* in the form that
`ψ x ∼ x`, where `ψ x = ∑ n < x, Λ n` and `Λ` is the von Mangoldt function. -/
theorem PNT_vonMangoldt (WIT : WienerIkeharaTheorem) :
    Tendsto (fun N : ℕ ↦ ((Finset.range N).sum Λ) / N) atTop (𝓝 1) := by
  convert Dirichlet_vonMangoldt WIT (q := 1) (a := 1) isUnit_one with n
  · exact (Finset.filter_true_of_mem fun _ _ ↦ Subsingleton.eq_one _).symm
  · simp only [Nat.totient_one, Nat.cast_one, inv_one]
