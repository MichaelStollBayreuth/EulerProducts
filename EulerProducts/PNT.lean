import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

open scoped LSeries.notation

open Complex

/-!
### The L-function of Λ restricted to a residue class
-/

section arith_prog

namespace ArithmeticFunction

open DirichletCharacter

namespace vonMangoldt

variable {q : ℕ} (a : ZMod q)

/-- The von Mangoldt function restricted to the residue class `a` mod `q`. -/
noncomputable abbrev residue_class : ℕ → ℝ :=
  {n : ℕ | (n : ZMod q) = a}.indicator (vonMangoldt ·)

lemma residue_class_apply_zero : residue_class a 0 = 0 := by
  simp only [Set.indicator_apply_eq_zero, Set.mem_setOf_eq, Nat.cast_zero, map_zero, ofReal_zero,
    implies_true]

lemma abscissaOfAbsConv_residue_class_le_one :
    LSeries.abscissaOfAbsConv ↗(vonMangoldt.residue_class a) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ ?_
  simp only [vonMangoldt.residue_class]
  have := ArithmeticFunction.LSeriesSummable_vonMangoldt <|
    show 1 < (y : ℂ).re by simp only [ofReal_re, hy]
  convert this.indicator {n : ℕ | (n : ZMod q) = a}
  refine summable_congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, LSeries.term_zero, Nat.cast_zero, ite_self]
  · simp+contextual only [Set.indicator_apply, Set.mem_setOf_eq, apply_ite, ofReal_zero, ne_eq, hn,
      not_false_eq_true, LSeries.term_of_ne_zero, ↓reduceIte, zero_div, ite_self]

variable [NeZero q] {a}

lemma residue_class_apply (ha : IsUnit a) (n : ℕ) :
    residue_class a n =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ n * vonMangoldt n := by
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp +contextual only [residue_class, Set.indicator_apply, Set.mem_setOf_eq, apply_ite,
    ofReal_zero, mul_zero, ← Finset.sum_mul, sum_char_inv_mul_char_eq ℂ ha n, eq_comm (a := a),
    ite_mul, zero_mul, ↓reduceIte, ite_self]

lemma residue_class_eq (ha : IsUnit a) :
    ↗(residue_class a) = (q.totient : ℂ)⁻¹ •
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ • (fun n : ℕ ↦ χ n * vonMangoldt n) := by
  ext1 n
  simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, ← mul_assoc]
    using residue_class_apply ha n

/-- The L-series of the von Mangoldt function restricted to the prime residue class `a` mod `q`
is a linear combination of logarithmic derivatives of L-functions of the Dirichlet characters
mod `q` (on `re s ≥ 1`). -/
lemma LSeries_residue_class_eq (ha : IsUnit a) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(residue_class a) s =
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

end vonMangoldt

namespace DirichletsThm

variable {q : ℕ} [NeZero q] (a : ZMod q)

open Classical in
/-- The function `F` used in the Wiener-Ikehara Theorem to prove Dirichlet's Theorem. -/
noncomputable
abbrev auxFun (s : ℂ) : ℂ :=
  (q.totient : ℂ)⁻¹ * (-deriv (LFunctionTrivChar₁ q) s / LFunctionTrivChar₁ q s -
    ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)), χ a⁻¹ * deriv (LFunction χ) s / LFunction χ s)

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

/-- The L-series of the von Mangoldt function restricted to the prime residue class `a` mod `q`
is continuous on `re s ≥ 1` except for a single pole at `s = 1` with residue `(q.totient)⁻¹`.
The statement as given here is equivalent. -/
lemma continuousOn_auxFun : ContinuousOn (auxFun a) {s | 1 ≤ s.re} := by
  refine (continuousOn_auxFun' a).mono fun s hs ↦ ?_
  rcases eq_or_ne s 1 with rfl | hs₁
  · simp only [ne_eq, Set.mem_setOf_eq, true_or]
  · simp only [ne_eq, Set.mem_setOf_eq, hs₁, false_or]
    exact fun χ ↦ LFunction_ne_zero_of_one_le_re χ (.inr hs₁) <| Set.mem_setOf.mp hs

variable {a}

lemma auxFun_prop (ha : IsUnit a) :
    Set.EqOn (auxFun a)
      (fun s ↦ L ↗(vonMangoldt.residue_class a) s - (q.totient : ℂ)⁻¹ / (s - 1))
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
  rw [deriv_LFunctionTrivChar₁_apply_of_ne_one _ hs₁, LFunctionTrivChar₁,
    Function.update_noteq hs₁]
  simp only [LFunctionTrivChar]
  rw [add_div, mul_div_mul_left _ _ (sub_ne_zero_of_ne hs₁)]
  conv_lhs => enter [2, 1]; rw [← mul_one (LFunction ..)]
  rw [mul_comm _ 1, mul_div_mul_right _ _ <| LFunction_ne_zero_of_one_le_re 1 (.inr hs₁) hs.le]

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
      · simp only [ne_eq, hn, not_false_eq_true, LSeries.term_of_ne_zero, ← ofReal_natCast n, ←
          ofReal_cpow n.cast_nonneg]
        norm_cast
    · refine LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
      refine (vonMangoldt.abscissaOfAbsConv_residue_class_le_one a).trans_lt ?_
      simp only [Set.mem_setOf_eq, ofReal_re] at hx ⊢
      norm_cast
  · rw [show (q.totient : ℂ) = (q.totient : ℝ) from rfl]
    norm_cast

end DirichletsThm

/-!
### Derivation of Dirichlet's Theorem (without Wiener-Ikehara)
-/

variable {q : ℕ} {a : ZMod q}

open DirichletsThm

open Topology Filter in
lemma LSeries_vonMangoldt_residue_class_tendsto_atTop [NeZero q] (ha : IsUnit a) :
    Tendsto (fun x : ℝ ↦ ∑' n, vonMangoldt.residue_class a n / (n : ℝ) ^ x)
      (𝓝[>] 1) atTop := by
  have H {x : ℝ} (hx : 1 < x) :
      ∑' n, vonMangoldt.residue_class a n / (n : ℝ) ^ x =
        (auxFun a x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
    apply_fun ((↑) : ℝ → ℂ) using ofReal_injective
    push_cast
    simp_rw [ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast]
    convert_to L ↗(vonMangoldt.residue_class a) x = _
    · simp only [div_eq_mul_inv, LSeries, LSeries.term]
      refine tsum_congr fun n ↦ ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [vonMangoldt.residue_class_apply_zero, ofReal_zero, Nat.cast_zero, zero_mul,
          ↓reduceIte]
      · simp only [hn, ↓reduceIte]
    · rw [← auxFun_real ha hx, auxFun_prop ha <| Set.mem_setOf.mpr (ofReal_re x ▸ hx)]
      simp only [sub_add_cancel]
  refine Tendsto.congr' (eventuallyEq_nhdsWithin_of_eqOn fun ⦃x⦄ hx ↦ H hx).symm ?_
  clear H
  have : ContinuousWithinAt (fun x : ℝ ↦ (auxFun a x).re) {x | 1 < x} 1 := by
    refine continuous_re.continuousWithinAt.comp (t := (Set.univ : Set ℂ)) ?_ fun ⦃_⦄ _ ↦ trivial
    change ContinuousWithinAt ((auxFun a) ∘ ofReal) ..
    refine ContinuousWithinAt.comp (t := {s | 1 < s.re}) ?_ continuous_ofReal.continuousWithinAt
      fun ⦃_⦄ a ↦ a
    refine ContinuousWithinAt.mono (t := {s | 1 ≤ s.re}) ?_
       fun s hs ↦ Set.mem_setOf.mpr <| (Set.mem_setOf.mp hs).le
    exact ContinuousOn.continuousWithinAt (continuousOn_auxFun a) <| by
      simp only [ofReal_one, Set.mem_setOf_eq, one_re, le_refl]
  refine tendsto_atTop_add_left_of_le' (𝓝[>] 1) ((auxFun a 1).re - 1) ?_ ?_
  · exact Tendsto.eventually_const_le (ofReal_one ▸ sub_one_lt _) this.tendsto
  · conv => enter [1, x]; rw [div_eq_mul_inv]
    refine Tendsto.comp (y := atTop) ?_ ?_
    · refine tendsto_atTop_atTop.mpr fun x ↦ ⟨q.totient * x, fun y hy ↦ ?_⟩
      exact (le_inv_mul_iff₀' <| mod_cast q.totient.pos_of_neZero).mpr hy
    · refine tendsto_inv_zero_atTop.comp (y := 𝓝[>] 0) ?_
      convert ContinuousWithinAt.tendsto_nhdsWithin_image ?_
      · exact (sub_self _).symm
      · simp only [Set.image_sub_const_Ioi, sub_self]
      · exact (continuous_add_right (-1)).continuousWithinAt


private lemma inv_lt_one (p : Nat.Primes) : (p : ℝ)⁻¹ < 1 := by
  rw [inv_lt_one₀ <| mod_cast p.prop.pos]
  exact_mod_cast p.prop.one_lt

private lemma log_div_bound (p : Nat.Primes) :
    Real.log p * (p : ℝ) ^ (-2 : ℤ) / (1 - (p : ℝ)⁻¹) ≤ 4 * (p : ℝ) ^ (-2 + 1 / 2 : ℝ) := by
  have hp₁ : 0 < (p : ℝ) := mod_cast p.prop.pos
  have key : Real.log p / (1 - (p : ℝ)⁻¹) ≤ 4 * (p : ℝ) ^ (1 / 2 : ℝ) := by
    have : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr <| inv_lt_one p
    rw [div_le_iff₀ this]
    have : 1 ≤ 2 * (1 - (p : ℝ)⁻¹) := by
      have : (p : ℝ)⁻¹ ≤ 2⁻¹ :=
        (inv_le_inv₀ (mod_cast p.prop.pos) zero_lt_two).mpr <| mod_cast p.prop.two_le
      linarith
    calc Real.log p
      _ ≤ (p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) := Real.log_le_rpow_div p.val.cast_nonneg one_half_pos
      _ = 2 * (p : ℝ) ^ (1 / 2 : ℝ) := by field_simp; ring
      _ ≤ 2 * (p : ℝ) ^ (1 / 2 : ℝ) * (2 * (1 - (p : ℝ)⁻¹)) := by
        nth_rw 1 [← mul_one (2 * _ ^ _)]
        gcongr
      _ = 4 * (p : ℝ) ^ (1 / 2 : ℝ) * (1 - (p : ℝ)⁻¹) := by ring
  rw [mul_div_right_comm, add_comm, Real.rpow_add hp₁, ← mul_assoc,
    show (-2 : ℝ) = (-2 : ℤ) by norm_cast, Real.rpow_intCast]
  gcongr

private lemma tsum_primes_le : ∃ C : ℝ, ∑' p : Nat.Primes, (p : ℝ) ^ (-2 + 1 / 2 : ℝ) ≤ C := by
  norm_num
  use ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))
  convert tsum_subtype_le (γ := ℝ) _ {p : ℕ | p.Prime} (fun n ↦ ?_) ?_ using 3 with e p
  · rfl
  · positivity
  · exact Real.summable_nat_rpow.mpr <| by norm_num

variable (a)

lemma summable_residue_class_real_mul_pow {x : ℝ} (hx : x > 1) :
    Summable fun n : ℕ ↦ (vonMangoldt.residue_class a n) / (n : ℝ) ^ x :=
  LSeries.summable_real_of_abscissaOfAbsConv_lt <|
    (vonMangoldt.abscissaOfAbsConv_residue_class_le_one a).trans_lt <| mod_cast hx.lt

lemma vonMangoldt_non_primes_residue_class_bound :
    ∃ C : ℝ, ∀ {x : ℝ} (_ : x > 1), ∑' n : ℕ,
      (if n.Prime then (0 : ℝ) else vonMangoldt.residue_class a n) / (n : ℝ) ^ x ≤ C := by
  obtain ⟨C, hC⟩ := tsum_primes_le
  use 4 * C
  intro x hx
  have hpx (p : Nat.Primes) : (p : ℝ) ^ (-x) < 1 := by
    rw [Real.rpow_neg (by positivity), inv_lt_one₀ (by have := p.prop.pos; positivity)]
    refine Real.one_lt_rpow (mod_cast p.prop.one_lt) (zero_lt_one.trans hx.lt)
  let F (n : ℕ) : ℝ :=
    (if n.Prime then (0 : ℝ) else vonMangoldt.residue_class a n) / (n : ℝ) ^ x
  have hF₀ (p : Nat.Primes) : F p = 0 := by
    simp only [p.prop, ↓reduceIte, zero_div, F]
  have hF₁ (p : Nat.Primes) (k : ℕ) : F ((p : ℕ) ^ (k + 2)) =
      if ((p : ℕ) ^ (k + 2) : ZMod q) = a then Real.log p * ((p : ℝ) ^ (-x)) ^ (k + 2) else 0 := by
    simp only [vonMangoldt.residue_class, Set.indicator, Set.mem_setOf_eq, div_eq_mul_inv, ite_mul,
      zero_mul, le_add_iff_nonneg_left, zero_le, Nat.Prime.not_prime_pow, ↓reduceIte, Nat.cast_pow,
      F]
    refine ite_congr rfl (fun _ ↦ ?_) fun _ ↦ rfl
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime p.prop,
      ← Real.rpow_natCast_mul (by positivity), ← Real.rpow_mul_natCast (by positivity), neg_mul,
      mul_comm x, Real.rpow_neg p.val.cast_nonneg]
  have hs : Summable F := by
    have := summable_residue_class_real_mul_pow a hx
    have H₁ (n : ℕ) : 0 ≤ {n : ℕ | (n : ZMod q) = a}.indicator (fun n ↦ Λ n) n / (n : ℝ) ^ x := by
      simp only [Set.indicator, Set.mem_setOf_eq]
      split_ifs with h
      · have : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
        positivity
      · rw [zero_div]
    have hFnonneg (n : ℕ) : 0 ≤ F n := by
      simp only [vonMangoldt.residue_class, ite_mul, zero_mul, F]
      split_ifs with hn
      · rw [zero_div]
      · exact H₁ n
    refine this.of_nonneg_of_le hFnonneg fun n ↦ ?_
    simp only [vonMangoldt.residue_class, ite_div, zero_div, F]
    refine (ite_le_sup ..).trans ?_
    simp only [H₁, sup_of_le_right, le_refl]
  have hF : Function.support F ⊆ {n | IsPrimePow n} := by
    intro n hn
    simp only [Function.mem_support] at hn
    contrapose! hn
    simp only [Set.mem_setOf_eq] at hn
    simp only [mt Nat.Prime.isPrimePow hn, ↓reduceIte, div_eq_zero_iff, Set.indicator_apply_eq_zero,
      Set.mem_setOf_eq, vonMangoldt_apply, hn, implies_true, Nat.cast_nonneg, true_or, F]
  rw [tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers hs hF]
  conv_lhs => enter [1, 1, p]; rw [hF₀ p]
  simp only [tsum_zero, zero_add]
  conv_lhs => enter [1, p, 1, k]; rw [hF₁ p k]
  have : ∑' (p : Nat.Primes), 4 * (p : ℝ) ^ (-2 + 1 / 2 : ℝ) ≤ 4 * C := by
    rw [tsum_mul_left]
    gcongr
  have hs₄ (p : Nat.Primes) : Summable fun k : ℕ ↦ Real.log p * (p : ℝ)⁻¹ ^ (k + 2) := by
    have H (k : ℕ) : Real.log p * (p : ℝ)⁻¹ ^ (k + 2) ≤ (p : ℝ)⁻¹ ^ (k + 1) := by
      have h₁ := Real.log_le_rpow_div p.val.cast_nonneg zero_lt_one
      simp only [Real.rpow_one, div_one] at h₁
      calc _
        _ ≤ p * (p : ℝ)⁻¹ ^ (k + 2) := by gcongr
        _ = (p : ℝ)⁻¹ ^ (k + 1) := by
          nth_rewrite 1 [← inv_inv (p : ℝ)]
          rw [mul_comm, ← div_eq_mul_inv, div_eq_iff (by have := p.prop.pos; positivity),
            ← pow_succ]
    refine Summable.of_nonneg_of_le (fun k ↦ by positivity) H ?_
    conv => enter [1, k]; rw [pow_succ']
    exact Summable.mul_left _ <| summable_geometric_of_lt_one (by positivity) <| inv_lt_one p
  have hs₀ (p : Nat.Primes) : Summable fun k ↦ Real.log p * ((p : ℝ) ^ (-x)) ^ (k + 2) := by
    refine (hs₄ p).of_nonneg_of_le (fun k ↦ by positivity) fun k ↦ ?_
    rw [← Real.rpow_neg_one]
    gcongr
    exact_mod_cast p.prop.one_le
  have hs₁ : Summable fun p : Nat.Primes ↦ ∑' (k : ℕ),
      if ((p : ℕ) ^ (k + 2) : ZMod q) = a then Real.log p * ((p : ℝ) ^ (-x)) ^ (k + 2) else 0 := by
    have H (p : Nat.Primes) : ∑' (k : ℕ),
        (if ((p : ℕ) ^ (k + 2) : ZMod q) = a then Real.log p * ((p : ℝ) ^ (-x)) ^ (k + 2) else 0) ≤
        ∑' k : ℕ, Real.log p * ((p : ℝ) ^ (-x)) ^ (k + 2) := by
      have H₀ (k : ℕ) : (if ((p : ℕ) ^ (k + 2) : ZMod q) = a then
          Real.log p * ((p : ℝ) ^ (-x)) ^ (k + 2) else 0) ≤ Real.log p * ((p : ℝ) ^ (-x)) ^ (k + 2) := by
        refine (ite_le_sup ..).trans ?_
        simp only [sup_le_iff, le_refl, true_and]
        positivity
      refine tsum_le_tsum H₀ ?_ (hs₀ p)
      · refine Summable.of_nonneg_of_le (fun k ↦ ?_) H₀ (hs₀ p)
        refine le_trans ?_ (inf_le_ite ..)
        positivity
    refine Summable.of_nonneg_of_le (fun p ↦ tsum_nonneg fun n ↦ ?_) H ?_
    · exact le_trans (by positivity) <| inf_le_ite ..
    · simp_rw [add_comm _ 2, pow_add, ← mul_assoc, tsum_mul_left]
      conv => enter [1, p, 2]; rw [tsum_geometric_of_lt_one (by positivity) (hpx p)]
      have H₁ (p : Nat.Primes) :
          Real.log p * ((p : ℝ) ^ (-x)) ^ 2 * (1 - (p : ℝ) ^ (-x))⁻¹ ≤
            2 * Real.log p * ((p : ℝ) ^ (-x)) ^ 2 := by
        have h₀ : 0 < 1 - (p : ℝ) ^ (-x) := sub_pos.mpr (hpx p)
        have h₁ : (1 - (p : ℝ) ^ (-x))⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ h₀ zero_lt_two, le_sub_comm, Real.rpow_neg (mod_cast p.val.cast_nonneg),
            show (1 - 2⁻¹ : ℝ) = 2⁻¹ by norm_num,
            inv_le_inv₀ (by have := p.prop.pos; positivity) zero_lt_two, ← Real.rpow_one 2]
          exact Real.rpow_le_rpow zero_le_two (mod_cast p.prop.two_le : (2 : ℝ) ≤ p) zero_le_one
            |>.trans <| Real.rpow_le_rpow_of_exponent_le (mod_cast p.prop.one_le) hx.lt.le
        rw [← mul_rotate]
        gcongr
      refine Summable.of_nonneg_of_le (fun p ↦ ?_) H₁ ?_
      · have : 0 < 1 - (p : ℝ) ^ (-x) := sub_pos.mpr (hpx p)
        positivity
      · simp_rw [mul_assoc]
        refine Summable.mul_left 2 ?_
        have key (p : Nat.Primes) :
            Real.log p * ((p : ℝ) ^ (-x)) ^ 2 ≤ 2 * (p : ℝ) ^ (-(3 / 2) : ℝ) := by
          have h₁ := Real.log_le_rpow_div p.val.cast_nonneg one_half_pos
          have h₂ : ((p : ℝ) ^ (-x)) ^ 2 ≤ (p : ℝ) ^ (-2 : ℝ) := by
            rw [Real.rpow_neg p.val.cast_nonneg 2, ← Real.inv_rpow p.val.cast_nonneg,
              ← Real.rpow_natCast]
            refine Real.rpow_le_rpow (by positivity) ?_ zero_le_two
            rw [← Real.rpow_neg_one]
            exact (Real.rpow_le_rpow_left_iff <| mod_cast p.prop.one_lt).mpr <| neg_le_neg hx.lt.le
          calc _
            _ ≤ Real.log p * (p : ℝ) ^ (-2 : ℝ) := by gcongr
            _ ≤ (p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) * (p : ℝ) ^ (-2 : ℝ) := by gcongr
            _ = _ := by
              rw [one_div, div_inv_eq_mul, mul_comm _ 2, mul_assoc, ← Real.rpow_add (mod_cast p.prop.pos)]
              norm_num
        refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) key ?_
        exact (Nat.Primes.summable_rpow.mpr <| by norm_num).mul_left 2
  have hs₂ : Summable fun p : Nat.Primes ↦ 4 * (p : ℝ) ^ (-2 + 1 / 2 : ℝ) :=
    (Nat.Primes.summable_rpow.mpr <| by norm_num).mul_left _
  refine le_trans ?_ this
  refine tsum_le_tsum (fun p ↦ ?_) hs₁ hs₂
  have H (k : ℕ) :
      (if ((p : ℕ) ^ (k + 2) : ZMod q) = a then Real.log p * ((p : ℝ) ^ (-x)) ^ (k + 2) else 0) ≤
      Real.log p * (p : ℝ)⁻¹ ^ (k + 2) := by
    refine (ite_le_sup ..).trans ?_
    rw [sup_eq_left.mpr <| by positivity, ← Real.rpow_neg_one]
    gcongr
    exact_mod_cast p.prop.one_le
  have hs₃ : Summable fun k : ℕ ↦
      if ((p : ℕ) ^ (k + 2) : ZMod q) = a then Real.log p * ((p : ℝ) ^ (-x)) ^ (k + 2) else 0 := by
    have H (k : ℕ) :
        (if ((p : ℕ) ^ (k + 2) : ZMod q) = a then Real.log p * ((p : ℝ) ^ (-x)) ^ (k + 2) else 0) ≤
          Real.log p * ((p : ℝ) ^ (-x)) ^ (k + 2) := by
      refine (ite_le_sup ..).trans ?_
      rw [sup_eq_left.mpr <| by positivity]
    refine Summable.of_nonneg_of_le (fun k ↦ ?_) H (hs₀ p)
    exact le_trans (by positivity) (inf_le_ite ..)
  refine (tsum_le_tsum H hs₃ <| hs₄ p).trans ?_
  conv_lhs => enter [1, k]; rw [add_comm, pow_add]
  rw [tsum_mul_left, tsum_mul_left, ← mul_assoc, tsum_geometric_of_lt_one (by positivity) (inv_lt_one p),
    ← div_eq_mul_inv, ← zpow_natCast, inv_zpow']
  exact log_div_bound p

lemma vonMangoldt_residue_class_bound :
    ∃ C : ℝ, ∀ {x : ℝ} (_ : x > 1), ∑' n : ℕ, vonMangoldt.residue_class a n / (n : ℝ) ^ x ≤
      (∑' p : Nat.Primes, vonMangoldt.residue_class a p / (p : ℝ) ^ x) + C := by
  obtain ⟨C, hC⟩ := vonMangoldt_non_primes_residue_class_bound a
  use C
  intro x hx
  have hs₁ : Summable fun n : ℕ ↦ vonMangoldt.residue_class a n / (n : ℝ) ^ x :=
    summable_residue_class_real_mul_pow a hx
  have hf₁ : Function.support (fun n ↦ vonMangoldt.residue_class a n / (n : ℝ) ^ x) ⊆
      {n | IsPrimePow n} := by
    simp only [Function.support_div, Set.support_indicator]
    refine Set.inter_subset_left.trans <| Set.inter_subset_right.trans ?_
    simp only [Function.support_subset_iff, ne_eq, vonMangoldt_ne_zero_iff, Set.mem_setOf_eq,
      imp_self, implies_true]
  rw [tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers hs₁ hf₁]
  gcongr
  convert hC hx
  have hs₂ : Summable fun n : ℕ ↦
      (if Nat.Prime n then 0 else vonMangoldt.residue_class a n) / ↑n ^ x := by
    convert_to Summable <|
      {n : ℕ | ¬ n.Prime}.indicator (fun n ↦ vonMangoldt.residue_class a n / ↑n ^ x)
    · ext1 n
      simp only [Set.indicator, Set.mem_setOf_eq, ite_div, zero_div, ite_not]
    · exact Summable.indicator hs₁ _
  have hf₂ : Function.support
      (fun n : ℕ ↦ (if Nat.Prime n then 0 else vonMangoldt.residue_class a n) / ↑n ^ x) ⊆
        {n | IsPrimePow n} := by
    rw [Function.support_div]
    refine Set.inter_subset_left.trans ?_
    simp only [Function.support_subset_iff, ne_eq, ite_eq_left_iff, Set.indicator_apply_eq_zero,
      Set.mem_setOf_eq, Classical.not_imp, vonMangoldt_ne_zero_iff, and_imp, imp_self, implies_true]
  rw [tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers hs₂ hf₂]
  conv_lhs => rw [← zero_add (tsum _)]
  have hs₃ : Summable fun p : Nat.Primes ↦
      (if Nat.Prime ↑p then 0 else vonMangoldt.residue_class a ↑p) / ↑↑p ^ x :=
    hs₂.subtype _
  congr
  · conv_rhs => enter [1, p]; simp [p.prop]
    exact tsum_zero.symm
  · ext1 p
    refine tsum_congr fun k ↦ ?_
    have : ¬ Nat.Prime ((p : ℕ) ^ (k + 2)) := Nat.Prime.not_prime_pow <| Nat.le_add_left 2 k
    simp only [Nat.cast_pow, this, ↓reduceIte]

end ArithmeticFunction

end arith_prog

section DirichletsTheorem

open ArithmeticFunction DirichletsThm in
/-- **Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positive
integer and `a : ZMod q` is a unit, then there are infintely many prime numbers `p`
such that `(p : ZMod q) = a`. -/
theorem dirchlet_primes_in_arith_progression {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ∀ n : ℕ, ∃ p > n, p.Prime ∧ (p : ZMod q) = a := by
  by_contra! H
  obtain ⟨N, hN⟩ := H
  have hsupp (p : Nat.Primes) (hp : p > N) : vonMangoldt.residue_class a p = 0 := by
    simp only [vonMangoldt.residue_class, Set.mem_setOf_eq, hN p.val hp p.prop,
      not_false_eq_true, Set.indicator_of_not_mem]
  replace hsupp :
      (Function.support (fun p : Nat.Primes ↦ vonMangoldt.residue_class a p)).Finite := by
    refine Set.Finite.subset (s := {p : Nat.Primes | p ≤ N}) ?_ fun p h ↦ ?_
    · refine Set.Finite.of_finite_image (f := Subtype.val) ?_ ?_
      · exact (Set.finite_le_nat N).subset (s := {n : ℕ | n ≤ N}) <|
          Set.image_subset_iff.mpr fun ⦃_⦄ a ↦ a
      · exact Function.Injective.injOn Nat.Primes.coe_nat_injective
    · simp only [Function.mem_support] at h
      simp only [Set.mem_setOf_eq]
      contrapose! h
      exact hsupp p h
  have hsupp' (x : ℝ) :
      (Function.support
        (fun p : Nat.Primes ↦ vonMangoldt.residue_class a p / (p : ℝ) ^ x)).Finite := by
    rw [Function.support_div]
    exact Set.Finite.inter_of_left hsupp _
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ {x : ℝ} (_ : x > 1),
      (∑' p : Nat.Primes, vonMangoldt.residue_class a p / (p : ℝ) ^ x) ≤ C := by
    use ∑' p : Nat.Primes, vonMangoldt.residue_class a p
    intro x hx
    refine tsum_le_tsum (fun p ↦ ?_) (summable_of_finite_support <| hsupp' x) <|
      summable_of_finite_support hsupp
    conv_rhs => rw [← div_one (vonMangoldt.residue_class ..)]
    gcongr
    · simp only [vonMangoldt.residue_class, Set.indicator, Set.mem_setOf_eq]
      have := vonMangoldt_nonneg (n := p)
      positivity
    · rw [← Real.rpow_zero p]
      gcongr
      · exact_mod_cast p.prop.one_le
      · exact zero_le_one.trans hx.lt.le
  obtain ⟨C', hC'⟩ := vonMangoldt_residue_class_bound a
  have key : ∀ {x : ℝ} (_ : x > 1),
      ∑' n : ℕ, vonMangoldt.residue_class a n / ↑n ^ x ≤ C + C' :=
    fun {x} hx ↦ (hC' hx).trans <| add_le_add_right (hC hx) C'
  have := LSeries_vonMangoldt_residue_class_tendsto_atTop ha
  rw [Filter.tendsto_atTop] at this
  specialize this (C + C' + 1)
  have H : ∀ᶠ (x : ℝ) in nhdsWithin 1 (Set.Ioi 1),
      ∑' (n : ℕ), vonMangoldt.residue_class a n / ↑n ^ x ≤ C + C' := by
    exact eventually_nhdsWithin_of_forall fun _ ↦ key
  have := this.and H
  rw [Filter.eventually_iff] at this
  have h (x : ℝ) : ¬ (C + C' + 1 ≤ ∑' (n : ℕ), vonMangoldt.residue_class a n / ↑n ^ x ∧
      ∑' (n : ℕ), vonMangoldt.residue_class a n / ↑n ^ x ≤ C + C') := by
    intro h'
    have := h'.1.trans h'.2
    simp only [add_le_iff_nonpos_right] at this
    exact zero_lt_one.not_le this
  simp only [h, Set.setOf_false, Filter.empty_not_mem] at this

end DirichletsTheorem

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
  · convert auxFun_prop ha with s
    push_cast
    rfl
  · exact continuousOn_auxFun a

/-- The *Wiener-Ikehara Theorem* implies the *Prime Number Theorem* in the form that
`ψ x ∼ x`, where `ψ x = ∑ n < x, Λ n` and `Λ` is the von Mangoldt function. -/
theorem PNT_vonMangoldt (WIT : WienerIkeharaTheorem) :
    Tendsto (fun N : ℕ ↦ ((Finset.range N).sum Λ) / N) atTop (𝓝 1) := by
  convert Dirichlet_vonMangoldt WIT (q := 1) (a := 1) isUnit_one with n
  · exact (Finset.filter_true_of_mem fun _ _ ↦ Subsingleton.eq_one _).symm
  · simp only [Nat.totient_one, Nat.cast_one, inv_one]
