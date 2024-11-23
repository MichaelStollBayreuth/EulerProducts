import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed


open Complex

/-!
### The L-series of Λ restricted to a residue class
-/

open LSeries DirichletCharacter

namespace ArithmeticFunction.vonMangoldt

variable {q : ℕ} (a : ZMod q) [NeZero q]

open Classical in
/-- The auxiliary function used, e.g., with the Wiener-Ikehara Theorem to prove
Dirichlet's Theorem. On `re s > 1`, it agrees with the L-series of the von Mangoldt
function restricted to the residue class `a : ZMod q` minus the principal part
`(q.totient)⁻¹/(s-1)` of the pole at `s = 1`; see `DirichletsThm.auxFun_prop`. -/
noncomputable
abbrev auxFun (s : ℂ) : ℂ :=
  (q.totient : ℂ)⁻¹ * (-deriv (LFunctionTrivChar₁ q) s / LFunctionTrivChar₁ q s -
    ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)), χ a⁻¹ * deriv (LFunction χ) s / LFunction χ s)

/-- The auxiliary function is continuous away from the zeros of the L-functions of the Dirichlet
characters mod `q` (including at `s = 1`). -/
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
The statement as given here in terms auf `DirichletsThm.auxFun` is equivalent. -/
lemma continuousOn_auxFun : ContinuousOn (auxFun a) {s | 1 ≤ s.re} := by
  refine (continuousOn_auxFun' a).mono fun s hs ↦ ?_
  rcases eq_or_ne s 1 with rfl | hs₁
  · simp only [ne_eq, Set.mem_setOf_eq, true_or]
  · simp only [ne_eq, Set.mem_setOf_eq, hs₁, false_or]
    exact fun χ ↦ LFunction_ne_zero_of_one_le_re χ (.inr hs₁) <| Set.mem_setOf.mp hs

variable {a}

open scoped LSeries.notation

/-- The auxiliary function agrees on `re s > 1` with the L-series of the von Mangoldt function
restricted to the residue class `a : ZMod q` minus the principal part `(q.totient)⁻¹/(s-1)`
of its pole at `s = 1`. -/
lemma eqOn_auxFun (ha : IsUnit a) :
    Set.EqOn (auxFun a)
      (fun s ↦ L ↗(residueClass a) s - (q.totient : ℂ)⁻¹ / (s - 1))
      {s | 1 < s.re} := by
  intro s hs
  replace hs := Set.mem_setOf.mp hs
  simp only [LSeries_residueClass_eq ha hs, auxFun]
  rw [neg_div, ← neg_add', mul_neg, ← neg_mul, div_eq_mul_one_div (q.totient : ℂ)⁻¹,
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
    Function.update_noteq hs₁, LFunctionTrivChar, add_div,
    mul_div_mul_left _ _ (sub_ne_zero_of_ne hs₁)]
  conv_lhs => enter [2, 1]; rw [← mul_one (LFunction ..)]
  rw [mul_comm _ 1, mul_div_mul_right _ _ <| LFunction_ne_zero_of_one_le_re 1 (.inr hs₁) hs.le]

/-- The auxiliary function takes real values for real arguments `x > 1`. -/
lemma auxFun_real (ha : IsUnit a) {x : ℝ} (hx : 1 < x) : auxFun a x = (auxFun a x).re := by
  rw [eqOn_auxFun ha hx]
  simp only [sub_re, ofReal_sub]
  congr 1
  · rw [LSeries, re_tsum <| LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      (abscissaOfAbsConv_residueClass_le_one a).trans_lt <| by norm_cast]
    push_cast
    refine tsum_congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [term_zero, zero_re, ofReal_zero]
    · simp only [term_of_ne_zero hn, ← ofReal_natCast n, ← ofReal_cpow n.cast_nonneg, ← ofReal_div,
        ofReal_re]
  · rw [show (q.totient : ℂ) = (q.totient : ℝ) from rfl, ← ofReal_one, ← ofReal_sub, ← ofReal_inv,
      ← ofReal_div, ofReal_re]

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- As `x` approaches `1` from the right along the real axis, the L-series of
`ArithmeticFunction.vonMangoldt.residueClass` is bounded below by `(q.totient)⁻¹/(x-1) - C`. -/
lemma LSeries_residueClass_lower_bound (ha : IsUnit a) :
    ∃ C : ℝ, ∀ {x : ℝ} (_ : x ∈ Set.Ioc 1 2),
      (q.totient : ℝ)⁻¹ / (x - 1) - C ≤ ∑' n, residueClass a n / (n : ℝ) ^ x := by
  have H {x : ℝ} (hx : 1 < x) :
      ∑' n, residueClass a n / (n : ℝ) ^ x = (auxFun a x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
    refine ofReal_injective ?_
    simp only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast,
      ofReal_add, ofReal_inv, ofReal_sub, ofReal_one]
    simp_rw [← auxFun_real ha hx, eqOn_auxFun ha <| Set.mem_setOf.mpr (ofReal_re x ▸ hx),
      sub_add_cancel, LSeries, term]
    refine tsum_congr fun n ↦ ?_
    split_ifs with hn
    · simp only [hn, residueClass_apply_zero, ofReal_zero, zero_div]
    · rfl
  have : ContinuousOn (fun x : ℝ ↦ (auxFun a x).re) (Set.Icc 1 2) :=
    continuous_re.continuousOn.comp (t := Set.univ) (continuousOn_auxFun a)
      (fun ⦃x⦄ a ↦ trivial) |>.comp continuous_ofReal.continuousOn fun x hx ↦ by
        simpa only [Set.mem_setOf_eq, ofReal_re] using hx.1
  obtain ⟨C, hC⟩ := bddBelow_def.mp <| IsCompact.bddBelow_image isCompact_Icc this
  replace hC {x : ℝ} (hx : x ∈ Set.Icc 1 2) : C ≤ (auxFun a x).re :=
    hC (auxFun a x).re <| Set.mem_image_of_mem (fun x : ℝ ↦ (auxFun a x).re) hx
  refine ⟨-C, fun {x} hx ↦ ?_⟩
  rw [H hx.1, add_comm, sub_neg_eq_add, add_le_add_iff_left]
  exact hC <| Set.mem_Icc_of_Ioc hx

open vonMangoldt Filter Topology in
/-- The function `n ↦ Λ n / n` restricted to primes in an invertible residue class
is not summable. This then implies that there must be infinitely many such primes. -/
lemma not_summable_residueClass_prime_div (ha : IsUnit a) :
    ¬ Summable fun n : ℕ ↦ (if n.Prime then residueClass a n else 0) / n := by
  intro H
  have key : Summable fun n : ℕ ↦ residueClass a n / n := by
    convert (summable_residueClass_non_primes_div a).add H using 2 with n
    simp only [← add_div, ite_add_ite, zero_add, add_zero, ite_self]
  let C := ∑' n, residueClass a n / n
  have H₁ {x : ℝ} (hx : 1 < x) : ∑' n, residueClass a n / (n : ℝ) ^ x ≤ C := by
    refine tsum_le_tsum (fun n ↦ ?_) ?_ key
    · rcases n.eq_zero_or_pos with rfl | hn
      · simp only [Nat.cast_zero, Real.zero_rpow (zero_lt_one.trans hx).ne', div_zero, le_refl]
      · refine div_le_div_of_nonneg_left (residueClass_nonneg a _) (mod_cast hn) ?_
        conv_lhs => rw [← Real.rpow_one n]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_cast) hx.le
    · exact summable_real_of_abscissaOfAbsConv_lt <|
        (abscissaOfAbsConv_residueClass_le_one a).trans_lt <| mod_cast hx
  obtain ⟨C', hC'⟩ := LSeries_residueClass_lower_bound ha
  have H₁ {x} (hx : x ∈ Set.Ioc 1 2) : (q.totient : ℝ)⁻¹ ≤ (C + C') * (x - 1) :=
    (div_le_iff₀ <| sub_pos.mpr hx.1).mp <|
      sub_le_iff_le_add.mp <| (hC' hx).trans (H₁ hx.1)
  have hq : 0 < (q.totient : ℝ)⁻¹ := inv_pos.mpr (mod_cast q.totient.pos_of_neZero)
  rcases le_or_lt (C + C') 0 with h₀ | h₀
  · have := hq.trans_le (H₁ (Set.right_mem_Ioc.mpr one_lt_two))
    rw [show (2 : ℝ) - 1 = 1 by norm_num, mul_one] at this
    exact (this.trans_le h₀).false
  · obtain ⟨ξ, hξ₁, hξ₂⟩ : ∃ ξ ∈ Set.Ioc 1 2, (C + C') * (ξ - 1) < (q.totient : ℝ)⁻¹ := by
      refine ⟨min (1 + (q.totient : ℝ)⁻¹ / (C + C') / 2) 2, ⟨?_, min_le_right ..⟩, ?_⟩
      · simpa only [lt_inf_iff, lt_add_iff_pos_right, Nat.ofNat_pos, div_pos_iff_of_pos_right,
          Nat.one_lt_ofNat, and_true] using div_pos hq h₀
      · rw [← min_sub_sub_right, add_sub_cancel_left, ← lt_div_iff₀' h₀]
        exact (min_le_left ..).trans_lt <| div_lt_self (div_pos hq h₀) one_lt_two
    exact ((H₁ hξ₁).trans_lt hξ₂).false

end ArithmeticFunction.vonMangoldt

/-!
### Dirichlet's Theorem
-/

section DirichletsTheorem

namespace Nat

open ArithmeticFunction vonMangoldt

variable {q : ℕ} [NeZero q] {a : ZMod q}
/-- **Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positive
integer and `a : ZMod q` is a unit, then there are infintely many prime numbers `p`
such that `(p : ZMod q) = a`. -/
theorem setOf_prime_and_eq_mod_infinite (ha : IsUnit a) :
    {p : ℕ | p.Prime ∧ (p : ZMod q) = a}.Infinite := by
  by_contra H
  rw [Set.not_infinite] at H
  exact not_summable_residueClass_prime_div ha <|
    summable_of_finite_support <| support_residueClass_prime_div a ▸ H

/-- **Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positive
integer and `a : ZMod q` is a unit, then there are infintely many prime numbers `p`
such that `(p : ZMod q) = a`. -/
theorem forall_exists_prime_gt_and_eq_mod (ha : IsUnit a) (n : ℕ) :
    ∃ p > n, p.Prime ∧ (p : ZMod q) = a := by
  obtain ⟨p, hp₁, hp₂⟩ := Set.infinite_iff_exists_gt.mp (setOf_prime_and_eq_mod_infinite ha) n
  exact ⟨p, hp₂.gt, Set.mem_setOf.mp hp₁⟩

end Nat

end DirichletsTheorem

/-!
### Statement of a version of the Wiener-Ikehara Theorem
-/

open scoped LSeries.notation

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

open Filter ArithmeticFunction Topology

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
  refine WIT (F := vonMangoldt.auxFun a) (fun n ↦ ?_) ?_ ?_
  · exact Set.indicator_apply_nonneg fun _ ↦ vonMangoldt_nonneg
  · convert vonMangoldt.eqOn_auxFun ha with s
    push_cast
    rfl
  · exact vonMangoldt.continuousOn_auxFun a

/-- The *Wiener-Ikehara Theorem* implies the *Prime Number Theorem* in the form that
`ψ x ∼ x`, where `ψ x = ∑ n < x, Λ n` and `Λ` is the von Mangoldt function. -/
theorem PNT_vonMangoldt (WIT : WienerIkeharaTheorem) :
    Tendsto (fun N : ℕ ↦ ((Finset.range N).sum Λ) / N) atTop (𝓝 1) := by
  convert Dirichlet_vonMangoldt WIT (q := 1) (a := 1) isUnit_one with n
  · exact (Finset.filter_true_of_mem fun _ _ ↦ Subsingleton.eq_one _).symm
  · simp only [Nat.totient_one, Nat.cast_one, inv_one]
