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
  · simp only [Function.update_same]
    refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_
    rw [sub_ne_zero, ne_eq, one_eq_inv]
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_one
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

end vonMangoldt

namespace DirichletsThm

variable (q)

variable (a) in
open Classical in
/-- The function `F` used in the Wiener-Ikehara Theorem to prove Dirichlet's Theorem. -/
noncomputable
abbrev auxFun (s : ℂ) : ℂ :=
  (q.totient : ℂ)⁻¹ * (-deriv (LFunctionTrivChar₁ q) s / LFunctionTrivChar₁ q s -
    ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)), χ a⁻¹ * deriv (LFunction χ) s / LFunction χ s)

variable {q}

lemma auxFun_prop (ha : IsUnit a) :
    Set.EqOn (auxFun q a)
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
    Set.EqOn (L (vonMangoldt.residue_class a) - auxFun q a) (fun s ↦ (q.totient : ℂ)⁻¹ / (s - 1))
    {s | 1 < s.re} := by
  intro s hs
  simp only [Pi.sub_apply, auxFun_prop ha hs, sub_sub_cancel]

variable (a) in
/-- The L-series of the von Mangoldt function restricted to the prime residue class `a` mod `q`
is continuous on `re s ≥ 1` except for a single pole at `s = 1` with residue `(q.totient)⁻¹`. -/
lemma continuousOn_auxFun : ContinuousOn (auxFun q a) {s | 1 ≤ s.re} := by
  rw [show auxFun q a = fun s ↦ _ from rfl]
  simp only [auxFun, sub_eq_add_neg]
  refine continuousOn_const.mul <| ContinuousOn.add ?_ ?_
  · refine ContinuousOn.mono (continuousOn_neg_logDeriv_LFunctionTrivChar₁ q) fun s hs ↦ ?_
    have := LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ q) (s := s)
    tauto
  · simp only [← Finset.sum_neg_distrib, mul_div_assoc, ← mul_neg, ← neg_div]
    refine continuousOn_finset_sum _ fun χ hχ ↦ continuousOn_const.mul ?_
    replace hχ : χ ≠ 1 := by simpa only [ne_eq, Finset.mem_compl, Finset.mem_singleton] using hχ
    exact ContinuousOn.mono (continuousOn_neg_logDeriv_LFunction_of_nontriv hχ)
      fun _ hs ↦ LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs

open Filter Topology in
lemma not_continuousAt_LSeries_residue_class (ha : IsUnit a) :
  ¬ ContinuousAt (L <| vonMangoldt.residue_class a) 1 := by
  by_contra H
  have h : (1 : ℂ) ∈ {s | 1 ≤ s.re} := by
    simp only [Set.mem_setOf_eq, one_re, le_refl]
  have H₁ := H.continuousWithinAt (s := {s | 1 ≤ s.re})
  have H₂ := (continuousOn_auxFun a).continuousWithinAt h
  have H₃ := H₁.sub H₂


  stop
  have : Tendsto (L <| vonMangoldt.residue_class a) (𝓝[{s | 1 < s.re}] 1) (cocompact ℂ) := by
    refine (tendsto_congr' <| eventuallyEq_nhdsWithin_of_eqOn <| auxFun_prop' ha).mpr ?_
    refine tendsto_nhdsWithin_mono_left (t := {s | 1 ≤ s.re}) (fun ⦃s⦄ hs ↦ le_of_lt hs) ?_

    sorry
  have inst : NeBot <| nhdsWithin (1 : ℂ) {s | 1 < s.re} := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_


    refine mem_closure_iff_nhds.mpr fun t ht ↦ ?_
    refine Set.inter_nonempty.mpr ?_

    sorry
  refine not_continuousAt_of_tendsto this ?_ ?_
  · sorry
  · sorry

lemma abscissaOfAbsConv_vonMangoldt_residue_class (ha : IsUnit a) :
    LSeries.abscissaOfAbsConv (vonMangoldt.residue_class a) = 1 := by
  refine le_antisymm ?_ ?_
  · rw [vonMangoldt.residue_class_eq ha]
    refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun h hy ↦ ?_
    refine (LSeriesSummable.sum fun χ _ ↦ LSeriesSummable.smul _ ?_).smul _
    exact χ.LSeriesSummable_mul <| ArithmeticFunction.LSeriesSummable_vonMangoldt <|
      by simp only [ofReal_re, hy]
  · by_contra! H
    change LSeries.abscissaOfAbsConv (vonMangoldt.residue_class a) < (1 : ℂ).re at H
    exact not_continuousAt_LSeries_residue_class ha <|
      HasDerivAt.continuousAt <| LSeries_hasDerivAt H

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
  refine WIT (F := auxFun q a) (fun n ↦ ?_) ?_ ?_
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
