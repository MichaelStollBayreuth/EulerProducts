import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Complex
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.Normed.Field.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# More results on L-series
-/

@[inherit_doc]
scoped[LSeries.notation] notation "L" => LSeries

/-- We introduce notation `↗f` for `f` interpreted as a function `ℕ → ℂ`.

Let `R` be a ring with a coercion to `ℂ`. Then we can write `↗χ` when `χ : DirichletCharacter R`
or `↗f` when `f : ArithmeticFunction R` or simply `f : N → R` with a coercion from `ℕ` to `N`
as an argument to `LSeries`, `LSeriesHasSum`, `LSeriesSummable` etc. -/
scoped[LSeries.notation] notation:max "↗" f:max => fun n : ℕ ↦ (f n : ℂ)

open scoped LSeries.notation

open Complex LSeries

/-!
### Convergence of L-series
-/

-- for LSeries.Convergence:
lemma LSeries.abscissaOfAbsConv_congr {f g : ℕ → ℂ} (h : ∀ n ≠ 0, f n = g n) :
    abscissaOfAbsConv f = abscissaOfAbsConv g :=
  congr_arg sInf <| congr_arg _ <| Set.ext fun x ↦ LSeriesSummable_congr x h

/-!
# Differentiability and derivatives of L-series

## Main results

* We show that the `LSeries` of `f` is differentiable at `s` when `re s` is greater than
  the abscissa of absolute convergence of `f` (`LSeries.hasDerivAt`) and that its derivative
  there isthe negative of the `LSeries` of the point-wise product `log * f` (`LSeries.deriv`).

* We prove similar results for iterated derivatives (`LSeries.iteratedDeriv`).

* We use this to show that `LSeries f` is holomorphic on the right half-plane of
  absolute convergence (`LSeries.analyticOn`).

## Implementation notes

We introduce `LSeries.logMul` as an abbreviation for the point-wise product `log * f`, to avoid
the problem that this expression does not type-check. Similarly, we make use of the abbreviation
`LSeries.logPowMul n f` for `log^n * f`.
-/

-- Should this go into its own file (because it needs `EReal`s, it doesn't fit well in some existing file),
-- together with versions for the left, upper and lower half-planes?
/-- An open right half-plane is open in the complex plane. -/
lemma Complex.isOpen_rightHalfPlane (x : EReal) : IsOpen {z : ℂ | x < z.re} :=
  isOpen_lt continuous_const <| EReal.continuous_coe_iff.mpr continuous_re


/-!
### Multiplication by (powers of) log
-/

/-- The (point-wise) product of `log : ℕ → ℂ` with `f`. -/
noncomputable abbrev LSeries.logMul (f : ℕ → ℂ) (n : ℕ) : ℂ := log n * f n

/-- A bound for the norm of the L-series terms of `f`, multiplied by `log`, in terms
of the norm at a complex number with larger real part. -/
lemma LSeries.norm_term_logMul_le_of_re_lt_re (f : ℕ → ℂ) {s s' : ℂ} (h : s.re < s'.re) (n : ℕ) :
    ‖term (logMul f) s' n‖ ≤ ‖term f s n‖ / (s'.re - s.re) := by
  have hwz : 0 < s'.re - s.re := sub_pos.mpr h
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [term_zero, norm_zero, zero_div, le_refl]
  simp only [term_of_ne_zero hn.ne']
  rw [mul_div_assoc, norm_mul]
  refine mul_le_mul_of_nonneg_right (norm_log_natCast_le_rpow_div n hwz) (norm_nonneg _)|>.trans ?_
  rw [mul_comm_div, mul_div, div_le_div_right hwz, norm_div, norm_div, norm_natCast_cpow_of_pos hn,
    norm_natCast_cpow_of_pos hn, mul_div_left_comm, ← Real.rpow_sub <| Nat.cast_pos.mpr hn,
    sub_sub_cancel_left, Real.rpow_neg n.cast_nonneg, div_eq_mul_inv]

/-- If the L-series of `f` is summable at `s` and `re s < re s'`, then the L-series of the
point-wise product of `log` with `f` is summable at `s'`. -/
lemma LSeriesSummable.logMul_of_re_lt_re {f : ℕ → ℂ} {s s' : ℂ} (h : s.re < s'.re)
    (hf : LSeriesSummable f s) :
    LSeriesSummable (logMul f) s' := by
  rw [LSeriesSummable, ← summable_norm_iff] at hf ⊢
  exact (hf.div_const _).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_term_logMul_le_of_re_lt_re f h)

/-- If the L-series of the point-wise product of `log` with `f` is summable at `s`, then
so is the L-series of `f`. -/
lemma LSeriesSummable.of_logMul {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable (logMul f) s) :
    LSeriesSummable f s := by
  refine h.norm.of_norm_bounded_eventually_nat (fun n ↦ ‖term (logMul f) s n‖) ?_
  simp only [norm_div, natCast_log, norm_mul, Filter.eventually_atTop]
  refine ⟨3, fun n hn ↦ ?_⟩
  simp only [term_of_ne_zero (show n ≠ 0 by omega), logMul, norm_div, norm_mul]
  conv => enter [1, 1]; rw [← one_mul (‖f n‖)]
  gcongr
  rw [← natCast_log, norm_eq_abs, abs_ofReal,
    _root_.abs_of_nonneg <| Real.log_nonneg <| by norm_cast; linarith, ← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) <| (Real.exp_one_lt_d9.trans <| by norm_num).le.trans <|
    (show (3 : ℝ) ≤ n by exact_mod_cast hn)

/-- The abscissa of absolute convergence of the point-wise product of `log` and `f`
is the same as that of `f`. -/
@[simp]
lemma abscissaOfAbsConv_logMul {f : ℕ → ℂ} :
    abscissaOfAbsConv (logMul f) = abscissaOfAbsConv f := by
  refine le_antisymm ?_ ?_
  · refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun y hy ↦ ?_
    obtain ⟨x, hx₁, hx₂⟩ := EReal.exists_between_coe_real hy
    have hx₁' : abscissaOfAbsConv f < ((x : ℂ).re) := by simp only [ofReal_re, hx₁]
    have hx₂' : (x : ℂ).re < (y : ℂ).re := by simp only [ofReal_re, EReal.coe_lt_coe_iff.mp hx₂]
    exact (LSeriesSummable_of_abscissaOfAbsConv_lt_re hx₁').logMul_of_re_lt_re hx₂'
  · refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun y hy ↦ ?_
    have hy' : abscissaOfAbsConv (logMul f) < ((y : ℂ).re) := by simp only [ofReal_re, hy]
    exact (LSeriesSummable_of_abscissaOfAbsConv_lt_re hy').of_logMul

/-- The (point-wise) product of the `n`th power of `log` with `f`. -/
noncomputable abbrev logPowMul (n : ℕ) (f : ℕ → ℂ) (m : ℕ) : ℂ :=
  (log m) ^ n * f m

lemma logPowMul_zero (f : ℕ → ℂ) : logPowMul 0 f = f := by
  ext
  simp only [logPowMul, pow_zero, one_mul]

lemma logPowMul_succ (n : ℕ) (f : ℕ → ℂ) : logPowMul n.succ f = logMul (logPowMul n f) := by
  ext
  simp only [logPowMul, pow_succ, mul_assoc, logMul]

lemma logPowMul_succ' (n : ℕ) (f : ℕ → ℂ) : logPowMul n.succ f = logPowMul n (logMul f) := by
  ext n
  simp only [logPowMul, pow_succ, logMul, ← mul_assoc]
  rw [mul_comm (log n)]

/-- The abscissa of absolute convergence of the point-wise product of a power of `log` and `f`
is the same as that of `f`. -/
@[simp]
lemma absicssaOfAbsConv_logPowMul {f : ℕ → ℂ} {n : ℕ} :
    abscissaOfAbsConv (logPowMul n f) = abscissaOfAbsConv f := by
  induction' n with n ih
  · simp only [Nat.zero_eq, logPowMul_zero]
  · rwa [logPowMul_succ, abscissaOfAbsConv_logMul]


/-!
### The derivative of an L-series
-/

/-- The derivative of the terms of an L-series. -/
lemma LSeries.hasderivat_term (f : ℕ → ℂ) (n : ℕ) (s : ℂ) :
    HasDerivAt (fun z ↦ term f z n) (-(term (logMul f) s n)) s := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [term_zero, neg_zero, hasDerivAt_const]
  simp only [term_of_ne_zero hn.ne']
  rw [← neg_div, ← neg_mul, mul_comm, mul_div_assoc]
  simp_rw [div_eq_mul_inv, ← cpow_neg]
  refine HasDerivAt.const_mul (f n) ?_
  rw [mul_comm, ← mul_neg_one (Complex.log n), ← mul_assoc]
  exact (hasDerivAt_neg' s).const_cpow (Or.inl <| Nat.cast_ne_zero.mpr hn.ne')

/-- The derivative of the terms of an L-series. -/
lemma LSeries.deriv_term (f : ℕ → ℂ) (n : ℕ) (s : ℂ) :
    deriv (fun z ↦ term f z n) s = -(term (logMul f) s n) :=
  (hasderivat_term f n s).deriv

/-- The derivative of the terms of an L-series. -/
lemma LSeries.deriv_term' (f : ℕ → ℂ) (n : ℕ) :
    deriv (fun z ↦ term f z n) = fun s ↦ -(term (logMul f) s n) := by
  ext
  exact deriv_term ..

/-- If `re s` is greater than the abscissa of absolute convergence of `f`, then the L-series
of `f` is differentiable with derivative the negative of the L-series of the point-wise
product of `log` with `f`. -/
lemma LSeries.hasDerivAt {f : ℕ → ℂ} {s : ℂ} (h : abscissaOfAbsConv f < s.re) :
    HasDerivAt (LSeries f) (- LSeries (logMul f) s) s := by
  -- The L-series of `f` is summable at some real `x < re s`.
  obtain ⟨x, h', hf⟩ := LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re h
  change HasDerivAt (fun z ↦ LSeries f z) ..
  simp only [LSeries, ← tsum_neg]
  -- We work in the right half-plane `re z > (x + re s)/2`.
  let S : Set ℂ := {z | (x + s.re) / 2 < z.re}
  have hop : IsOpen S := isOpen_lt continuous_const continuous_re
  have hpr : IsPreconnected S := (convex_halfspace_re_gt _).isPreconnected
  have hmem : s ∈ S := by
    simp only [S, Set.mem_setOf_eq]
    linarith only [h']
  -- To get a uniform summable bound for the derivative series, we use that we
  -- have summability of the L-series of `log * f` at `(x + s)/2`.
  have hx : (x : ℂ).re < ((x + s) / 2).re := by
    simp only [add_re, ofReal_re, div_ofNat_re, sub_re]
    linarith only [h']
  have hf' := hf.logMul_of_re_lt_re hx
  rw [LSeriesSummable, ← summable_norm_iff] at hf'
  -- Show that the terms have the correct derivative.
  refine hasDerivAt_tsum_of_isPreconnected hf' hop hpr (fun n s _ ↦ hasderivat_term f n s)
    (fun n z hz ↦ ?_) hmem (hf.of_re_le_re <| ofReal_re x ▸ h'.le) hmem
  -- Show that the derivative series is uniformly bounded term-wise.
  simp only [norm_neg, norm_div, norm_mul]
  refine norm_term_le_of_re_le_re _ ?_ _
  simp only [Set.mem_setOf_eq, div_ofNat_re, add_re, ofReal_re, S] at hz ⊢
  exact hz.le

/-- If `re z` is greater than the abscissa of absolute convergence of `f`, then
the derivative of this L-series is the negative of the L-series of `log * f`. -/
protected
lemma LSeries.deriv {f : ℕ → ℂ} {z : ℂ} (h : abscissaOfAbsConv f < z.re) :
    deriv (LSeries f) z = - LSeries (logMul f) z :=
  (hasDerivAt h).deriv

/-- The derivative of the L-series of `f` agrees with the negative of the L-series of
`log * f` on the right half-plane of absolute convergence. -/
protected
lemma LSeries.deriv_eqOn {f : ℕ → ℂ} :
    {z | abscissaOfAbsConv f < z.re}.EqOn (deriv (LSeries f)) (- LSeries (logMul f)) :=
  deriv_eqOn (isOpen_rightHalfPlane _) fun _ hz ↦ (hasDerivAt hz).hasDerivWithinAt


/-!
### Higher derivatives of L-series
-/

/-- The higher derivatives of the terms of an L-series. -/
lemma LSeries.iteratedDeriv_term (f : ℕ → ℂ) (m n : ℕ) (s : ℂ) :
    iteratedDeriv m (fun z ↦ term f z n) s =
      (-1) ^ m * (term (logPowMul m f) s n) := by
  induction' m with m ih generalizing f s
  · simp only [Nat.zero_eq, iteratedDeriv_zero, pow_zero, logPowMul_zero, one_mul]
  · have ih' : iteratedDeriv m (fun z ↦ term (logMul f) z n) =
        fun s ↦ (-1) ^ m * (term (logPowMul m (logMul f)) s n) :=
      funext <| ih (logMul f)
    rw [iteratedDeriv_succ', deriv_term' f n, iteratedDeriv_neg, ih', neg_mul_eq_neg_mul,
      logPowMul_succ', pow_succ, neg_one_mul]

/-- If `re s` is greater than the abscissa of absolute convergence of `f`, then
the `n`th derivative of this L-series is `(-1)^n` times the L-series of `log^n * f`. -/
protected
lemma LSeries.iteratedDeriv {f : ℕ → ℂ} (n : ℕ) {s : ℂ} (h : abscissaOfAbsConv f < s.re) :
    iteratedDeriv n (LSeries f) s = (-1) ^ n * LSeries (logPowMul n f) s := by
  induction' n with n ih generalizing s
  · simp only [Nat.zero_eq, iteratedDeriv_zero, pow_zero, logPowMul_zero, one_mul]
  · have ih' : {z | abscissaOfAbsConv f < z.re}.EqOn (iteratedDeriv n (LSeries f))
        ((-1) ^ n * LSeries (logPowMul n f)) := by
      exact fun _ hs ↦ ih hs
    have := derivWithin_congr ih' (ih h)
    simp_rw [derivWithin_of_isOpen (isOpen_rightHalfPlane _) h] at this
    rw [iteratedDeriv_succ, this]
    change deriv (fun z ↦ (-1) ^ n * LSeries (logPowMul n f) z) s = _
    rw [deriv_const_mul_field', pow_succ', mul_assoc, neg_one_mul]
    simp only [LSeries.deriv <| absicssaOfAbsConv_logPowMul.symm ▸ h, logPowMul_succ]


/-!
### The L-series is holomorphic
-/

/-- The L-series of `f` is complex differentiable in its open half-plane of absolute
convergence. -/
lemma LSeries.differentiableOn (f : ℕ → ℂ) :
    DifferentiableOn ℂ (LSeries f) {s | abscissaOfAbsConv f < s.re} :=
  fun _ hz ↦ (hasDerivAt hz).differentiableAt.differentiableWithinAt

/-- The L-series of `f` is holomorphic on its open half-plane of absolute convergence. -/
lemma LSeries.analyticOn (f : ℕ → ℂ) :
    AnalyticOn ℂ (LSeries f) {s | abscissaOfAbsConv f < s.re} :=
  (LSeries.differentiableOn f).analyticOn <| isOpen_rightHalfPlane (abscissaOfAbsConv f)



/-!
### Multiplication of L-series
-/

open BigOperators

namespace LSeries

/-- Dirichlet convolution of two sequences. -/
noncomputable def convolution {R : Type*} [Semiring R] (f g : ℕ → R) : ℕ → R :=
  fun n ↦ ∑ p in n.divisorsAntidiagonal, f p.1 * g p.2

@[inherit_doc]
scoped[LSeries.notation] infixl:70 " ⍟ " => convolution

open scoped LSeries.notation

lemma convolution_def {R : Type*} [Semiring R] (f g : ℕ → R) (n : ℕ) :
    (f ⍟ g) n = ∑ p in n.divisorsAntidiagonal, f p.1 * g p.2 :=
  rfl

lemma convolution_def' {R : Type*} [Semiring R] (f g : ℕ → R) :
    f ⍟ g = fun n ↦ ∑ p in n.divisorsAntidiagonal, f p.1 * g p.2 :=
  rfl

@[simp]
lemma convolution_zero {R : Type*} [Semiring R] (f g : ℕ → R) : (f ⍟ g) 0 = 0 := by
  simp only [convolution_def', Nat.divisorsAntidiagonal_zero, Finset.sum_empty]

lemma _root_.ArithmeticFunction.mul_to_convolution {R : Type*} [Semiring R]
    (f g : ArithmeticFunction R) :
    f ⍟ g = (f * g :) := by
  ext
  simp only [convolution_def, ArithmeticFunction.mul_apply]

open Set Nat in
lemma term_convolution (f g : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    term (f ⍟ g) s n =
      ∑' (b : (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {n}),
        term f s b.val.1 * term g s b.val.2 := by
  let m : ℕ × ℕ → ℕ := fun p ↦ p.1 * p.2
  let h : ℕ × ℕ → ℂ := fun x ↦ term f s x.1 * term g s x.2
  rcases n.eq_zero_or_pos with rfl | hn
  · trans 0 -- show that both sides vanish when `n = 0`
    · -- by definition, the left hand sum is over the empty set
      exact term_zero ..
    · -- the right hand sum is over the union below, but in each term, one factor is always zero
      have hS : m ⁻¹' {0} = {0} ×ˢ univ ∪ (univ \ {0}) ×ˢ {0} := by
        ext
        simp only [m, mem_preimage, mem_singleton_iff, _root_.mul_eq_zero, mem_union, mem_prod,
          mem_univ, mem_diff]
        tauto
      rw [tsum_congr_set_coe h hS,
        tsum_union_disjoint (Disjoint.set_prod_left disjoint_sdiff_right ..) ?_ ?_,
          -- (hsum.subtype _) (hsum.subtype _),
        tsum_setProd_singleton_left 0 _ h, tsum_setProd_singleton_right _ 0 h]
      · simp only [h, term_zero, zero_mul, tsum_zero, mul_zero, add_zero]
      · simp only [h, Function.comp_def]
        convert summable_zero with p
        rw [Set.mem_singleton_iff.mp p.prop.1, term_zero, zero_mul]
      · simp only [h, Function.comp_def]
        convert summable_zero with p
        rw [Set.mem_singleton_iff.mp p.prop.2, term_zero, mul_zero]
  -- now `n > 0`
  have H : n.divisorsAntidiagonal = m ⁻¹' {n} := by
    ext x
    replace hn := hn.ne' -- for `tauto` below
    simp only [Finset.mem_coe, mem_divisorsAntidiagonal, m, mem_preimage, mem_singleton_iff]
    tauto
  rw [← H, Finset.tsum_subtype' n.divisorsAntidiagonal h, term_of_ne_zero hn.ne',
    convolution_def, Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  simp only [h]
  obtain ⟨hp, hn₀⟩ := mem_divisorsAntidiagonal.mp hp
  have ⟨hp₁, hp₂⟩ := mul_ne_zero_iff.mp <| hp.symm ▸ hn₀
  rw [term_of_ne_zero hp₁ f s, term_of_ne_zero hp₂ g s, mul_comm_div, div_div,
    ← mul_div_assoc, ← natCast_mul_natCast_cpow, ← Nat.cast_mul, mul_comm p.2, hp]

end LSeries

open scoped LSeries.notation

open Set in
/-- The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
equals the product of their L-series, assuming both L-series converge. -/
lemma LSeriesHasSum.convolution {f g : ℕ → ℂ} {s a b : ℂ} (hf : LSeriesHasSum f s a)
    (hg : LSeriesHasSum g s b) :
    LSeriesHasSum (f ⍟ g) s (a * b) := by
  simp only [LSeriesHasSum]
  have hsum := summable_mul_of_summable_norm hf.summable.norm hg.summable.norm
  let m : ℕ × ℕ → ℕ := fun p ↦ p.1 * p.2
  convert (HasSum.mul hf hg hsum).tsum_fiberwise m with n
  exact term_convolution ..

/-- The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
equals the product of their L-series, assuming both L-series converge. -/
lemma LSeries_convolution {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeries (f ⍟ g) s = LSeries f s * LSeries g s :=
  (LSeriesHasSum.convolution hf.LSeriesHasSum hg.LSeriesHasSum).LSeries_eq

/-- The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
equals the product of their L-series in their common half-plane of absolute convergence. -/
lemma LSeries_convolution' {f g : ℕ → ℂ} {s : ℂ}
    (hf : abscissaOfAbsConv f < s.re) (hg : abscissaOfAbsConv g < s.re) :
    LSeries (f ⍟ g) s = LSeries f s * LSeries g s :=
  LSeries_convolution (LSeriesSummable_of_abscissaOfAbsConv_lt_re hf)
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re hg)

/-- The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
is summable when both L-series are summable. -/
lemma LSeriesSummable_convolution {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeriesSummable (f ⍟ g) s :=
  (LSeriesHasSum.convolution hf.LSeriesHasSum hg.LSeriesHasSum).LSeriesSummable

namespace ArithmeticFunction

lemma LSeriesHasSum.mul {f g : ArithmeticFunction ℂ} {s a b : ℂ} (hf : LSeriesHasSum ↗f s a)
    (hg : LSeriesHasSum ↗g s b) :
    LSeriesHasSum ↗(f * g) s (a * b) := by
  rw [← mul_to_convolution]
  exact LSeriesHasSum.convolution hf hg

lemma LSeries_mul {f g : ArithmeticFunction ℂ} {s : ℂ} (hf : LSeriesSummable ↗f s)
    (hg : LSeriesSummable ↗g s) :
    LSeries ↗(f * g) s = LSeries ↗f s * LSeries ↗g s := by
  rw [← mul_to_convolution]
  exact LSeries_convolution hf hg

lemma LSeries_mul' {f g : ArithmeticFunction ℂ} {s : ℂ}
    (hf : abscissaOfAbsConv ↗f < s.re) (hg : abscissaOfAbsConv ↗g < s.re) :
    LSeries ↗(f * g) s = LSeries ↗f s * LSeries ↗g s := by
  rw [← mul_to_convolution]
  exact LSeries_convolution' hf hg

lemma LSeriesSummable_mul {f g : ArithmeticFunction ℂ} {s : ℂ} (hf : LSeriesSummable ↗f s)
    (hg : LSeriesSummable ↗g s) :
    LSeriesSummable ↗(f * g) s := by
  rw [← mul_to_convolution]
  exact LSeriesSummable_convolution hf hg

end ArithmeticFunction
