import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.QuadraticNonvanishing
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Logarithms of Euler Products

Here we consider `f : ℕ →*₀ ℂ` and the goal is to prove that
`exp (∑ p in Primes, log (1 - f p)⁻¹) = ∑ n : ℕ, f n`
under suitable conditions on `f`.
-/
-- Mathlib.NumberTheory.EulerProduct.ExpLog

open Complex

attribute [fun_prop] DifferentiableAt.clog

open Topology in
/-- If `f : α → ℂ` is summable, then so is `n ↦ -log (1 - f n)`. -/
lemma Summable.neg_clog_one_sub {α  : Type*} {f : α → ℂ} (hsum : Summable f) :
    Summable (fun n ↦ -log (1 - f n)) := by
  have hg : DifferentiableAt ℂ (fun z ↦ -log (1 - z)) 0 := by
    have : 1 - 0 ∈ slitPlane := (sub_zero (1 : ℂ)).symm ▸ one_mem_slitPlane
    fun_prop (disch := assumption)
  have : (fun z ↦ -log (1 - z)) =O[𝓝 0] id := by
    simpa only [sub_zero, log_one, neg_zero] using hg.isBigO_sub
  exact this.comp_summable hsum

namespace EulerProduct

/-- A variant of the Euler Product formula in terms of the exponential of a sum of logarithms. -/
theorem exp_tsum_primes_log_eq_tsum {f : ℕ →*₀ ℂ} (hsum : Summable (‖f ·‖)) :
    exp (∑' p : Nat.Primes, -log (1 - f p)) = ∑' n : ℕ, f n := by
  have hs {p : ℕ} (hp : 1 < p) : ‖f p‖ < 1 := hsum.of_norm.norm_lt_one (f := f.toMonoidHom) hp
  have hp (p : Nat.Primes) : 1 - f p ≠ 0 :=
    fun h ↦ norm_one (α := ℂ) ▸ (sub_eq_zero.mp h) ▸ hs p.prop.one_lt |>.false
  have H := hsum.of_norm.neg_clog_one_sub.subtype {p | p.Prime} |>.hasSum.cexp.tprod_eq
  simp only [Set.coe_setOf, Set.mem_setOf_eq, Function.comp_apply] at H
  conv at H => enter [1, 1, p]; rw [exp_neg, exp_log (hp p)]
  exact H.symm.trans <| eulerProduct_completely_multiplicative_tprod hsum

/-- A variant of the Euler Product formula in terms of the exponential of a sum of logarithms. -/
theorem exp_tsum_primes_log_eq_tsum' {f : ℕ → ℂ} (h₀ : f 0 = 0) (h₁ : f 1 = 1)
    (hf : ∀ m n, f (m * n) = f m * f n) (hsum : Summable (‖f ·‖)) :
    exp (∑' p : Nat.Primes, -log (1 - f p)) = ∑' n : ℕ, f n :=
  exp_tsum_primes_log_eq_tsum (f := {toFun := f, map_zero' := h₀, map_one' := h₁, map_mul' := hf})
    hsum

end EulerProduct

section BigO

open Topology Asymptotics Filter

-- [Mathlib.Analysis.InnerProductSpace.Basic, Mathlib.Analysis.Complex.Asymptotics,
--  Mathlib.Analysis.Normed.Algebra.Exponential]
lemma Complex.isBigO_comp_ofReal {f g : ℂ → ℂ} {x : ℝ} (h : f =O[𝓝 (x : ℂ)] g) :
    (fun y : ℝ ↦ f y) =O[𝓝 x] (fun y : ℝ ↦ g y) :=
  h.comp_tendsto <| Continuous.tendsto continuous_ofReal x

-- [Mathlib.Analysis.Complex.RealDeriv]
lemma Complex.isBigO_comp_ofReal_nhds_ne {f g : ℂ → ℂ} {x : ℝ} (h : f =O[𝓝[≠] (x : ℂ)] g) :
    (fun y : ℝ ↦ f y) =O[𝓝[≠] x] (fun y : ℝ ↦ g y) :=
  h.comp_tendsto <| ((hasDerivAt_id (x : ℂ)).comp_ofReal).tendsto_punctured_nhds one_ne_zero

-- [Mathlib.Analysis.Asymptotics.Theta, Mathlib.Analysis.SpecificLimits.Normed,
--  Mathlib.Analysis.Asymptotics.SpecificAsymptotics,
--  Mathlib.Analysis.NormedSpace.OperatorNorm.Asymptotics]
lemma ContinuousAt.isBigO {𝕜 𝕜' : Type*} [NormedRing 𝕜] [NormedRing 𝕜'] [NormOneClass 𝕜']
    {f : 𝕜 → 𝕜'} {z : 𝕜} (hf : ContinuousAt f z) :
    (fun w ↦ f (w + z)) =O[𝓝 0] (fun _ ↦ (1 : 𝕜')) := by
  rw [isBigO_iff']
  replace hf : ContinuousAt (fun w ↦ f (w + z)) 0 := by
    convert (Homeomorph.comp_continuousAt_iff' (Homeomorph.addLeft (-z)) _ z).mp ?_
    · simp only [Homeomorph.coe_addLeft, neg_add_cancel]
    · simp only [Homeomorph.coe_addLeft, Function.comp_def, neg_add_cancel_comm, hf]
  simp_rw [Metric.continuousAt_iff', dist_eq_norm_sub, zero_add] at hf
  specialize hf 1 zero_lt_one
  refine ⟨‖f z‖ + 1, by positivity, ?_⟩
  refine Eventually.mp hf <| Eventually.of_forall fun w hw ↦ le_of_lt ?_
  calc ‖f (w + z)‖
    _ ≤ ‖f z‖ + ‖f (w + z) - f z‖ := norm_le_insert' ..
    _ < ‖f z‖ + 1 := add_lt_add_left hw _
    _ = _ := by simp only [norm_one, mul_one]

-- [Mathlib.Analysis.Calculus.Deriv.Shift]
lemma DifferentiableAt.isBigO_of_eq_zero {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup 𝕜'] [NormedSpace 𝕜 𝕜']
    {f : 𝕜 → 𝕜'} {z : 𝕜} (hf : DifferentiableAt 𝕜 f z) (hz : f z = 0) :
    (fun w ↦ f (w + z)) =O[𝓝 0] id := by
  rw [← zero_add z] at hf
  simpa only [zero_add, hz, sub_zero]
    using (hf.hasDerivAt.comp_add_const 0 z).differentiableAt.isBigO_sub

end BigO

section LSeries

-- This should go to `Mathlib.NumberTheory.LSeries.Linearity`

open LSeries

variable {ι : Type*} [DecidableEq ι] (f : ι → ℕ → ℂ) (S : Finset ι) (s : ℂ)

lemma LSeries.term_sum_apply (n : ℕ) :
    term (∑ i ∈ S, f i) s n  = ∑ i ∈ S, term (f i) s n := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, term, Pi.zero_apply, zero_div, ite_self]
  | insert hi IH  =>
    simp only [Finset.sum_insert hi, term_add_apply, IH]

lemma LSeries.term_sum : term (∑ i ∈ S, f i) s  = ∑ i ∈ S, term (f i) s :=
  funext fun _ ↦ by rw [Finset.sum_apply]; exact term_sum_apply f S s _

variable {f S s}

lemma LSeriesHasSum.sum {a : ι → ℂ} (hf : ∀ i ∈ S, LSeriesHasSum (f i) s (a i)) :
    LSeriesHasSum (∑ i ∈ S, f i) s (∑ i ∈ S, a i) := by
  simpa only [LSeriesHasSum, term_sum, Finset.sum_fn S fun i ↦ term (f i) s] using hasSum_sum hf

lemma LSeriesSummable.sum (hf : ∀ i ∈ S, LSeriesSummable (f i) s) :
    LSeriesSummable (∑ i ∈ S, f i) s := by
  simpa only [LSeriesSummable, ← term_sum_apply] using summable_sum hf

@[simp]
lemma LSeries_sum (hf : ∀ i ∈ S, LSeriesSummable (f i) s) :
    LSeries (∑ i ∈ S, f i) s = ∑ i ∈ S, LSeries (f i) s := by
  simpa only [LSeries, term_sum, Finset.sum_apply] using tsum_sum hf

variable [Fintype ι]

/-- The version of `LSeriesHasSum.sum` for `Fintype.sum`. -/
lemma LSeriesHasSum.sum' {a : ι → ℂ} (hf : ∀ i, LSeriesHasSum (f i) s (a i)) :
    LSeriesHasSum (∑ i : ι, f i) s (∑ i : ι, a i) :=
  sum fun i _ ↦ hf i

/-- The version of `LSeriesSummable.sum` for `Fintype.sum`. -/
lemma LSeriesSummable.sum' (hf : ∀ i, LSeriesSummable (f i) s) :
    LSeriesSummable (∑ i : ι, f i) s :=
  sum fun i _ ↦ hf i

/-- The version of `LSeries_sum` for `Fintype.sum`. -/
@[simp]
lemma LSeries_sum' (hf : ∀ i, LSeriesSummable (f i) s) :
    LSeries (∑ i : ι, f i) s = ∑ i : ι, LSeries (f i) s :=
  LSeries_sum fun i _ ↦ hf i

end LSeries

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
### The L-function of a Dirichlet character does not vanish on Re(s) = 1
-/

open Complex

section EulerProduct

-- This gets moved to `NumberTheory.LSeries.EulerProduct`

open LSeries Nat EulerProduct

/-- A variant of the Euler product for Dirichlet L-series. -/
theorem DirichletCharacter.LSeries_eulerProduct' {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -log (1 - χ p * p ^ (-s))) = L ↗χ s := by
  rw [LSeries]
  let f := dirichletSummandHom χ <| ne_zero_of_one_lt_re hs
  have h n : term ↗χ s n = f n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [term_zero, map_zero]
    · simp only [ne_eq, hn, not_false_eq_true, term_of_ne_zero, div_eq_mul_inv,
        dirichletSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, f]
  simpa only [h] using exp_tsum_primes_log_eq_tsum (f := f) <| summable_dirichletSummand χ hs

open DirichletCharacter

/-- A variant of the Euler product for the L-series of `ζ`. -/
theorem ArithmeticFunction.LSeries_zeta_eulerProduct' {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = L 1 s := by
  convert modOne_eq_one (R := ℂ) ▸ LSeries_eulerProduct' (1 : DirichletCharacter ℂ 1) hs using 7
  rw [MulChar.one_apply <| isUnit_of_subsingleton _, one_mul]

/-- A variant of the Euler product for the Riemann zeta function. -/
theorem riemannZeta_eulerProduct'  {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = riemannZeta s :=
  LSeries_one_eq_riemannZeta hs ▸ ArithmeticFunction.LSeries_zeta_eulerProduct' hs

end EulerProduct


lemma summable_neg_log_one_sub_character_mul_prime_cpow {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes ↦ -log (1 - χ p * (p : ℂ) ^ (-s)) := by
  have (p : Nat.Primes) : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-s).re := by
    rw [norm_mul, norm_natCast_cpow_of_re_ne_zero _ <| re_neg_ne_zero_of_one_lt_re hs]
    calc ‖χ p‖ * (p : ℝ) ^ (-s).re
      _ ≤ 1 * (p : ℝ) ^ (-s.re) := by gcongr; exact DirichletCharacter.norm_le_one χ _
      _ = _ := one_mul _
  refine (Nat.Primes.summable_rpow.mpr ?_).of_nonneg_of_le (fun _ ↦ norm_nonneg _) this
    |>.of_norm.neg_clog_one_sub
  simp only [neg_re, neg_lt_neg_iff, hs]

/-- A technical lemma showing that a certain linear combination of real parts of logarithms
is nonnegative. This is used to show non-vanishing of the Riemann zeta function and of
Dirichlet L-series on the line `re s = 1`. -/
lemma re_log_comb_nonneg {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ = 1) :
      0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re + (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [norm_eq_abs, abs_ofReal, _root_.abs_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  have H₀ := (hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3
  have H₁ := (hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4
  have H₂ := hasSum_re <| hasSum_taylorSeries_neg_log hac₂
  rw [← ((H₀.add H₁).add H₂).tsum_eq]; clear H₀ H₁ H₂
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [pow_zero, CharP.cast_eq_zero, div_zero, mul_zero, one_re, mul_one, add_zero,
     le_refl]
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_abs_sub_sq_re, ← norm_eq_abs, norm_pow, hz]
    calc
     0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 := by positivity
      _ = _  := by ring

namespace DirichletCharacter

lemma deriv_LFunction_eq_deriv_LSeries {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) {s : ℂ}
    (hs : 1 < s.re) :
    deriv (LFunction χ) s = deriv (LSeries ↗χ) s :=  by
  refine Filter.EventuallyEq.deriv_eq ?_
  have h : {z | 1 < z.re} ∈ nhds s :=
    (isOpen_lt continuous_const continuous_re).mem_nhds hs
  filter_upwards [h] with z hz
  exact LFunction_eq_LSeries χ hz

/-- The logarithm of an Euler factor of the product `L(χ^0, x)^3 * L(χ, x+I*y)^4 * L(χ^2, x+2*I*y)`
has nonnegative real part when `s = x + I*y` has real part `x > 1`. -/
lemma re_log_comb_nonneg {N : ℕ} (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : 2 ≤ n) {x y : ℝ}
    (hx : 1 < x) :
    0 ≤ 3 * (-log (1 - (1 : DirichletCharacter ℂ N) n * n ^ (-x : ℂ))).re +
          4 * (-log (1 - χ n * n ^ (-(x + I * y)))).re +
          (-log (1 - (χ n ^ 2) * n ^ (-(x + 2 * I * y)))).re := by
  by_cases hn' : IsUnit (n : ZMod N)
  · have ha₀ : 0 ≤ (n : ℝ) ^ (-x) := Real.rpow_nonneg n.cast_nonneg _
    have ha₁ : (n : ℝ) ^ (-x) < 1 := by
      simpa only [Real.rpow_lt_one_iff n.cast_nonneg, Nat.cast_eq_zero, Nat.one_lt_cast,
        Left.neg_neg_iff, Nat.cast_lt_one, Left.neg_pos_iff]
        using .inr <| .inl ⟨hn, zero_lt_one.trans hx⟩
    have hz : ‖χ n * (n : ℂ) ^ (-(I * y))‖ = 1 := by
      rw [norm_mul, ← hn'.unit_spec, DirichletCharacter.unit_norm_eq_one χ hn'.unit, one_mul,
        norm_eq_abs, abs_cpow_of_imp fun h ↦ False.elim <| by linarith [Nat.cast_eq_zero.mp h, hn]]
      simp only [abs_natCast, neg_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, neg_zero, Real.rpow_zero, natCast_arg, neg_im, mul_im, one_mul, zero_add, mul_neg,
        Real.exp_zero, ne_eq, one_ne_zero, not_false_eq_true, div_self]
    rw [MulChar.one_apply hn', one_mul]
    convert _root_.re_log_comb_nonneg ha₀ ha₁ hz using 6
    · congr 2
      exact_mod_cast (ofReal_cpow n.cast_nonneg (-x)).symm
    · congr 2
      rw [neg_add, cpow_add _ _ <| by norm_cast; linarith, ← ofReal_neg,
        ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, mul_left_comm]
    · rw [neg_add, cpow_add _ _ <| by norm_cast; linarith, ← ofReal_neg,
        ofReal_cpow n.cast_nonneg (-x), ofReal_natCast,
        show -(2 * I * y) = (2 : ℕ) * -(I * y) by ring, cpow_nat_mul, mul_pow, mul_left_comm]
  · simp only [MulChar.map_nonunit _ hn', zero_mul, sub_zero, log_one, neg_zero, zero_re, mul_zero,
      neg_add_rev, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, le_refl]

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

open Complex BigOperators Filter Topology Homeomorph Asymptotics

private lemma one_lt_re_one_add {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 < (1 + x : ℂ).re ∧ 1 < (1 + x + I * y).re ∧ 1 < (1 + x + 2 * I * y).re := by
  simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right, hx, mul_re, I_re, zero_mul, I_im,
    ofReal_im, mul_zero, sub_self, add_zero, re_ofNat, im_ofNat, mul_one, mul_im, and_self]

open scoped LSeries.notation

open Nat ArithmeticFunction

/-- For positive `x` and nonzero `y` we have that
$|L(\chi^0, x)^3 \cdot L(\chi, x+iy)^4 \cdot L(\chi^2, x+2iy)| \ge 1$. -/
lemma norm_LSeries_product_ge_one {N : ℕ} (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 0 < x)
    (y : ℝ) :
    ‖L ↗(1 : DirichletCharacter ℂ N) (1 + x) ^ 3 * L ↗χ (1 + x + I * y) ^ 4 *
      L ↗(χ ^ 2 :) (1 + x + 2 * I * y)‖ ≥ 1 := by
  let χ₀ := (1 : DirichletCharacter ℂ N)
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_one_add hx y
  have hx₁ : 1 + (x : ℂ) = (1 + x : ℂ).re := by -- kills three goals of the `convert` below
    simp only [add_re, one_re, ofReal_re, ofReal_add, ofReal_one]
  have hsum₀ :=
    (hasSum_re (summable_neg_log_one_sub_character_mul_prime_cpow χ₀ h₀).hasSum).summable
    |>.mul_left 3
  have hsum₁ :=
    (hasSum_re (summable_neg_log_one_sub_character_mul_prime_cpow χ h₁).hasSum).summable.mul_left 4
  have hsum₂ :=
    (hasSum_re (summable_neg_log_one_sub_character_mul_prime_cpow (χ ^ 2) h₂).hasSum).summable
  rw [← LSeries_eulerProduct' _ h₀, ← LSeries_eulerProduct' χ h₁,
    ← LSeries_eulerProduct' (χ ^ 2) h₂, ← exp_nat_mul, ← exp_nat_mul, ← exp_add, ← exp_add,
    norm_eq_abs, abs_exp]
  simp only [cast_ofNat, add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero,
    Real.one_le_exp_iff]
  rw [re_tsum <| summable_neg_log_one_sub_character_mul_prime_cpow _ h₀,
    re_tsum <| summable_neg_log_one_sub_character_mul_prime_cpow _ h₁,
    re_tsum <| summable_neg_log_one_sub_character_mul_prime_cpow _ h₂, ← tsum_mul_left,
    ← tsum_mul_left, ← tsum_add hsum₀ hsum₁, ← tsum_add (hsum₀.add hsum₁) hsum₂]
  simp only [χ.pow_apply' two_ne_zero]
  -- `exact` times out here
  convert tsum_nonneg fun p : Nat.Primes ↦ χ.re_log_comb_nonneg p.prop.two_le h₀

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- A variant of `DirichletCharacter.norm_LSeries_product_ge_one` in terms of the L-functions. -/
lemma norm_LFunction_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖LFunctionTrivChar N (1 + x) ^ 3 * LFunction χ (1 + x + I * y) ^ 4 *
      LFunction (χ ^ 2) (1 + x + 2 * I * y)‖ ≥ 1 := by
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_one_add hx y
  rw [LFunctionTrivChar, DirichletCharacter.LFunction_eq_LSeries 1 h₀,
    χ.LFunction_eq_LSeries h₁, (χ ^ 2).LFunction_eq_LSeries h₂]
  exact norm_LSeries_product_ge_one χ hx y

lemma LFunctionTrivChar_isBigO_near_one_horizontal :
    (fun x : ℝ ↦ LFunctionTrivChar N (1 + x)) =O[𝓝[>] 0] (fun x ↦ (1 : ℂ) / x) := by
  have : (fun w : ℂ ↦ LFunctionTrivChar N (1 + w)) =O[𝓝[≠] 0] (1 / ·) := by
    have H : Tendsto (fun w ↦ w * LFunctionTrivChar N (1 + w)) (𝓝[≠] 0)
               (𝓝 <| ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)) := by
      convert (LFunctionTrivChar_residue_one (N := N)).comp (f := fun w ↦ 1 + w) ?_ using 1
      · ext1 w
        simp only [Function.comp_apply, add_sub_cancel_left]
      · refine tendsto_iff_comap.mpr <| map_le_iff_le_comap.mp <| Eq.le ?_
        convert map_punctured_nhds_eq (Homeomorph.addLeft (1 : ℂ)) 0 using 2 <;>
          simp only [coe_addLeft, add_zero]
    exact ((isBigO_mul_iff_isBigO_div eventually_mem_nhdsWithin).mp <|
      Tendsto.isBigO_one ℂ H).trans <| isBigO_refl ..
  exact (isBigO_comp_ofReal_nhds_ne this).mono <| nhds_right'_le_nhds_ne 0

omit [NeZero N] in
private lemma one_add_I_mul_ne_one_or {y : ℝ} (hy : y ≠ 0 ∨ χ ≠ 1) :
    1 + I * y ≠ 1 ∨ χ ≠ 1:= by
  simpa only [ne_eq, add_right_eq_self, _root_.mul_eq_zero, I_ne_zero, ofReal_eq_zero, false_or]
    using hy

lemma LFunction_isBigO_horizontal {y : ℝ} (hy : y ≠ 0 ∨ χ ≠ 1) :
    (fun x : ℝ ↦ χ.LFunction (1 + x + I * y)) =O[𝓝[>] 0] (fun _ ↦ (1 : ℂ)) := by
  refine IsBigO.mono ?_ nhdsWithin_le_nhds
  convert isBigO_comp_ofReal
    (χ.differentiableAt_LFunction _ <| one_add_I_mul_ne_one_or hy).continuousAt.isBigO using 3
  abel

lemma LFunction_isBigO_horizontal_of_eq_zero {y : ℝ} (hy : y ≠ 0 ∨ χ ≠ 1)
    (h : LFunction χ (1 + I * y) = 0) :
    (fun x : ℝ ↦ LFunction χ (1 + x + I * y)) =O[𝓝[>] 0] fun x : ℝ ↦ (x : ℂ) := by
  conv => enter [2, x]; rw [add_comm 1, add_assoc]
  refine (isBigO_comp_ofReal <| DifferentiableAt.isBigO_of_eq_zero ?_ h).mono nhdsWithin_le_nhds
  exact χ.differentiableAt_LFunction (1 + I * ↑y) <| one_add_I_mul_ne_one_or hy

/-- The L-function of a Dirichlet character `χ` does not vanish at `1 + I*t` if `t ≠ 0`
or `χ^2 ≠ 1`. -/
lemma LFunction_ne_zero_of_ne_one_or_not_quadratic {t : ℝ} (h : χ ^ 2 ≠ 1 ∨ t ≠ 0) :
    LFunction χ (1 + I * t) ≠ 0 := by
  intro Hz
  have H₀ : (fun _ : ℝ ↦ (1 : ℝ)) =O[𝓝[>] 0]
      (fun x ↦ LFunctionTrivChar N (1 + x) ^ 3 * LFunction χ (1 + x + I * t) ^ 4 *
                   LFunction (χ ^ 2) (1 + x + 2 * I * t)) :=
    IsBigO.of_bound' <| eventually_nhdsWithin_of_forall
      fun _ hx ↦ (norm_one (α := ℝ)).symm ▸ (norm_LFunction_product_ge_one hx t).le
  have hz₁ : t ≠ 0 ∨ χ ≠ 1 := by
    rcases h with h | h
    · exact .inr <| by rintro rfl; simp only [one_pow, ne_eq, not_true_eq_false] at h
    · exact .inl h
  have hz₂ : 2 * t ≠ 0 ∨ χ ^ 2 ≠ 1 := by
    rcases h with h | h
    · exact .inr h
    · exact .inl <| mul_ne_zero two_ne_zero h
  have H := ((LFunctionTrivChar_isBigO_near_one_horizontal (N := N)).pow 3).mul
    ((LFunction_isBigO_horizontal_of_eq_zero hz₁ Hz).pow 4) |>.mul <|
    LFunction_isBigO_horizontal hz₂
  have help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | h
    · rw [ofReal_zero, zero_pow (by norm_num), mul_zero, mul_one]
    · field_simp [h]
      exact _root_.pow_succ' ..
  simp only [ofReal_mul, ofReal_ofNat, mul_left_comm I, ← mul_assoc, help] at H
  replace H := (H₀.trans H).norm_right
  simp only [norm_eq_abs, abs_ofReal] at H
  refine isLittleO_irrefl ?_ <| H.of_abs_right.trans_isLittleO <|
    isLittleO_id_one.mono nhdsWithin_le_nhds
  simp only [ne_eq, one_ne_zero, not_false_eq_true, frequently_true_iff_neBot]
  exact mem_closure_iff_nhdsWithin_neBot.mp <| closure_Ioi (0 : ℝ) ▸ Set.left_mem_Ici

/-- If `χ` is a Dirichlet character, then `L(χ, 1 + I*t)` does not vanish for `t ∈ ℝ`
except when `χ` is trivial and `t = 0` (then `L(χ, s)` has a simple pole at `s = 1`). -/
theorem Lfunction_ne_zero_of_re_eq_one (χ : DirichletCharacter ℂ N) (t : ℝ) (hχt : χ ≠ 1 ∨ t ≠ 0) :
    LFunction χ (1 + I * t) ≠ 0 := by
  by_cases h : χ ^ 2 = 1 ∧ t = 0
  · simp only [ne_eq, h.2, not_true_eq_false, or_false] at hχt
    simpa only [h.2, ofReal_zero, mul_zero, add_zero]
      using LFunction_at_one_ne_zero_of_quadratic h.1 hχt
  · exact LFunction_ne_zero_of_ne_one_or_not_quadratic <| not_and_or.mp h

/-- If `χ` is a Dirichlet character, then `L(χ, s)` does not vanish for `s.re ≥ 1`
except when `χ` is trivial and `s = 1` (then `L(χ, s)` has a simple pole at `s = 1`). -/
theorem Lfunction_ne_zero_of_one_le_re (χ : DirichletCharacter ℂ N) ⦃s : ℂ⦄ (hχs : χ ≠ 1 ∨ s ≠ 1)
    (hs : 1 ≤ s.re) :
    LFunction χ s ≠ 0 := by
  rcases hs.eq_or_lt with hs | hs
  · have hseq : s = 1 + I * s.im := by
      rw [mul_comm I, ← re_add_im s, ← hs]
      push_cast
      simp only [add_im, one_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
        add_zero, zero_add]
    rw [hseq]
    apply Lfunction_ne_zero_of_re_eq_one
    rcases hχs with h | h
    · exact .inl h
    · refine .inr ?_
      rw [← re_add_im s, ← hs, ofReal_one] at h
      simpa only [ne_eq, add_right_eq_self, _root_.mul_eq_zero, ofReal_eq_zero, I_ne_zero,
        or_false] using h
  · exact LFunction_eq_LSeries χ hs ▸ LSeries_ne_zero_of_one_lt_re χ hs

end DirichletCharacter

open DirichletCharacter in
/-- The Riemann Zeta Function does not vanish on the closed half-plane `re z ≥ 1`. -/
lemma riemannZeta_ne_zero_of_one_le_re ⦃z : ℂ⦄ (hz : z ≠ 1) (hz' : 1 ≤ z.re) :
    riemannZeta z ≠ 0 := by
  rw [← LFunction_modOne_eq (χ := 1)]
  exact Lfunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ 1) (.inr hz) hz'

/-!
### The logarithmic derivative of the L-function of a trivial character has a simple pole at s = 1 with residue -1

We show that `s ↦ L'(χ) s / L(χ) s + 1 / (s - 1)` (or rather, its negative, which is the function
we need for the Wiener-Ikehara Theorem) is continuous outside the zeros of `L(χ)` when `χ`
is a trivial Dirichlet character.
-/

namespace DirichletCharacter

section trivial

variable (n : ℕ) [NeZero n]

/-- The function obtained by "multiplying away" the pole of `L(χ)` for a trivial Dirichlet
character `χ`. Its (negative) logarithmic derivative is used in the Wiener-Ikehara Theorem
to prove the Prime Number Theorem version of Dirichlet's Theorem on primes in arithmetic
progressions. -/
noncomputable def LFunctionTrivChar₁ : ℂ → ℂ :=
  Function.update (fun z ↦ LFunctionTrivChar n z * (z - 1)) 1
    (∏ p ∈ n.primeFactors, (1 - (p : ℂ)⁻¹))

lemma LFunctionTrivChar₁_apply_of_ne_one {z : ℂ} (hz : z ≠ 1) :
    LFunctionTrivChar₁ n z = LFunctionTrivChar n z * (z - 1) := by
  simp [LFunctionTrivChar₁, hz]

lemma LFunction_triv_char₁_differentiable : Differentiable ℂ (LFunctionTrivChar₁ n) := by
  rw [← differentiableOn_univ,
    ← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem,
    LFunctionTrivChar₁]
  refine ⟨DifferentiableOn.congr (f := fun z ↦ LFunctionTrivChar n z * (z - 1))
    (fun z hz ↦ DifferentiableAt.differentiableWithinAt ?_) fun _ hz ↦ ?_,
    continuousWithinAt_compl_self.mp ?_⟩
  · simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and] at hz
    exact (differentiableAt_LFunction _ z (.inl hz)).mul <| (differentiableAt_id').sub <|
      differentiableAt_const _
  · simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and] at hz
    simp only [ne_eq, hz, not_false_eq_true, Function.update_noteq]
  · conv in (_ * _) => rw [mul_comm]
    simp only [continuousWithinAt_compl_self, continuousAt_update_same]
    exact LFunctionTrivChar_residue_one

lemma deriv_LFunctionTrivChar₁_apply_of_ne_one  {z : ℂ} (hz : z ≠ 1) :
    deriv (LFunctionTrivChar₁ n) z =
      deriv (LFunctionTrivChar n) z * (z - 1) + LFunctionTrivChar n z := by
  have H : deriv (LFunctionTrivChar₁ n) z =
      deriv (fun w ↦ LFunctionTrivChar n w * (w - 1)) z := by
    refine Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨{w | w ≠ 1}, IsOpen.mem_nhds isOpen_ne hz, fun w hw ↦ ?_⟩
    simp only [LFunctionTrivChar₁, ne_eq, Set.mem_setOf.mp hw, not_false_eq_true,
      Function.update_noteq]
  rw [H, deriv_mul (differentiableAt_LFunction _ z (.inl hz)) <| differentiableAt_id'.sub <|
    differentiableAt_const 1, deriv_sub_const, deriv_id'', mul_one]

lemma neg_logDeriv_LFunctionTrivChar₁_eq {z : ℂ} (hz₁ : z ≠ 1)
    (hz₂ : LFunctionTrivChar n z ≠ 0) :
    -deriv (LFunctionTrivChar₁ n) z / LFunctionTrivChar₁ n z =
      -deriv (LFunctionTrivChar n) z / LFunctionTrivChar n z - 1 / (z - 1) := by
  rw [deriv_LFunctionTrivChar₁_apply_of_ne_one n hz₁, LFunctionTrivChar₁_apply_of_ne_one n hz₁]
  field_simp [sub_ne_zero.mpr hz₁]
  ring

lemma continuousOn_neg_logDeriv_LFunctionTrivChar₁ :
    ContinuousOn (fun z ↦ -deriv (LFunctionTrivChar₁ n) z / LFunctionTrivChar₁ n z)
      {z | z = 1 ∨ LFunctionTrivChar n z ≠ 0} := by
  simp_rw [neg_div]
  refine (((LFunction_triv_char₁_differentiable n).contDiff.continuous_deriv le_rfl).continuousOn.div
    (LFunction_triv_char₁_differentiable n).continuous.continuousOn fun w hw ↦ ?_).neg
  rcases eq_or_ne w 1 with rfl | hw'
  · simp only [LFunctionTrivChar₁, Function.update_same]
    refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_
    rw [sub_ne_zero, ne_eq, one_eq_inv]
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_one
  · simp only [ne_eq, Set.mem_setOf_eq, hw', false_or] at hw
    simp only [LFunctionTrivChar₁, ne_eq, hw', not_false_eq_true, Function.update_noteq, _root_.mul_eq_zero, hw,
      false_or]
    exact sub_ne_zero.mpr hw'

lemma eq_one_or_LFunctionTrivChar_ne_zero_of_one_le_re :
    {s : ℂ | 1 ≤ s.re} ⊆ {s | s = 1 ∨ LFunction (1 : DirichletCharacter ℂ n) s ≠ 0} := by
  intro s hs
  simp only [Set.mem_setOf_eq, ne_eq] at hs ⊢
  have := Lfunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ n) (s := s)
  tauto

end trivial

section nontrivial

variable {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n}

/-- The negative logarithmic derivative of a Dirichlet L-function is continuous away from
the zeros of the L-function. -/
lemma continuousOn_neg_logDeriv_LFunction_nontriv_char (hχ : χ ≠ 1) :
    ContinuousOn (fun z ↦ -deriv (LFunction χ) z / LFunction χ z)
      {z | LFunction χ z ≠ 0} := by
  simp_rw [neg_div]
  have h₁ := differentiable_LFunction hχ
  exact ((h₁.contDiff.continuous_deriv le_rfl).continuousOn.div
    h₁.continuous.continuousOn fun w hw ↦ hw).neg

lemma LFunction_nontriv_char_ne_zero_of_one_le_re (hχ : χ ≠ 1) :
    {s : ℂ | 1 ≤ s.re} ⊆ {s | LFunction χ s ≠ 0} := by
  intro s hs
  simp only [Set.mem_setOf_eq, ne_eq] at hs ⊢
  have := Lfunction_ne_zero_of_one_le_re χ (s := s)
  tauto

end nontrivial

end DirichletCharacter

section zeta

/-!
### The logarithmic derivative of ζ has a simple pole at s = 1 with residue -1

We show that `s ↦ ζ' s / ζ s + 1 / (s - 1)` (or rather, its negative, which is the function
we need for the Wiener-Ikehara Theorem) is continuous outside the zeros of `ζ`.
-/

/-- We use `ζ` to denote the Riemann zeta function. -/
local notation (name := rzeta) "ζ" => riemannZeta

/-- The function obtained by "multiplying away" the pole of `ζ`. Its (negative) logarithmic
derivative is the function used in the Wiener-Ikehara Theorem to prove the Prime Number
Theorem. -/
noncomputable def ζ₁ : ℂ → ℂ := Function.update (fun z ↦ ζ z * (z - 1)) 1 1

open DirichletCharacter

lemma riemannZeta_eq_LFunctionTrivChar_one : ζ = LFunctionTrivChar 1 :=
  LFunction_modOne_eq.symm

lemma ζ₁_eq_LFunctionTrivChar₁_one : ζ₁ = LFunctionTrivChar₁ 1 := by
  ext1
  simp only [ζ₁, LFunctionTrivChar₁, LFunction_modOne_eq, Nat.primeFactors_one,
    Finset.prod_empty]

lemma neg_logDeriv_ζ₁_eq {z : ℂ} (hz₁ : z ≠ 1) (hz₂ : ζ z ≠ 0) :
    -deriv ζ₁ z / ζ₁ z = -deriv ζ z / ζ z - 1 / (z - 1) := by
  simp only [ζ₁_eq_LFunctionTrivChar₁_one, riemannZeta_eq_LFunctionTrivChar_one] at hz₂ ⊢
  exact neg_logDeriv_LFunctionTrivChar₁_eq 1 hz₁ hz₂

lemma continuousOn_neg_logDeriv_ζ₁ :
    ContinuousOn (fun z ↦ -deriv ζ₁ z / ζ₁ z) {z | z = 1 ∨ ζ z ≠ 0} := by
  simp only [ζ₁_eq_LFunctionTrivChar₁_one, riemannZeta_eq_LFunctionTrivChar_one]
  exact continuousOn_neg_logDeriv_LFunctionTrivChar₁ 1

end zeta

/-!
### Proof of Lemma 9

We prove Lemma 9 of
[Section 2 in the PNT+ Project](https://alexkontorovich.github.io/PrimeNumberTheoremAnd/web/sect0002.html).
-/

section arith_prog

open scoped ArithmeticFunction.vonMangoldt
open DirichletCharacter

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- Lemma 9 of Section 2 of PNT+: The L-series of the von Mangoldt function restricted to the
prime residue class `a` mod `q` as a linear combination of logarithmic derivatives of
L functions of the Dirichlet characters mod `q`. -/
lemma WeakPNT_character (ha : IsUnit a) {s : ℂ} (hs : 1 < s.re) :
     LSeries ({n : ℕ | (n : ZMod q) = a}.indicator ↗Λ) s =
      -(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ *
        (deriv (LFunction χ) s / LFunction χ s) := by
  simp only [deriv_LFunction_eq_deriv_LSeries _ hs, LFunction_eq_LSeries _ hs, neg_mul, ← mul_neg,
    ← Finset.sum_neg_distrib, ← neg_div, ← LSeries_twist_vonMangoldt_eq _ hs]
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp only [← LSeries_smul]
  classical
  rw [← LSeries_sum' <| fun χ ↦ (LSeriesSummable_twist_vonMangoldt χ hs).smul _]
  refine LSeries_congr s fun {n} _ ↦ ?_
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.mul_apply, Set.indicator_apply]
  conv_lhs => rw [← one_mul (Λ n : ℂ), ← zero_mul (Λ n : ℂ), ← ite_mul]
  simp only [← mul_assoc, ← Finset.sum_mul, mul_ite, mul_one, mul_zero, Set.mem_setOf_eq]
  congrm (?_ * (Λ n : ℂ))
  simpa only [Nat.cast_ite, Nat.cast_zero, eq_comm (a := a)]
    using (sum_char_inv_mul_char_eq ℂ ha n).symm

variable (q a) in
open Classical in
/-- The function `F` used in the Wiener-Ikehara Theorem to prove Dirichlet's Theorem. -/
noncomputable
def weakDirichlet_auxFun (s : ℂ) : ℂ :=
  (q.totient : ℂ)⁻¹ * (-deriv (LFunctionTrivChar₁ q) s / LFunctionTrivChar₁ q s -
    ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)), χ a⁻¹ * deriv (LFunction χ) s / LFunction χ s)

lemma weakDirichlet_auxFun_prop (ha : IsUnit a) :
    Set.EqOn (weakDirichlet_auxFun q a)
      (fun s ↦ LSeries ({n : ℕ | (n : ZMod q) = a}.indicator ↗Λ) s - (q.totient : ℂ)⁻¹ / (s - 1))
      {s | 1 < s.re} := by
  classical
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  simp only [WeakPNT_character ha hs]
  rw [weakDirichlet_auxFun, neg_div, ← neg_add', mul_neg, ← neg_mul,
    div_eq_mul_one_div (q.totient : ℂ)⁻¹, sub_eq_add_neg, ← neg_mul, ← mul_add]
  congrm (_ * ?_)
  -- this should be easier, but `IsUnit.inv ha` does not work here
  have ha' : IsUnit a⁻¹ := isUnit_of_dvd_one ⟨a, (ZMod.inv_mul_of_unit a ha).symm⟩
  rw [Fintype.sum_eq_add_sum_compl 1, MulChar.one_apply ha', one_mul, add_right_comm]
  simp only [mul_div_assoc]
  congrm (?_ + _)
  have hs₁ : s ≠ 1 := by
    rintro rfl
    simp only [one_re, lt_self_iff_false] at hs
  rw [deriv_LFunctionTrivChar₁_apply_of_ne_one _ hs₁, LFunctionTrivChar₁_apply_of_ne_one _ hs₁]
  simp only [LFunctionTrivChar]
  rw [add_div, mul_div_mul_right _ _ (sub_ne_zero_of_ne hs₁)]
  conv_lhs => enter [2, 1]; rw [← mul_one (LFunction ..)]
  rw [mul_div_mul_left _ _ <| Lfunction_ne_zero_of_one_le_re 1 (.inr hs₁) hs.le]

/-- (A version of) Proposition 2 of Section 2 of PNT+: the L-series of the von Mangoldt function
restricted to the prime residue class `a` mod `q` is continuous on `s.re ≥ 1` except
for a single pole at `s = 1` with residue `(q.totient)⁻¹`.-/
lemma continuousOn_weakDirichlet_auxFun :
    ContinuousOn (weakDirichlet_auxFun q a) {s | 1 ≤ s.re} := by
  rw [show weakDirichlet_auxFun q a = fun s ↦ _ from rfl]
  simp only [weakDirichlet_auxFun, sub_eq_add_neg]
  refine continuousOn_const.mul <| ContinuousOn.add ?_ ?_
  · exact ContinuousOn.mono (continuousOn_neg_logDeriv_LFunctionTrivChar₁ q)
      (eq_one_or_LFunctionTrivChar_ne_zero_of_one_le_re q)
  · simp only [← Finset.sum_neg_distrib, mul_div_assoc, ← mul_neg, ← neg_div]
    refine continuousOn_finset_sum _ fun χ hχ ↦ continuousOn_const.mul ?_
    replace hχ : χ ≠ 1 := by simpa only [ne_eq, Finset.mem_compl, Finset.mem_singleton] using hχ
    exact ContinuousOn.mono (continuousOn_neg_logDeriv_LFunction_nontriv_char hχ)
      (LFunction_nontriv_char_ne_zero_of_one_le_re hχ)

end arith_prog

/-!
### Derivation of the Prime Number Theorem and Dirichlet's Theorem from the Wiener-Ikehara Theorem
-/

open Filter ArithmeticFunction Topology

/- /-- The *Wiener-Ikehara Theorem* implies the *Prime Number Theorem* in the form that
`ψ x ∼ x`, where `ψ x = ∑ n < x, Λ n` and `Λ` is the von Mangoldt function. -/
theorem PNT_vonMangoldt' (WIT : WienerIkeharaTheorem) :
    Tendsto (fun N : ℕ ↦ ((Finset.range N).sum Λ) / N) atTop (𝓝 1) := by
  have hnv := riemannZeta_ne_zero_of_one_le_re
  refine WIT (F := fun z ↦ -deriv ζ₁ z / ζ₁ z) (fun _ ↦ vonMangoldt_nonneg) (fun s hs ↦ ?_) ?_
  · have hs₁ : s ≠ 1 := by
      rintro rfl
      simp at hs
    simp only [ne_eq, hs₁, not_false_eq_true, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
      ofReal_one]
    exact neg_logDeriv_ζ₁_eq hs₁ <| hnv hs₁ (Set.mem_setOf.mp hs).le
  · refine continuousOn_neg_logDeriv_ζ₁.mono fun s _ ↦ ?_
    specialize @hnv s
    simp at *
    tauto -/

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
  refine WIT (F := weakDirichlet_auxFun q a) (fun n ↦ ?_) ?_ ?_
  · exact Set.indicator_apply_nonneg fun _ ↦ vonMangoldt_nonneg
  · convert weakDirichlet_auxFun_prop ha with s n
    · by_cases hn : n = a
      · simp only [Set.mem_setOf_eq, hn, Set.indicator_of_mem]
      · simp only [Set.mem_setOf_eq, hn, not_false_eq_true, Set.indicator_of_not_mem, ofReal_zero]
    · rw [ofReal_inv, ofReal_natCast]
  · exact continuousOn_weakDirichlet_auxFun

/-- The *Wiener-Ikehara Theorem* implies the *Prime Number Theorem* in the form that
`ψ x ∼ x`, where `ψ x = ∑ n < x, Λ n` and `Λ` is the von Mangoldt function. -/
theorem PNT_vonMangoldt (WIT : WienerIkeharaTheorem) :
    Tendsto (fun N : ℕ ↦ ((Finset.range N).sum Λ) / N) atTop (𝓝 1) := by
  convert Dirichlet_vonMangoldt WIT (q := 1) (a := 1) isUnit_one with n
  · exact (Finset.filter_true_of_mem fun _ _ ↦ Subsingleton.eq_one _).symm
  · simp only [Nat.totient_one, Nat.cast_one, inv_one]
