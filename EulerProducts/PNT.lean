import EulerProducts.Auxiliary
import EulerProducts.Logarithm
import EulerProducts.NonvanishingQuadratic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
-- import Mathlib.Tactic.RewriteSearch

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

/-- We use `ζ` to denote the Riemann zeta function. -/
local notation (name := rzeta) "ζ" => riemannZeta

/-- We use `χ₁` to denote the (trivial) Dirichlet character modulo `1`. -/
local notation (name := Dchar_one') "χ₁" => (1 : DirichletCharacter ℂ 1)

section EulerProduct

-- This gets moved to `NumberTheory.LSeries.EulerProduct`

open LSeries Nat EulerProduct

/-- A variant of the Euler product for Dirichlet L-series. -/
theorem DirichletCharacter.LSeries_eulerProduct' {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -log (1 - χ p * p ^ (-s))) = L ↗χ s := by
  rw [LSeries]
  convert exp_sum_primes_log_eq_tsum (f := dirichletSummandHom χ <| ne_zero_of_one_lt_re hs) <|
    summable_dirichletSummand χ hs -- where does the `x✝: ℕ` come from??
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [term_zero, map_zero]
  · simp [hn, dirichletSummandHom, div_eq_mul_inv, cpow_neg]

open DirichletCharacter

/-- A variant of the Euler product for the L-series of `ζ`. -/
theorem ArithmeticFunction.LSeries_zeta_eulerProduct' {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = L 1 s := by
  convert modOne_eq_one (R := ℂ) ▸ LSeries_eulerProduct' χ₁ hs using 7
  rw [MulChar.one_apply <| isUnit_of_subsingleton _, one_mul]

/-- A variant of the Euler product for the Riemann zeta function. -/
theorem riemannZeta_eulerProduct'  {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = riemannZeta s :=
  LSeries_one_eq_riemannZeta hs ▸ ArithmeticFunction.LSeries_zeta_eulerProduct' hs

end EulerProduct


lemma summable_neg_log_one_sub_char_mul_prime_cpow {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
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
  simp only [mul_pow, ← ofReal_pow, div_natCast_re, ofReal_re, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  field_simp
  refine div_nonneg ?_ n.cast_nonneg
  rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_abs_sub_sq_re, ← norm_eq_abs, norm_pow, hz]
  calc
    0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 := by positivity
    _ = _  := by ring

/-- The logarithm of an Euler factor of the product `L(χ^0, x)^3 * L(χ, x+I*y)^4 * L(χ^2, x+2*I*y)`
has nonnegative real part when `s = x + I*y` has real part `x > 1`. -/
lemma re_log_comb_nonneg_dirichlet {N : ℕ} (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : 2 ≤ n)
    {x y : ℝ} (hx : 1 < x) :
    0 ≤ 3 * (-log (1 - (1 : DirichletCharacter ℂ N) n * n ^ (-x : ℂ))).re +
          4 * (-log (1 - χ n * n ^ (-(x + I * y)))).re +
          (-log (1 - (χ n ^ 2) * n ^ (-(x + 2 * I * y)))).re := by
  by_cases hn' : IsUnit (n : ZMod N)
  · have ha₀ : 0 ≤ (n : ℝ) ^ (-x) := Real.rpow_nonneg n.cast_nonneg _
    have ha₁ : (n : ℝ) ^ (-x) < 1 := by
      simpa only [Real.rpow_lt_one_iff n.cast_nonneg, Nat.cast_eq_zero, Nat.one_lt_cast,
        Left.neg_neg_iff, Nat.cast_lt_one, Left.neg_pos_iff]
        using Or.inr <| Or.inl ⟨hn, zero_lt_one.trans hx⟩
    have hz : ‖χ n * (n : ℂ) ^ (-(I * y))‖ = 1 := by
      rw [norm_mul, ← hn'.unit_spec, DirichletCharacter.unit_norm_eq_one χ hn'.unit, one_mul,
        norm_eq_abs, abs_cpow_of_imp fun h ↦ False.elim <| by linarith [Nat.cast_eq_zero.mp h, hn]]
      simp
    rw [MulChar.one_apply hn', one_mul]
    convert re_log_comb_nonneg ha₀ ha₁ hz using 6
    · congr 2
      exact_mod_cast (ofReal_cpow n.cast_nonneg (-x)).symm
    · congr 2
      rw [neg_add, cpow_add _ _ <| by norm_cast; linarith, ← ofReal_neg,
        ofReal_cpow n.cast_nonneg (-x), ofReal_natCast]
      ring
    · rw [neg_add, cpow_add _ _ <| by norm_cast; linarith, ← ofReal_neg,
        ofReal_cpow n.cast_nonneg (-x), ofReal_natCast,
        show -(2 * I * y) = (2 : ℕ) * (-I * y) by ring, cpow_nat_mul]
      ring_nf
  · simp [MulChar.map_nonunit _ hn']

-- A helper lemma used in the two proofs below
lemma one_lt_re_of_pos {x : ℝ} (y : ℝ) (hx : 0 < x) :
    1 < (1 + x : ℂ).re ∧ 1 < (1 + x + I * y).re ∧ 1 < (1 + x + 2 * I * y).re := by
  simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right, hx, mul_re, I_re, zero_mul, I_im,
    ofReal_im, mul_zero, sub_self, add_zero, re_ofNat, im_ofNat, mul_one, mul_im, and_self]

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

open Complex BigOperators Filter Topology Homeomorph Asymptotics

open scoped LSeries.notation

noncomputable
abbrev LFunction_one (N : ℕ) [NeZero N] := (1 : DirichletCharacter ℂ N).LFunction

/-- If `χ` is a Dirichlet character and its level `M` divides `N`, then we obtain the L-series
of `χ` considered as a Dirichlet character of level `N` from the L-series of `χ` by multiplying
with `∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))`. -/
lemma LSeries_changeLevel {M N : ℕ} [NeZero N] (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries ↗(changeLevel hMN χ) s =
      LSeries ↗χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  rw [prod_eq_tprod_mulIndicator, ← dirichletLSeries_eulerProduct_tprod _ hs,
    ← dirichletLSeries_eulerProduct_tprod _ hs]
  -- not sure why the `show` is needed here, `tprod_subtype` doesn't bite otherwise
  show ∏' p : ↑{p : ℕ | p.Prime}, _ = (∏' p : ↑{p : ℕ | p.Prime}, _) * _
  rw [tprod_subtype ↑{p : ℕ | p.Prime} fun p ↦ (1 - (changeLevel hMN χ) p * p ^ (-s))⁻¹,
    tprod_subtype ↑{p : ℕ | p.Prime} fun p ↦ (1 - χ p * p ^ (-s))⁻¹, ← tprod_mul]
  rotate_left -- deal with convergence goals first
  · rw [← multipliable_subtype_iff_mulIndicator]
    exact (dirichletLSeries_eulerProduct_hasProd χ hs).multipliable
  · rw [← multipliable_subtype_iff_mulIndicator]
    exact Multipliable.of_finite
  · congr 1 with p
    simp only [Set.mulIndicator_apply, Set.mem_setOf_eq, Finset.mem_coe, Nat.mem_primeFactors,
      ne_eq, mul_ite, ite_mul, one_mul, mul_one]
    by_cases h : p.Prime; swap
    · simp only [h, false_and, if_false]
    simp only [h, true_and, if_true]
    by_cases hp' : p ∣ N; swap
    · simp only [hp', false_and, ↓reduceIte, inv_inj, sub_right_inj, mul_eq_mul_right_iff,
        cpow_eq_zero_iff, Nat.cast_eq_zero, h.ne_zero, ne_eq, neg_eq_zero, or_false]
      have hq : IsUnit (p : ZMod N) := (ZMod.isUnit_prime_iff_not_dvd h).mpr hp'
      have := hq.unit_spec ▸ DirichletCharacter.changeLevel_eq_cast_of_dvd χ hMN hq.unit
      simp only [this, ZMod.cast_natCast hMN]
    · simp only [hp', NeZero.ne N, not_false_eq_true, and_self, ↓reduceIte]
      have : ¬IsUnit (p : ZMod N) := by rwa [ZMod.isUnit_prime_iff_not_dvd h, not_not]
      rw [MulChar.map_nonunit _ this, zero_mul, sub_zero, inv_one]
      refine (inv_mul_cancel₀ ?_).symm
      rw [sub_ne_zero, ne_comm]
      -- Remains to show `χ p * p ^ (-s) ≠ 1`. We show its norm is strictly `< 1`.
      apply_fun (‖·‖)
      simp only [norm_mul, norm_one]
      have ha : ‖χ p‖ ≤ 1 := χ.norm_le_one p
      have hb : ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := norm_prime_cpow_le_one_half ⟨p, h⟩ hs
      exact ((mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans_lt (by norm_num)).ne

lemma LFunction_changeLevel_aux {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : s ≠ 1) :
    LFunction (changeLevel hMN χ) s =
      LFunction χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) := by
    refine (isConnected_compl_singleton_of_one_lt_rank ?_ _).isPreconnected
    simp only [rank_real_complex, Nat.one_lt_ofNat]
  have hne : 2 ∈ ({1}ᶜ : Set ℂ) := by norm_num
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (g := fun s ↦ LFunction χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))) ?_ ?_ hpc hne ?_ hs
  · refine DifferentiableOn.analyticOnNhd (fun s hs ↦ ?_) isOpen_compl_singleton
    exact (differentiableAt_LFunction ((changeLevel hMN) χ) s (.inl hs)).differentiableWithinAt
  · refine DifferentiableOn.analyticOnNhd (fun s hs ↦ ?_) isOpen_compl_singleton
    refine ((differentiableAt_LFunction _ _ (.inl hs)).mul ?_).differentiableWithinAt
    refine .finset_prod fun i hi ↦ ?_
    refine (differentiableAt_const _).sub ((differentiableAt_const _).mul ?_)
    apply differentiableAt_id.neg.const_cpow
    exact .inl (mod_cast (Nat.pos_of_mem_primeFactors hi).ne')
  · refine eventually_of_mem ?_  (fun t (ht : 1 < t.re) ↦ ?_)
    · exact (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num : 1 < (2 : ℂ).re)
    · simpa only [LFunction_eq_LSeries _ ht] using LSeries_changeLevel hMN χ ht

/-- If `χ` is a Dirichlet character and its level `M` divides `N`, then we obtain the L function
of `χ` considered as a Dirichlet character of level `N` from the L function of `χ` by multiplying
with `∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))`. -/
lemma LFunction_changeLevel {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (h : χ ≠ 1 ∨ s ≠ 1) :
    (changeLevel hMN χ).LFunction s =
       χ.LFunction s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  rcases h with h | h
  · have hχ : changeLevel hMN χ ≠ 1 := fun H ↦ h <| (changeLevel_eq_one_iff hMN).mp H
    have h' :
        Continuous fun s ↦ χ.LFunction s * ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s)) :=
      Continuous.mul (differentiable_LFunction h).continuous <|
        continuous_finset_prod _ fun p hp ↦ Continuous.sub continuous_const <|
        Continuous.mul continuous_const <|
          @continuous_cpow_natCast_neg p ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    have H s (hs : s ≠ 1) := LFunction_changeLevel_aux hMN χ hs
    revert s
    rw [← funext_iff]
    exact Continuous.ext_on (dense_compl_singleton 1) (differentiable_LFunction hχ).continuous h' H
  · exact LFunction_changeLevel_aux hMN χ h

/-- The L function of the trivial Dirichlet character mod `N` is obtained from the Riemann
zeta function by multiplying with `∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))`. -/
lemma LFunction_one_eq_mul_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    LFunction_one N s = (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s := by
  rw [← LFunction_modOne_eq (χ := 1), LFunction_one, ← changeLevel_one N.one_dvd, mul_comm]
  convert LFunction_changeLevel N.one_dvd 1 (.inr hs) using 4 with p
  rw [MulChar.one_apply <| isUnit_of_subsingleton _, one_mul]

/-- The L function of the trivial Dirichlet character mod `N` has a simple pole with
residue `∏ p ∈ N.primeFactors, (1 - p⁻¹)` at `s = 1`. -/
lemma LFunction_one_residue_one :
  Filter.Tendsto (fun s ↦ (s - 1) * LFunction_one N s) (nhdsWithin 1 {1}ᶜ)
    (nhds <| ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)) := by
  -- need to use that `s ≠ 1`
  have H : (fun s ↦ (s - 1) * LFunction_one N s) =ᶠ[nhdsWithin 1 {1}ᶜ]
        fun s ↦ (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))) * ((s - 1) * riemannZeta s) := by
    refine Set.EqOn.eventuallyEq_nhdsWithin fun s hs ↦ ?_
    rw [mul_left_comm, LFunction_one_eq_mul_riemannZeta hs]
  rw [tendsto_congr' H]
  conv => enter [3, 1]; rw [← mul_one <| Finset.prod ..]; enter [1, 2, p]; rw [← cpow_neg_one]
  convert Tendsto.mul (f := fun s ↦ ∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s)))
    ?_ riemannZeta_residue_one
  refine tendsto_nhdsWithin_of_tendsto_nhds <| Continuous.tendsto ?_ 1
  exact continuous_finset_prod _ fun p hp ↦ Continuous.sub continuous_const <|
    @continuous_cpow_natCast_neg p ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩

open Nat ArithmeticFunction

/-- For positive `x` and nonzero `y` we have that
$|L(\chi^0, x)^3 \cdot L(\chi, x+iy)^4 \cdot L(\chi^2, x+2iy)| \ge 1$. -/
lemma norm_dirichlet_product_ge_one {N : ℕ} (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 0 < x)
    (y : ℝ) :
    ‖L ↗(1 : DirichletCharacter ℂ N) (1 + x) ^ 3 * L ↗χ (1 + x + I * y) ^ 4 *
      L ↗(χ ^ 2 :) (1 + x + 2 * I * y)‖ ≥ 1 := by
  let χ₀ := (1 : DirichletCharacter ℂ N)
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_of_pos y hx
  have hx₁ : 1 + (x : ℂ) = (1 + x : ℂ).re := by -- kills three goals of the `convert` below
    simp only [add_re, one_re, ofReal_re, ofReal_add, ofReal_one]
  have hsum₀ :=
    (hasSum_re (summable_neg_log_one_sub_char_mul_prime_cpow χ₀ h₀).hasSum).summable.mul_left 3
  have hsum₁ :=
    (hasSum_re (summable_neg_log_one_sub_char_mul_prime_cpow χ h₁).hasSum).summable.mul_left 4
  have hsum₂ :=
    (hasSum_re (summable_neg_log_one_sub_char_mul_prime_cpow (χ ^ 2) h₂).hasSum).summable
  rw [← DirichletCharacter.LSeries_eulerProduct' _ h₀,
    ← DirichletCharacter.LSeries_eulerProduct' χ h₁,
    ← DirichletCharacter.LSeries_eulerProduct' (χ ^ 2) h₂, ← exp_nat_mul, ← exp_nat_mul, ← exp_add,
    ← exp_add, norm_eq_abs, abs_exp]
  simp only [Nat.cast_ofNat, add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero,
    Real.one_le_exp_iff]
  rw [re_tsum <| summable_neg_log_one_sub_char_mul_prime_cpow _ h₀,
    re_tsum <| summable_neg_log_one_sub_char_mul_prime_cpow _ h₁,
    re_tsum <| summable_neg_log_one_sub_char_mul_prime_cpow _ h₂, ← tsum_mul_left, ← tsum_mul_left,
    ← tsum_add hsum₀ hsum₁, ← tsum_add (hsum₀.add hsum₁) hsum₂]
  convert tsum_nonneg fun p : Nat.Primes ↦ re_log_comb_nonneg_dirichlet χ p.prop.two_le h₀
  rw [sq, sq, MulChar.mul_apply]

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- A variant of `norm_dirichlet_product_ge_one` in terms of the L functions. -/
lemma norm_LFunction_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖LFunction_one N (1 + x) ^ 3 * χ.LFunction (1 + x + I * y) ^ 4 *
      (χ ^ 2).LFunction (1 + x + 2 * I * y)‖ ≥ 1 := by
  convert norm_dirichlet_product_ge_one χ hx y using 3
  · congr 2
    · refine DirichletCharacter.LFunction_eq_LSeries 1 ?_
      simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right, hx]
    · refine χ.LFunction_eq_LSeries ?_
      simp only [add_re, one_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero, lt_add_iff_pos_right, hx]
  · refine (χ ^ 2).LFunction_eq_LSeries ?_
    simp only [add_re, one_re, ofReal_re, mul_re, re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one,
      sub_self, zero_mul, mul_im, add_zero, ofReal_im, lt_add_iff_pos_right, hx]

lemma LFunction_one_isBigO_near_one_horizontal :
    (fun x : ℝ ↦ LFunction_one N (1 + x)) =O[𝓝[>] 0] (fun x ↦ (1 : ℂ) / x) := by
  have : (fun w : ℂ ↦ LFunction_one N (1 + w)) =O[𝓝[≠] 0] (1 / ·) := by
    have H : Tendsto (fun w ↦ w * LFunction_one N (1 + w)) (𝓝[≠] 0)
               (𝓝 <| ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)) := by
      convert Tendsto.comp (f := fun w ↦ 1 + w) (LFunction_one_residue_one (N := N)) ?_ using 1
      · ext w
        simp only [Function.comp_apply, add_sub_cancel_left]
      · refine tendsto_iff_comap.mpr <| map_le_iff_le_comap.mp <| Eq.le ?_
        convert map_punctured_nhds_eq (Homeomorph.addLeft (1 : ℂ)) 0 using 2 <;> simp
    exact ((isBigO_mul_iff_isBigO_div eventually_mem_nhdsWithin).mp <|
      Tendsto.isBigO_one ℂ H).trans <| isBigO_refl ..
  exact (isBigO_comp_ofReal_nhds_ne this).mono <| nhds_right'_le_nhds_ne 0

lemma LFunction_isBigO_of_ne_one_horizontal {y : ℝ} (hy : y ≠ 0 ∨ χ ≠ 1) :
    (fun x : ℝ ↦ χ.LFunction (1 + x + I * y)) =O[𝓝[>] 0] (fun _ ↦ (1 : ℂ)) := by
  refine Asymptotics.IsBigO.mono ?_ nhdsWithin_le_nhds
  have hy' : 1 + I * y ≠ 1 ∨ χ ≠ 1:= by
    simpa only [ne_eq, add_right_eq_self, _root_.mul_eq_zero, I_ne_zero, ofReal_eq_zero,
      false_or] using hy
  convert isBigO_comp_ofReal
    (χ.differentiableAt_LFunction _ hy').continuousAt.isBigO using 3 with x
  ring

lemma LFunction_isBigO_near_root_horizontal {y : ℝ} (hy : y ≠ 0 ∨ χ ≠ 1)
    (h : χ.LFunction (1 + I * y) = 0) :
    (fun x : ℝ ↦ χ.LFunction (1 + x + I * y)) =O[𝓝[>] 0] fun x : ℝ ↦ (x : ℂ) := by
  have hy' : 1 + I * y ≠ 1 ∨ χ ≠ 1:= by simp [hy]
  conv => enter [2, x]; rw [add_comm 1, add_assoc]
  refine (isBigO_comp_ofReal <| DifferentiableAt.isBigO_of_eq_zero ?_ h).mono
    nhdsWithin_le_nhds
  exact χ.differentiableAt_LFunction (1 + I * ↑y) hy'

/-- The L function of a Dirichlet character `χ` does not vanish at `1 + I*t` if `t ≠ 0`
or `χ^2 ≠ 1`. -/
theorem LFunction_ne_zero_of_re_eq_one_of_not_quadratic {t : ℝ} (h : χ ^ 2 ≠ 1 ∨ t ≠ 0) :
    χ.LFunction (1 + I * t) ≠ 0 := by
  intro Hz
  have H₀ : (fun _ : ℝ ↦ (1 : ℝ)) =O[𝓝[>] 0]
      (fun x ↦ LFunction_one N (1 + x) ^ 3 * χ.LFunction (1 + x + I * t) ^ 4 *
                   (χ ^ 2).LFunction (1 + x + 2 * I * t)) :=
    IsBigO.of_bound' <| eventually_nhdsWithin_of_forall
      fun _ hx ↦ (norm_one (α := ℝ)).symm ▸ (norm_LFunction_product_ge_one hx t).le
  have hz₁ : t ≠ 0 ∨ χ ≠ 1 := by
    rcases h with h | h
    · refine .inr ?_
      rintro rfl
      simp only [one_pow, ne_eq, not_true_eq_false] at h
    · exact .inl h
  have hz₂ : 2 * t ≠ 0 ∨ χ ^ 2 ≠ 1 := by
    rcases h with h | h
    · exact .inr h
    · exact .inl <| mul_ne_zero two_ne_zero h
  have H := ((LFunction_one_isBigO_near_one_horizontal (N := N)).pow 3).mul
    ((LFunction_isBigO_near_root_horizontal hz₁ Hz).pow 4)|>.mul <|
    LFunction_isBigO_of_ne_one_horizontal hz₂
  have help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | h
    · rw [ofReal_zero, zero_pow (by norm_num), mul_zero, mul_one]
    · field_simp [h]
      ring
  conv at H => enter [3, x]; rw [help]
  conv at H =>
    enter [2, x]; rw [show 1 + x + I * ↑(2 * t) = 1 + x + 2 * I * t by simp; ring]
  replace H := (H₀.trans H).norm_right
  simp only [norm_eq_abs, abs_ofReal] at H
  refine isLittleO_irrefl ?_ <| H.of_abs_right.trans_isLittleO <|
    isLittleO_id_one.mono nhdsWithin_le_nhds
  simp only [ne_eq, one_ne_zero, not_false_eq_true, frequently_true_iff_neBot]
  exact mem_closure_iff_nhdsWithin_neBot.mp <| closure_Ioi (0 : ℝ) ▸ Set.left_mem_Ici

/-- If `χ` is a Dirichlet character, then `L(χ, 1 + I*t)` does not vanish for `t ∈ ℝ`
except when `χ` is trivial and `t = 0` (then `L(χ, s)` has a simple pole at `s = 1`). -/
theorem Lfunction_ne_zero_of_re_eq_one (χ : DirichletCharacter ℂ N) (t : ℝ) (hχt : χ ≠ 1 ∨ t ≠ 0) :
    χ.LFunction (1 + I * t) ≠ 0 := by
  by_cases h : χ ^ 2 = 1 ∧ t = 0
  · simp only [ne_eq, h.2, not_true_eq_false, or_false] at hχt
    rw [h.2, ofReal_zero, mul_zero, add_zero]
    exact LFunction_at_one_ne_zero_of_quadratic h.1 hχt
  · exact LFunction_ne_zero_of_re_eq_one_of_not_quadratic <| not_and_or.mp h

end DirichletCharacter

open DirichletCharacter in
open Complex BigOperators Filter Topology Homeomorph Asymptotics in
/-- The Riemann Zeta Function does not vanish on the closed half-plane `re z ≥ 1`. -/
lemma riemannZeta_ne_zero_of_one_le_re ⦃z : ℂ⦄ (hz : z ≠ 1) (hz' : 1 ≤ z.re) : ζ z ≠ 0 := by
  refine hz'.eq_or_lt.elim (fun h Hz ↦ ?_) riemannZeta_ne_zero_of_one_lt_re
  rw [← LFunction_modOne_eq (χ := 1)] at Hz
  have hz₀ : z.im ≠ 0 := by
    rw [← re_add_im z, ← h, ofReal_one] at hz
    simpa only [ne_eq, add_right_eq_self, mul_eq_zero, ofReal_eq_zero, I_ne_zero, or_false]
      using hz
  have hzeq : z = 1 + I * z.im := by
    rw [mul_comm I, ← re_add_im z, ← h]
    push_cast
    simp only [add_im, one_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
      add_zero, zero_add]
  exact LFunction_ne_zero_of_re_eq_one_of_not_quadratic (N := 1) (.inr hz₀) (hzeq ▸ Hz)

/-!
### The logarithmic derivative of ζ has a simple pole at s = 1 with residue -1

We show that `s ↦ ζ' s / ζ s + 1 / (s - 1)` (or rather, its negative, which is the function
we need for the Wiener-Ikehara Theorem) is continuous outside the zeros of `ζ`.
-/

/-- The function obtained by "multiplying away" the pole of `ζ`. Its (negative) logarithmic
derivative is the function used in the Wiener-Ikehara Theorem to prove the Prime Number
Theorem. -/
noncomputable def ζ₁ : ℂ → ℂ := Function.update (fun z ↦ ζ z * (z - 1)) 1 1

lemma ζ₁_apply_of_ne_one {z : ℂ} (hz : z ≠ 1) : ζ₁ z = ζ z * (z - 1) := by
  simp [ζ₁, hz]

lemma ζ₁_differentiable : Differentiable ℂ ζ₁ := by
  rw [← differentiableOn_univ,
    ← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem, ζ₁]
  refine ⟨DifferentiableOn.congr (f := fun z ↦ ζ z * (z - 1))
    (fun _ hz ↦ DifferentiableAt.differentiableWithinAt ?_) fun _ hz ↦ ?_,
    continuousWithinAt_compl_self.mp ?_⟩
  · simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and] at hz
    exact (differentiableAt_riemannZeta hz).mul <| (differentiableAt_id').sub <|
      differentiableAt_const 1
  · simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and] at hz
    simp only [ne_eq, hz, not_false_eq_true, Function.update_noteq]
  · conv in (_ * _) => rw [mul_comm]
    simp only [continuousWithinAt_compl_self, continuousAt_update_same]
    exact riemannZeta_residue_one

lemma deriv_ζ₁_apply_of_ne_one  {z : ℂ} (hz : z ≠ 1) :
    deriv ζ₁ z = deriv ζ z * (z - 1) + ζ z := by
  have H : deriv ζ₁ z = deriv (fun w ↦ ζ w * (w - 1)) z := by
    refine Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨{w | w ≠ 1}, IsOpen.mem_nhds isOpen_ne hz, fun w hw ↦ ?_⟩
    simp only [ζ₁, ne_eq, Set.mem_setOf.mp hw, not_false_eq_true, Function.update_noteq]
  rw [H, deriv_mul (differentiableAt_riemannZeta hz) <| differentiableAt_id'.sub <|
    differentiableAt_const 1, deriv_sub_const, deriv_id'', mul_one]

lemma neg_logDeriv_ζ₁_eq {z : ℂ} (hz₁ : z ≠ 1) (hz₂ : ζ z ≠ 0) :
    -deriv ζ₁ z / ζ₁ z = -deriv ζ z / ζ z - 1 / (z - 1) := by
  rw [ζ₁_apply_of_ne_one hz₁, deriv_ζ₁_apply_of_ne_one hz₁]
  field_simp [sub_ne_zero.mpr hz₁]
  ring

lemma continuousOn_neg_logDeriv_ζ₁ :
    ContinuousOn (fun z ↦ -deriv ζ₁ z / ζ₁ z) {z | z = 1 ∨ ζ z ≠ 0} := by
  simp_rw [neg_div]
  refine ((ζ₁_differentiable.contDiff.continuous_deriv le_rfl).continuousOn.div
    ζ₁_differentiable.continuous.continuousOn fun w hw ↦ ?_).neg
  rcases eq_or_ne w 1 with rfl | hw'
  · simp only [ζ₁, Function.update_same, ne_eq, one_ne_zero, not_false_eq_true]
  · simp only [ne_eq, Set.mem_setOf_eq, hw', false_or] at hw
    simp only [ζ₁, ne_eq, hw', not_false_eq_true, Function.update_noteq, _root_.mul_eq_zero, hw,
      false_or]
    exact sub_ne_zero.mpr hw'

/-!
### Derivation of the Prime Number Theorem from the Wiener-Ikehara Theorem
-/

open Filter Nat ArithmeticFunction in
/-- The *Wiener-Ikehara Theorem* implies the *Prime Number Theorem* in the form that
`ψ x ∼ x`, where `ψ x = ∑ n < x, Λ n` and `Λ` is the von Mangoldt function. -/
theorem PNT_vonMangoldt (WIT : WienerIkeharaTheorem) :
    Tendsto (fun N : ℕ ↦ ((Finset.range N).sum Λ) / N) atTop (nhds 1) := by
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
    tauto

-- not sure we need this
/- open BigOperators Finset ZMod in
lemma prod_primesBelow_mul_eq_prod_primesBelow {N : ℕ} (hN : N ≠ 0) {s : ℂ} (hs : 1 < s.re)
    {n : ℕ} (hn : N < n) :
    (∏ p in primesBelow n, (1 - (p : ℂ) ^ (-s))⁻¹) * (∏ p in N.primeFactors, (1 - (p : ℂ) ^ (-s))) =
        ∏ p in primesBelow n, (1 - (1 : DirichletCharacter ℂ N) p * (p : ℂ) ^ (-s))⁻¹ := by
  letI ε : DirichletCharacter ℂ N := 1
  rw [mul_comm]
  have hd : Disjoint N.primeFactors (n.primesBelow.filter (· ∉ N.primeFactors)) := by
    convert disjoint_filter_filter_neg N.primeFactors n.primesBelow (· ∈ N.primeFactors)
    rw [filter_mem_eq_inter, inter_self]
  have hdeq : disjUnion _ _ hd = primesBelow n := by
    simp only [disjUnion_eq_union]
    ext p
    simp only [mem_union, mem_filter]
    refine ⟨fun H' ↦ H'.elim (fun H ↦ ?_) fun H ↦ H.1, fun _ ↦ by tauto⟩
    exact mem_primesBelow.mpr ⟨(le_of_mem_primeFactors H).trans_lt hn, prime_of_mem_primeFactors H⟩
  have H₁ := hdeq ▸ prod_disjUnion (f := fun p : ℕ ↦ (1 - ε p * (p : ℂ) ^ (-s))⁻¹) hd
  have H₂ := hdeq ▸ prod_disjUnion (f := fun p : ℕ ↦ (1 - (p : ℂ) ^ (-s))⁻¹) hd
  have H₃ : ∏ p in N.primeFactors, (1 - ε p * (p : ℂ) ^ (-s))⁻¹ = 1 := by
    refine prod_eq_one fun p hp ↦ ?_
    rw [MulChar.map_nonunit _ <| not_isUnit_of_mem_primeFactors hp, zero_mul, sub_zero, inv_one]
  rw [H₁, H₂, H₃, one_mul, ← mul_assoc, ← prod_mul_distrib]; clear H₁ H₂ H₃
  conv => enter [2]; rw [← one_mul (∏ p in (n.primesBelow.filter _), _)]
  congr 1
  · exact prod_eq_one fun p hp ↦
      mul_inv_cancel <| one_sub_prime_cpow_ne_zero (prime_of_mem_primeFactors hp) hs
  · refine prod_congr rfl fun p hp ↦ ?_
    simp only [mem_primeFactors, ne_eq, hN, not_false_eq_true, and_true, not_and, mem_filter] at hp
    have hp₁ := (mem_primesBelow.mp hp.1).2
    rw [MulChar.one_apply <| isUnit_prime_of_not_dvd hp₁ <| hp.2 hp₁, one_mul]

open BigOperators in
lemma LSeries.exists_extension_of_trivial {N : ℕ} (hN : N ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    L ↗(1 : DirichletCharacter ℂ N) s = ζ s * ∏ p in N.primeFactors, (1 - (p : ℂ) ^ (-s)) := by
  have Hζ := (riemannZeta_eulerProduct hs).mul_const (∏ p in N.primeFactors, (1 - (p : ℂ) ^ (-s)))
  have HL := dirichletLSeries_eulerProduct (1 : DirichletCharacter ℂ N) hs
  have Hev : (fun n : ℕ ↦ (∏ p in primesBelow n, (1 - (p : ℂ) ^ (-s))⁻¹) *
    (∏ p in N.primeFactors, (1 - (p : ℂ) ^ (-s)))) =ᶠ[Filter.atTop]
      (fun n : ℕ ↦ ∏ p in primesBelow n,
        (1 - (1 : DirichletCharacter ℂ N) p * (p : ℂ) ^ (-s))⁻¹) := by
    refine Filter.eventuallyEq_of_mem (s := {n | N < n}) ?_
      fun _ ↦ prod_primesBelow_mul_eq_prod_primesBelow hN hs
    simp only [Filter.mem_atTop_sets, Set.mem_setOf_eq]
    exact ⟨N + 1, fun _ hm ↦ hm⟩
  convert (tendsto_nhds_unique (Filter.Tendsto.congr' Hev Hζ) HL).symm using 1
  rw [LSeries]
  congr
  funext n
  simp only [dirichletSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [term_zero, cast_zero, CharP.cast_eq_zero, ne_eq, neg_eq_zero,
    ne_zero_of_one_lt_re hs, not_false_eq_true, zero_cpow, mul_zero]
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, cpow_neg] -/
