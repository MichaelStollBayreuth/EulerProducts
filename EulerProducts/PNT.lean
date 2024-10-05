import EulerProducts.Auxiliary
import EulerProducts.Logarithm
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Dirichlet
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
### The Riemann Zeta Function does not vanish on Re(s) = 1
-/

open Complex

/-- We use `ζ` to denote the Rieman zeta function. -/
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
lemma re_log_comb_nonneg' {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ = 1) :
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
    convert re_log_comb_nonneg' ha₀ ha₁ hz using 6
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

-- A helper lemma used in the next two proofs
lemma one_lt_re_of_pos {x : ℝ} (y : ℝ) (hx : 0 < x) :
    1 < (1 + x : ℂ).re ∧ 1 < (1 + x + I * y).re ∧ 1 < (1 + x + 2 * I * y).re := by
  simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right, hx, mul_re, I_re, zero_mul, I_im,
    ofReal_im, mul_zero, sub_self, add_zero, re_ofNat, im_ofNat, mul_one, mul_im, and_self]

section

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

/-- For positive `x` and nonzero `y` we have that
$|\zeta(x)^3 \cdot \zeta(x+iy)^4 \cdot \zeta(x+2iy)| \ge 1$. -/
lemma norm_zeta_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖ζ (1 + x) ^ 3 * ζ (1 + x + I * y) ^ 4 * ζ (1 + x + 2 * I * y)‖ ≥ 1 := by
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_of_pos y hx
  simpa only [one_pow, norm_mul, norm_pow, DirichletCharacter.LSeries_modOne_eq,
    LSeries_one_eq_riemannZeta, h₀, h₁, h₂] using norm_dirichlet_product_ge_one χ₁ hx y

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

end

section

open Filter Topology Homeomorph Asymptotics

lemma riemannZeta_isBigO_near_one_horizontal :
    (fun x : ℝ ↦ ζ (1 + x)) =O[𝓝[>] 0] (fun x ↦ (1 : ℂ) / x) := by
  have : (fun w : ℂ ↦ ζ (1 + w)) =O[𝓝[≠] 0] (1 / ·) := by
    have H : Tendsto (fun w ↦ w * ζ (1 + w)) (𝓝[≠] 0) (𝓝 1) := by
      convert Tendsto.comp (f := fun w ↦ 1 + w) riemannZeta_residue_one ?_ using 1
      · ext w
        simp only [Function.comp_apply, add_sub_cancel_left]
      · refine tendsto_iff_comap.mpr <| map_le_iff_le_comap.mp <| Eq.le ?_
        convert map_punctured_nhds_eq (Homeomorph.addLeft (1 : ℂ)) 0 using 2 <;> simp
    exact ((isBigO_mul_iff_isBigO_div eventually_mem_nhdsWithin).mp <|
      Tendsto.isBigO_one ℂ H).trans <| isBigO_refl ..
  exact (isBigO_comp_ofReal_nhds_ne this).mono <| nhds_right'_le_nhds_ne 0

lemma riemannZeta_isBigO_of_ne_one_horizontal {y : ℝ} (hy : y ≠ 0) :
    (fun x : ℝ ↦ ζ (1 + x + I * y)) =O[𝓝[>] 0] (fun _ ↦ (1 : ℂ)) := by
  refine Asymptotics.IsBigO.mono ?_ nhdsWithin_le_nhds
  have hy' : 1 + I * y ≠ 1 := by simp [hy]
  convert isBigO_comp_ofReal
    (differentiableAt_riemannZeta hy').continuousAt.isBigO using 3 with x
  ring

lemma riemannZeta_isBigO_near_root_horizontal {y : ℝ} (hy : y ≠ 0) (h : ζ (1 + I * y) = 0) :
    (fun x : ℝ ↦ ζ (1 + x + I * y)) =O[𝓝[>] 0] fun x : ℝ ↦ (x : ℂ) := by
  have hy' : 1 + I * y ≠ 1 := by simp [hy]
  conv => enter [2, x]; rw [add_comm 1, add_assoc]
  exact (isBigO_comp_ofReal <| (differentiableAt_riemannZeta hy').isBigO_of_eq_zero h).mono
    nhdsWithin_le_nhds

/-- The Riemann Zeta Function does not vanish on the closed half-plane `re z ≥ 1`. -/
lemma riemannZeta_ne_zero_of_one_le_re ⦃z : ℂ⦄ (hz : z ≠ 1) (hz' : 1 ≤ z.re) : ζ z ≠ 0 := by
  refine hz'.eq_or_lt.elim (fun h Hz ↦ ?_) riemannZeta_ne_zero_of_one_lt_re
  -- We assume that `ζ z = 0` and `z.re = 1` and derive a contradiction.
  have hz₀ : z.im ≠ 0 := by
    rw [← re_add_im z, ← h, ofReal_one] at hz
    simpa only [ne_eq, add_right_eq_self, mul_eq_zero, ofReal_eq_zero, I_ne_zero, or_false]
      using hz
  have hzeq : z = 1 + I * z.im := by
    rw [mul_comm I, ← re_add_im z, ← h]
    push_cast
    simp only [add_im, one_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
      add_zero, zero_add]
  -- The key step: the vanishing assumption implies that the zeta product below
  -- also vanishes at `z`. We only need the right-hand limit keeping the imaginary part fixed.
  have H₀ : (fun _ : ℝ ↦ (1 : ℝ)) =O[𝓝[>] 0]
      (fun x ↦ ζ (1 + x) ^ 3 * ζ (1 + x + I * z.im) ^ 4 * ζ (1 + x + 2 * I * z.im)) :=
    IsBigO.of_bound' <| eventually_nhdsWithin_of_forall
      fun _ hx ↦ (norm_one (α := ℝ)).symm ▸ (norm_zeta_product_ge_one hx z.im).le
  have H := (riemannZeta_isBigO_near_one_horizontal.pow 3).mul
    ((riemannZeta_isBigO_near_root_horizontal hz₀ (hzeq ▸ Hz)).pow 4)|>.mul <|
    riemannZeta_isBigO_of_ne_one_horizontal <| mul_ne_zero two_ne_zero hz₀
  have help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | h
    · rw [ofReal_zero, zero_pow (by norm_num), mul_zero, mul_one]
    · field_simp [h]
      ring
  conv at H => enter [3, x]; rw [help]
  conv at H =>
    enter [2, x]; rw [show 1 + x + I * ↑(2 * z.im) = 1 + x + 2 * I * z.im by simp; ring]
  replace H := (H₀.trans H).norm_right
  simp only [norm_eq_abs, abs_ofReal] at H
  refine isLittleO_irrefl ?_ <| H.of_abs_right.trans_isLittleO <|
    isLittleO_id_one.mono nhdsWithin_le_nhds
  simp only [ne_eq, one_ne_zero, not_false_eq_true, frequently_true_iff_neBot]
  exact mem_closure_iff_nhdsWithin_neBot.mp <| closure_Ioi (0 : ℝ) ▸ Set.left_mem_Ici

end

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
