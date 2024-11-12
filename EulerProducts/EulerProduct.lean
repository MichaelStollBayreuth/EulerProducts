import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Euler products for L-series
-/

section preliminary

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

end preliminary

open Complex

open scoped LSeries.notation

namespace LSeries

-- Use this to golf `LSeries.term_convolution`
lemma term_mul_aux (a b : ℂ) (m n : ℕ) (s : ℂ) :
    (a / m ^ s) * (b / n ^ s) = a * b / (m * n) ^ s := by
  rw [mul_comm_div, div_div, ← mul_div_assoc, mul_comm (m : ℂ), natCast_mul_natCast_cpow]

lemma term_mul {f₁ f₂ f : ℕ → ℂ} {m n : ℕ} (h : f (m * n) = f₁ m * f₂ n) (s : ℂ) :
    term f s (m * n) = term f₁ s m * term f₂ s n := by
  rcases eq_or_ne (m * n) 0 with H | H
  · rcases mul_eq_zero.mp H with rfl | rfl <;> simp only [term_zero, mul_zero, zero_mul]
  · obtain ⟨hm, hn⟩ := mul_ne_zero_iff.mp H
    simp only [ne_eq, H, not_false_eq_true, term_of_ne_zero, Nat.cast_mul, hm, hn, h, term_mul_aux]

/-- Weak multiplicativity of `f : ℕ → ℂ` is inherited by the terms of its L-series. -/
lemma term_multiplicative {f : ℕ → ℂ} (hf : ∀ {m n}, m.Coprime n → f (m * n) = f m * f n) (s : ℂ)
    {m n : ℕ} (hcop : m.Coprime n) :
    term f s (m * n) = term f s m * term f s n :=
  term_mul (hf hcop) s

/-- Complete multiplicativity of `f : ℕ → ℂ` is inherited by the terms of its L-series. -/
lemma term_completelyMultiplicative {f : ℕ → ℂ} (hf : ∀ m n, f (m * n) = f m * f n) (s : ℂ)
    (m n : ℕ) :
    term f s (m * n) = term f s m * term f s n :=
  term_mul (hf m n) s

lemma term_at_one {f : ℕ → ℂ} (h₁ : f 1 = 1) (s : ℂ) : term f s 1 = 1 := by
  rw [term_of_ne_zero one_ne_zero, h₁, Nat.cast_one, one_cpow, div_one]

end LSeries

section eulerProduct

open Nat BigOperators Filter Topology EulerProduct

namespace LSeries

/-- The Euler product for the L-series of a weakly multiplicative sequence `f` -/
lemma eulerProduct_of_multiplicative {f : ℕ → ℂ} (h₁ : f 1 = 1)
    (hf : ∀ {m n}, m.Coprime n → f (m * n) = f m * f n) {s : ℂ} (hs : LSeriesSummable f s) :
    Tendsto (fun n : ℕ ↦ ∏ p in primesBelow n, ∑' e, term f s (p ^ e)) atTop (𝓝 (L f s)) :=
  eulerProduct (term_at_one h₁ s) (term_multiplicative hf s) hs.norm (term_zero ..)

/-- The Euler product for the L-series of a completely multiplicative sequence `f` -/
lemma eulerProduct_of_completelyMultiplicative {f : ℕ → ℂ} (h₁ : f 1 = 1)
    (hf : ∀ m n, f (m * n) = f m * f n) {s : ℂ} (hs : LSeriesSummable f s) :
    Tendsto (fun n : ℕ ↦ ∏ p in primesBelow n, (1 - term f s p)⁻¹) atTop (𝓝 (L f s)) :=
  eulerProduct_completely_multiplicative
    (f := { toFun := term f s,
            map_zero' := term_zero ..,
            map_one' := term_at_one h₁ s,
            map_mul' := term_completelyMultiplicative hf s })
    hs.norm

/-- The Euler product for the L-series of a completely multiplicative sequence `f`,
logarithmic version -/
lemma eulerProduct_of_completelyMultiplicative' {f : ℕ → ℂ} (h₁ : f 1 = 1)
    (hf : ∀ m n, f (m * n) = f m * f n) {s : ℂ} (hs : LSeriesSummable f s) :
    exp (∑' p : Nat.Primes, -log (1 - term f s p)) = L f s :=
  exp_tsum_primes_log_eq_tsum' (term_zero ..) (term_at_one h₁ s)
    (term_completelyMultiplicative hf s) hs.norm

end LSeries

open LSeries

namespace DirichletCharacter

lemma toFun_on_nat_map_one {N : ℕ} (χ : DirichletCharacter ℂ N) : ↗χ 1 = 1 := by
  simp only [cast_one, map_one]

lemma toFun_on_nat_map_mul {N : ℕ} (χ : DirichletCharacter ℂ N) (m n : ℕ) :
    ↗χ (m * n) = ↗χ m * ↗χ n := by
  simp only [cast_mul, map_mul]

/-- The Euler product formula for a Dirichlet L-series -/
theorem LSeries_eulerProduct {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun n ↦ ∏ p in primesBelow n, (1 - χ p * (p : ℂ) ^ (-s))⁻¹) atTop (𝓝 (L ↗χ s)) := by
  refine Tendsto.congr (fun n ↦ Finset.prod_congr rfl fun p hp ↦ ?_) <|
    eulerProduct_of_completelyMultiplicative (toFun_on_nat_map_one χ) (toFun_on_nat_map_mul χ) <|
    LSeriesSummable_of_one_lt_re χ hs
  rw [term_of_ne_zero (prime_of_mem_primesBelow hp).ne_zero, cpow_neg, div_eq_mul_inv]

/-- A variant of the Euler product for Dirichlet L-series. -/
theorem LSeries_eulerProduct' {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -log (1 - χ p * p ^ (-s))) = L ↗χ s := by
  rw [LSeries]
  convert exp_tsum_primes_log_eq_tsum (f := dirichletSummandHom χ <| ne_zero_of_one_lt_re hs) <|
    summable_dirichletSummand χ hs -- where does the `x✝: ℕ` come from??
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [term_zero, map_zero]
  · simp [hn, dirichletSummandHom, div_eq_mul_inv, cpow_neg]

end DirichletCharacter

open DirichletCharacter

/-- A variant of the Euler product for the L-series of `ζ`. -/
theorem ArithmeticFunction.LSeries_zeta_eulerProduct' {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = L 1 s := by
  convert modOne_eq_one (R := ℂ) ▸ LSeries_eulerProduct' (1 : DirichletCharacter ℂ 1) hs using 7
  rw [MulChar.one_apply <| isUnit_of_subsingleton _, one_mul]

/-- A variant of the Euler product for the Riemann zeta function. -/
theorem riemannZeta_eulerProduct' {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = riemannZeta s :=
  LSeries_one_eq_riemannZeta hs ▸ ArithmeticFunction.LSeries_zeta_eulerProduct' hs

end eulerProduct
