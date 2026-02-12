import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# L-series of Dirichlet characters and arithmetic functions

We collect some results on L-series of specific (arithmetic) functions, for example,
the Möbius function `μ` or the von Mangoldt function `Λ`. In particular, we show that
`L ↗Λ` is the negative of the logarithmic derivative of the Riemann zeta function
on `re s > 1`; see `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`.

We also prove some general results on L-series associated to Dirichlet characters
(i.e., Dirichlet L-series). For example, we show that the abscissa of absolute convergence
equals `1` (see `DirichletCharacter.absicssaOfAbsConv`) and that the L-series does not
vanish on the open half-plane `re s > 1` (see `DirichletCharacter.LSeries_ne_zero`).

We deduce results on the Riemann zeta function (which is `L 1` or `L ↗ζ` on `re s > 1`)
as special cases.
-/


open scoped LSeries.notation ArithmeticFunction.Moebius ArithmeticFunction.zeta

lemma LSeriesSummable.mul_bounded {f g : ℕ → ℂ} {c : ℝ} {s : ℂ} (hs : LSeriesSummable f s)
    (hg : ∀ n, ‖g n‖ ≤ c) :
    LSeriesSummable (f * g) s := by
  refine Summable.of_norm <| (hs.const_smul c).norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  rw [Complex.real_smul, ← LSeries.term_smul_apply, mul_comm]
  refine LSeries.norm_term_le s ?_
  have hc : ‖(c : ℂ)‖ = c := by simp [(norm_nonneg _).trans (hg 0)]
  simpa only [Pi.mul_apply, norm_mul, Pi.smul_apply, smul_eq_mul, hc]
    using mul_le_mul_of_nonneg_right (hg n) <| norm_nonneg _

open ArithmeticFunction in
lemma LSeriesSummable.mul_moebius {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) :
    LSeriesSummable (f * ↗μ) s := by
  refine hf.mul_bounded (c := 1) fun n ↦ ?_
  simp only [Complex.norm_intCast]
  exact_mod_cast abs_moebius_le_one


section multiplicative

/-- Twisting by a completely multiplicative function `φ` distributes over convolution. -/
lemma LSeries.mul_convolution_distrib {R : Type*} [CommSemiring R] {φ : ℕ → R}
    (hφ : ∀ m n, φ (m * n) = φ m * φ n) (f g : ℕ → R) :
    φ * (f ⍟ g) = (φ * f) ⍟ (φ * g) := by
  ext n
  simp only [Pi.mul_apply, LSeries.convolution_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [(Nat.mem_divisorsAntidiagonal.mp hp).1.symm, hφ]
  exact mul_mul_mul_comm ..

open ArithmeticFunction in
/-- The convolution of a completely multiplicative function `φ` with the twist `φ * μ` is `δ`,
the indicator function of `{1}`. -/
lemma LSeries.convolution_mul_moebius {φ : ℕ → ℂ} (h₁ : φ 1 = 1)
    (hφ : ∀ m n, φ (m * n) = φ m * φ n) :
    φ ⍟ (φ * ↗μ) = δ := by
  have : (1 : ℕ → ℂ) ⍟ (μ ·) = δ := by
    rw [one_convolution_eq_zeta_convolution, ← one_eq_delta]
    change ⇑(ζ : ArithmeticFunction ℂ) ⍟ ⇑(μ : ArithmeticFunction ℂ) = ⇑(1 : ArithmeticFunction ℂ)
    simp only [coe_mul, coe_zeta_mul_coe_moebius]
  nth_rewrite 1 [← mul_one φ]
  simp only [← mul_convolution_distrib hφ 1 ↗μ, this, mul_delta h₁]

open scoped ArithmeticFunction.Moebius in
/-- The L-series of a completely multiplicative function `φ` and of the twist of `μ` by `φ`
are multiplicative inverses. -/
lemma LSeries.mul_mu_eq_one {φ : ℕ → ℂ} (h₁ : φ 1 = 1) (hφ : ∀ m n, φ (m * n) = φ m * φ n) {s : ℂ}
    (hs : LSeriesSummable φ s) : L φ s * L (φ * ↗μ) s = 1 := by
  rw [← LSeries_convolution' hs ?_, convolution_mul_moebius h₁ hφ, LSeries_delta, Pi.one_apply]
  exact hs.mul_moebius

end multiplicative

/-!
### L-series of Dirichlet characters
-/

namespace DirichletCharacter

open LSeries Nat Complex

lemma toFun_on_nat_map_one {N : ℕ} (χ : DirichletCharacter ℂ N) : ↗χ 1 = 1 := by
  simp only [cast_one, map_one]

lemma toFun_on_nat_map_mul {N : ℕ} (χ : DirichletCharacter ℂ N) (m n : ℕ) :
    ↗χ (m * n) = ↗χ m * ↗χ n := by
  simp only [cast_mul, map_mul]

end DirichletCharacter
