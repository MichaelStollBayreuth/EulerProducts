import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
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


open scoped LSeries.notation

lemma LSeriesSummable.mul_bounded {f g : ℕ → ℂ} {c : ℝ} {s : ℂ} (hs : LSeriesSummable f s)
    (hg : ∀ n, ‖g n‖ ≤ c) :
    LSeriesSummable (f * g) s := by
  refine Summable.of_norm <| (hs.const_smul c).norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  rw [Complex.real_smul, ← LSeries.term_smul_apply, mul_comm]
  refine LSeries.norm_term_le s ?_
  have hc : ‖(c : ℂ)‖ = c := by
    simp only [Complex.norm_eq_abs, Complex.abs_ofReal, abs_eq_self, (norm_nonneg _).trans (hg 0)]
  simpa only [Pi.mul_apply, norm_mul, Pi.smul_apply, smul_eq_mul, hc]
    using mul_le_mul_of_nonneg_right (hg n) <| norm_nonneg _

open ArithmeticFunction in
lemma LSeriesSummable.mul_moebius {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) :
    LSeriesSummable (f * ↗μ) s := by
  refine hf.mul_bounded (c := 1) fun n ↦ ?_
  simp only [Complex.norm_int]
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

/- /-- Twisting by a Dirichlet character `χ` distributes over convolution. -/
lemma mul_convolution_distrib {R : Type*} [CommSemiring R] {n : ℕ} (χ : DirichletCharacter R n)
    (f g : ℕ → R) :
    ((χ ·) : ℕ → R) * (f ⍟ g) = (((χ ·) : ℕ → R) * f) ⍟ (((χ ·) : ℕ → R) * g) := by
  ext n
  simp only [Pi.mul_apply, LSeries.convolution_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [(Nat.mem_divisorsAntidiagonal.mp hp).1.symm, Nat.cast_mul, map_mul]
  exact mul_mul_mul_comm ..

open ArithmeticFunction in
/-- The convolution of a Dirichlet character `χ` with the twist `χ * μ` is `δ`,
the indicator function of `{1}`. -/
lemma convolution_mul_moebius {n : ℕ} (χ : DirichletCharacter ℂ n) :
    ↗χ ⍟ (↗χ * ↗μ) = δ :=
  LSeries.convolution_mul_moebius (toFun_on_nat_map_one χ) (toFun_on_nat_map_mul χ)

lemma mul_delta {n : ℕ} (χ : DirichletCharacter ℂ n) : ↗χ * δ = δ := by
  refine LSeries.mul_delta ?_
  rw [cast_one, MulChar.map_one]

lemma delta_mul {n : ℕ} (χ : DirichletCharacter ℂ n) : δ * ↗χ = δ :=
  mul_comm δ _ ▸ mul_delta ..

/-- The Dirichlet character mod `0` corresponds to `δ`. -/
lemma modZero_eq_delta {χ : DirichletCharacter ℂ 0} : ↗χ = δ := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [CharP.cast_eq_zero, isUnit_zero_iff, zero_ne_one, not_false_eq_true,
      MulCharClass.map_nonunit, delta, ↓reduceIte]
  rcases eq_or_ne n 1 with rfl | hn'
  · simp only [cast_one, map_one, delta, ↓reduceIte]
  have : ¬ IsUnit (n : ZMod 0) := fun h ↦ hn' <| ZMod.eq_one_of_isUnit_natCast h
  simp only [MulChar.map_nonunit χ this, delta, hn', ↓reduceIte]

/-- The Dirichlet character mod `1` corresponds to the constant function `1`. -/
lemma modOne_eq_one {R : Type*} [CommSemiring R] {χ : DirichletCharacter R 1} :
    ((χ ·) : ℕ → R) = 1 := by
  ext
  rw [show χ = (MulChar.trivial (ZMod 1) _) from χ.level_one]
  simp only [MulChar.trivial_apply, isUnit_of_subsingleton, ↓reduceIte, Pi.one_apply]

lemma LSeries_modOne_eq : L ↗χ₁ = L 1 :=
  congr_arg L modOne_eq_one

/-- The L-series of a Dirichlet character mod `N > 0` does not converge absolutely at `s = 1`. -/
lemma not_LSeriesSummable_at_one {N : ℕ} (hN : N ≠ 0) (χ : DirichletCharacter ℂ N) :
    ¬ LSeriesSummable ↗χ 1 := by
  intro h
  refine (Real.not_summable_indicator_one_div_natCast hN 1) ?_
  refine h.norm.of_nonneg_of_le (fun m ↦ Set.indicator_apply_nonneg (fun _ ↦ by positivity))
    (fun n ↦ ?_)
  -- `Set.indicator {n | ↑n = 1} (fun n ↦ 1 / ↑n) n ≤ ‖term (fun n ↦ χ ↑n) 1 n‖`
  rw [norm_term_eq, one_re, Real.rpow_one]
  by_cases hn : n ∈ {(m : ℕ) | (m : ZMod N) = 1}
  · rw [Set.indicator_of_mem hn]
    rcases eq_or_ne n 0 with rfl | hn₀
    · simp only [CharP.cast_eq_zero, div_zero, ↓reduceIte, le_refl]
    simp only [hn₀, ↓reduceIte]
    gcongr
    rw [hn, map_one, norm_one]
  · rw [Set.indicator_of_not_mem hn]
    positivity

/-- The L-series of a Dirichlet character converges absolutely at `s` if and only if `re s > 1`. -/
lemma LSeriesSummable_iff {N : ℕ} (hN : N ≠ 0) (χ : DirichletCharacter ℂ N) {s : ℂ} :
    LSeriesSummable ↗χ s ↔ 1 < s.re := by
  refine ⟨fun H ↦ ?_, LSeriesSummable_of_bounded_of_one_lt_re fun _ _ ↦ χ.norm_le_one _⟩
  by_contra! h
  have h' : s.re ≤ (1 : ℂ).re := by simp only [one_re, h]
  exact not_LSeriesSummable_at_one hN χ <| LSeriesSummable.of_re_le_re h' H

/-- The abscissa of absolute convergence of the L-series of a Dirichlet character is `1`. -/
lemma absicssaOfAbsConv_eq_one {N : ℕ} (hn : N ≠ 0) (χ : DirichletCharacter ℂ N) :
    abscissaOfAbsConv ↗χ = 1 := by
  simpa only [abscissaOfAbsConv, LSeriesSummable_iff hn χ, ofReal_re, Set.Ioi_def,
    EReal.image_coe_Ioi, EReal.coe_one] using csInf_Ioo <| EReal.coe_lt_top _

/-- The L-series of the twist of `f` by a Dirichlet character converges at `s` if the L-series
of `f` does. -/
lemma LSeriesSummable_mul {N : ℕ} (χ : DirichletCharacter ℂ N) {f : ℕ → ℂ} {s : ℂ}
    (h : LSeriesSummable f s) :
    LSeriesSummable (↗χ * f) s := by
  refine Summable.of_norm <| h.norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  refine LSeries.norm_term_le s ?_
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) <| DirichletCharacter.norm_le_one ..

open scoped ArithmeticFunction.Moebius in
/-- The L-series of a Dirichlet character `χ` and of the twist of `μ` by `χ` are multiplicative
inverses. -/
lemma LSeries.mul_mu_eq_one {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) : L ↗χ s * L (↗χ * ↗μ) s = 1 := by
  rcases eq_or_ne N 0 with rfl | hN
  · rw [modZero_eq_delta, LSeries_delta, LSeries.delta_mul (by norm_cast), LSeries_delta,
     Pi.one_apply, one_mul]
  · rw [← LSeries_convolution' ((LSeriesSummable_iff hN χ).mpr hs) ?_, convolution_mul_moebius,
      LSeries_delta, Pi.one_apply]
    exact LSeriesSummable_mul χ <| ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
 -/

end DirichletCharacter
