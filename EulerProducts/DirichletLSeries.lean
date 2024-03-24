import EulerProducts.LSeries
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.ZetaFunction
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.LSeries.Deriv

open scoped LSeries.notation

section delta

/-!
### L-series of δ

We define `LSeries.delta` (with notation `δ`) to be the indicator function of `{1}`.
Its `LSeries` is the constant function `1`.
-/

namespace LSeries

open Nat Complex

/-- The indicator function of `{1} ⊆ ℕ` with values in `ℂ`. -/
def delta (n : ℕ) : ℂ :=
  if n = 1 then 1 else 0

@[inherit_doc]
scoped[LSeries.notation] notation "δ" => delta

lemma term_delta (s : ℂ) (n : ℕ) : term δ s n = if n = 1 then 1 else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [term_zero, zero_ne_one, ↓reduceIte]
  · simp only [ne_eq, hn, not_false_eq_true, term_of_ne_zero, delta]
    rcases eq_or_ne n 1 with rfl | hn'
    · simp only [↓reduceIte, cast_one, one_cpow, ne_eq, one_ne_zero, not_false_eq_true, div_self]
    · simp only [hn', ↓reduceIte, zero_div]

/-- The L-series of `δ` is the constant function `1`. -/
lemma _root_.LSeries_delta : L δ = 1 := by
  ext
  simp only [LSeries, term_delta, tsum_ite_eq, Pi.one_apply]

lemma mul_delta {f : ℕ → ℂ} (h : f 1 = 1) : f * δ = δ := by
  ext n
  simp only [Pi.mul_apply, delta, mul_ite, mul_one, mul_zero]
  split_ifs with hn <;> simp only [hn, h]

lemma delta_mul {f : ℕ → ℂ} (h : f 1 = 1) : δ * f = δ :=
  (mul_comm δ f) ▸ mul_delta h

end LSeries

lemma ArithmeticFunction.one_eq_delta : ↗(1 : ArithmeticFunction ℂ) = δ := by
  ext n
  rcases eq_or_ne n 0 with rfl | _
  · simp only [map_zero, LSeries.delta, zero_ne_one, ↓reduceIte]
  · simp only [one_apply, LSeries.delta]

end delta


section Moebius

/-!
### The L-series of the Möbius function

We show that `L μ s` converges absolutely if and only if `re s > 1`.
-/

namespace ArithmeticFunction

open LSeries Nat Complex

lemma not_LSeriesSummable_moebius_at_one : ¬ LSeriesSummable ↗μ 1 := by
  by_contra! h
  refine not_summable_one_div_on_primes <| summable_ofReal.mp <| Summable.of_neg ?_
  simp only [← Pi.neg_def, Set.indicator_comp_of_zero ofReal_zero, ofReal_inv, ofReal_nat_cast]
  convert h.indicator {n | n.Prime} using 1
  ext n
  by_cases hn : n ∈ {p | p.Prime}
  · simp only [Pi.neg_apply, Set.indicator_of_mem hn, ofReal_div, ofReal_one, ofReal_nat_cast,
      neg_div', term_of_ne_zero hn.ne_zero, moebius_apply_prime hn, Int.reduceNeg, Int.cast_neg,
      Int.cast_one, cpow_one]
  · simp only [one_div, Pi.neg_apply, Set.indicator_of_not_mem hn, ofReal_zero, neg_zero]

/-- The L-series of the Möbius function converges absolutely at `s` if and only if `re s > 1`. -/
lemma moebius_LSeriesSummable_iff {s : ℂ} : LSeriesSummable ↗μ s ↔ 1 < s.re := by
  refine ⟨fun H ↦? _, LSeriesSummable_of_bounded_of_one_lt_re (m := 1) fun n ↦ ?_⟩
  · by_contra! h
    have h' : s.re ≤ (1 : ℂ).re := by simp only [one_re, h]
    exact not_LSeriesSummable_moebius_at_one <| LSeriesSummable.of_re_le_re h' H
  · rw [abs_intCast, ← Int.cast_abs]
    norm_cast
    rcases eq_or_ne (μ n) 0 with h | h
    · simp [h]
    · rcases moebius_ne_zero_iff_eq_or.mp h with h | h <;> simp [h]

/-- The abscissa of absolute convergence of the L-series of the Möbius function is `1`. -/
lemma abscissaOfAbsConv_mu : abscissaOfAbsConv ↗μ = 1 := by
  simpa only [abscissaOfAbsConv, moebius_LSeriesSummable_iff, ofReal_re, Set.Ioi_def,
    EReal.image_coe_Ioi, EReal.coe_one] using csInf_Ioo <| EReal.coe_lt_top _

end ArithmeticFunction

end Moebius

/-!
### L-series of Dirichlet characters
-/

/-- `χ₁` is notation for the (trivial) Dirichlet charcater modulo `1`. -/
local notation (name := Dchar_one) "χ₁" => (1 : DirichletCharacter ℂ 1)

namespace DirichletCharacter

open LSeries Nat Complex

lemma mul_convolution_distrib {R : Type*} [CommSemiring R] {n : ℕ} (χ : DirichletCharacter R n)
    (f g : ℕ → R) :
    ((χ ·) : ℕ → R) * (f ⍟ g) = (((χ ·) : ℕ → R) * f) ⍟ (((χ ·) : ℕ → R) * g) := by
  ext n
  simp only [Pi.mul_apply, LSeries.convolution_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [(Nat.mem_divisorsAntidiagonal.mp hp).1.symm, Nat.cast_mul, map_mul]
  exact mul_mul_mul_comm ..

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta in
lemma convolution_mul_moebius {n : ℕ} (χ : DirichletCharacter ℂ n) :
    ↗χ ⍟ (↗χ * ↗μ) = δ := by
  nth_rewrite 1 [← mul_one ↗χ]
  rw [← mul_convolution_distrib χ 1 ↗μ]
  have : (1 : ℕ → ℂ) ⍟ (μ ·) = δ := by
    ext n
    have H : (1 : ℕ → ℂ) ⍟ (μ ·) = (((ζ * μ :) ·) : ℕ → ℂ) := by
      ext n
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.convolution_def, divisorsAntidiagonal_zero, Pi.one_apply, one_mul,
          Finset.sum_empty, ArithmeticFunction.coe_zeta_mul_moebius, ArithmeticFunction.map_zero,
          Int.cast_zero]
      simp only [LSeries.convolution_def, Pi.one_apply, one_mul, ArithmeticFunction.mul_apply]
      norm_cast
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      have : p.1 ≠ 0 := Nat.ne_zero_of_mul_ne_zero_left <|
        (Nat.mem_divisorsAntidiagonal.mp hp).1.symm ▸ hn
      simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, this, ↓reduceIte,
        cast_one, one_mul]
    simp only [H, ArithmeticFunction.coe_zeta_mul_moebius, ArithmeticFunction.one_apply,
      Int.cast_ite, Int.cast_one, Int.cast_zero, delta]
  rw [this]
  exact mul_delta <| by simp only [cast_one, map_one]

lemma mul_delta {n : ℕ} (χ : DirichletCharacter ℂ n) : ↗χ * δ = δ := by
  ext n
  simp only [Pi.mul_apply, delta, mul_ite, mul_one, mul_zero]
  split_ifs with h <;> simp only [h, cast_one, map_one]

lemma delta_mul {n : ℕ} (χ : DirichletCharacter ℂ n) : δ * ↗χ = δ := by
  rw [mul_comm]
  exact mul_delta ..

lemma modZero_eq_delta {χ : DirichletCharacter ℂ 0} : ↗χ = δ := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [CharP.cast_eq_zero, isUnit_zero_iff, zero_ne_one, not_false_eq_true,
      MulCharClass.map_nonunit, delta, ↓reduceIte]
  rcases eq_or_ne n 1 with rfl | hn'
  · simp only [cast_one, map_one, delta, ↓reduceIte]
  have : ¬ IsUnit (n : ZMod 0) := by
    contrapose! hn'
    exact ZMod.eq_one_of_isUnit_natCast hn'
  simp only [MulChar.map_nonunit χ this, delta, hn', ↓reduceIte]

lemma modOne_eq_one {R : Type*} [CommSemiring R] {χ : DirichletCharacter R 1} :
    ((χ ·) : ℕ → R) = 1 := by
  ext n
  have : χ = (MulChar.trivial (ZMod 1) _) := χ.level_one
  rw [this, MulChar.trivial_apply]
  simp only [isUnit_of_subsingleton, ↓reduceIte, Pi.one_apply]

lemma LSeries_modOne_eq : L ↗χ₁ = L 1 := by
  ext s
  refine LSeries_congr s fun n _ ↦ ?_
  simp only [MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Pi.one_apply]

lemma not_LSeriesSummable_at_one {N : ℕ} (hN : N ≠ 0) (χ : DirichletCharacter ℂ N) :
    ¬ LSeriesSummable ↗χ 1 := by
  by_contra! h
  refine (Real.not_summable_indicator_one_div_natCast hN 1) ?_
  refine Summable.of_nonneg_of_le (fun m ↦ Set.indicator_apply_nonneg (fun _ ↦ by positivity))
    (fun n ↦ ?_) h.norm
  rw [norm_term_eq, one_re, Real.rpow_one]
  by_cases hn : n ∈ {(m : ℕ) | (m : ZMod N) = 1}
  · rw [Set.indicator_of_mem hn]
    rcases eq_or_ne n 0 with rfl | hn₀
    · simp only [CharP.cast_eq_zero, div_zero, ↓reduceIte, le_refl]
    simp only [hn₀, ↓reduceIte]
    gcongr
    rw [hn]
    simp only [map_one, norm_one, le_refl]
  · rw [Set.indicator_of_not_mem hn]
    positivity

/-- The L-series os a Dirichlet character converges absolutely at `s` if and only if `re s > 1`. -/
lemma LSeriesSummable_iff {N : ℕ} (hN : N ≠ 0) (χ : DirichletCharacter ℂ N) {s : ℂ} :
    LSeriesSummable ↗χ s ↔ 1 < s.re := by
  refine ⟨fun H ↦? _, LSeriesSummable_of_bounded_of_one_lt_re (m := 1) fun n ↦ ?_⟩
  · by_contra! h
    have h' : s.re ≤ (1 : ℂ).re := by simp only [one_re, h]
    exact not_LSeriesSummable_at_one hN χ <| LSeriesSummable.of_re_le_re h' H
  · rw [← norm_eq_abs]
    exact fun _ ↦ χ.norm_le_one _

/-- The abscissa of absolute convergence of the L-series of a Dirichlet character is `1`. -/
lemma absicssaOfAbsConv {N : ℕ} (hn : N ≠ 0) (χ : DirichletCharacter ℂ N) :
    abscissaOfAbsConv ↗χ = 1 := by
  simpa only [abscissaOfAbsConv, LSeriesSummable_iff hn χ, ofReal_re, Set.Ioi_def,
    EReal.image_coe_Ioi, EReal.coe_one] using csInf_Ioo <| EReal.coe_lt_top _

/-- The L-series of the twist of `f` by a Dirichlet character converges at `s` if the L-series
of `f` does. -/
lemma LSeriesSummable.mul {N : ℕ} (χ : DirichletCharacter ℂ N) {f : ℕ → ℂ} {s : ℂ}
    (h : LSeriesSummable f s) :
    LSeriesSummable (↗χ * f) s := by
  refine Summable.of_norm <| h.norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  refine norm_term_le s ?_
  simp only [Pi.mul_apply, norm_mul]
  conv => enter [2]; rw [← one_mul (‖_‖)]
  gcongr
  exact DirichletCharacter.norm_le_one ..

open scoped ArithmeticFunction.Moebius in
/-- The L-series of a Dirichlet character `χ` and of the twist of `μ` by `χ` are multiplicative
inverses. -/
lemma LSeries.mul_mu_eq_one {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) : L ↗χ s * L (↗χ * ↗μ) s = 1 := by
  rcases eq_or_ne N 0 with rfl | hN
  · rw [modZero_eq_delta, LSeries_delta, LSeries.delta_mul (by norm_cast), LSeries_delta,
     Pi.one_apply, one_mul]
  rw [← LSeries_convolution ((LSeriesSummable_iff hN χ).mpr hs) ?_, convolution_mul_moebius,
    LSeries_delta, Pi.one_apply]
  exact LSeriesSummable.mul χ <| ArithmeticFunction.moebius_LSeriesSummable_iff.mpr hs


/-!
### L-series of Dirichlet characters do not vanish on re s > 1
-/

/-- The L-series of the twist of `f` by a Dirichlet character converges at `s` if the L-series
of `f` does. -/
lemma LSeriesSummable_mul {N : ℕ} (χ : DirichletCharacter ℂ N) {f : ℕ → ℂ} {s : ℂ}
    (h : LSeriesSummable f s) :
    LSeriesSummable (↗χ * f) s := by
  refine Summable.of_norm <| h.norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  refine LSeries.norm_term_le s ?_
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) <| DirichletCharacter.norm_le_one ..

/-- The L-series of a Dirichlet character does not vanish on the right half-plane `re s > 1`. -/
lemma LSeries_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    L ↗χ s ≠ 0 :=
  fun h ↦ by simpa [h] using LSeries.mul_mu_eq_one χ hs

end DirichletCharacter

section zeta

/-!
### The L-series of the arithmetic function ζ
-/

namespace ArithmeticFunction

open LSeries Nat Complex DirichletCharacter

/-- The `LSeries` of the arithmetic function `ζ` is the same as the `LSeries` associated
to the constant function `1`. -/
lemma LSeries_zeta_eq : L ↗ζ = L 1 := by
  ext s
  refine LSeries_congr s fun n hn ↦ ?_
  simp only [zeta_apply, hn, ↓reduceIte, cast_one, Pi.one_apply]

/-- The abscissa of (absolute) convergence of the constant sequence `1` is `1`. -/
lemma abscissaOfAbsConv_one : abscissaOfAbsConv 1 = 1 :=
  modOne_eq_one (R := ℂ) ▸ absicssaOfAbsConv one_ne_zero χ₁

/-- The abscissa of (absolute) convergence of the arithmetic function `ζ` is `1`. -/
lemma abscissaOfAbsConv_zeta : abscissaOfAbsConv ↗ζ = 1 := by
  rw [abscissaOfAbsConv_congr (g := 1) fun n hn ↦ by simp [hn]]
  exact abscissaOfAbsConv_one

/-- The L-series of the arithmetic function `ζ` equals the Riemann Zeta Function on its
domain of convergence `1 < re s`. -/
lemma LSeries_zeta_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) : L ↗ζ s = riemannZeta s := by
  simp only [LSeries, natCoe_apply, zeta_apply, cast_ite, CharP.cast_eq_zero, cast_one]
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  refine tsum_congr fun n ↦ ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [ne_zero_of_one_lt_re hs]
  simp only [ne_eq, hn.ne', not_false_eq_true, term_of_ne_zero, ↓reduceIte, one_div]

/-- The L-series of the constant sequence `1` equals the Riemann Zeta Function on its
domain of convergence `1 < re s`. -/
lemma _root_.LSeries_one_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) : L 1 s = riemannZeta s :=
  ArithmeticFunction.LSeries_zeta_eq ▸ LSeries_zeta_eq_riemannZeta hs

/-- The L-series of the arithmetic function `ζ` equals the Riemann Zeta Function on its
domain of convergence `1 < re s`. -/
lemma LSeriesHasSum_zeta {s : ℂ} (hs : 1 < s.re) : LSeriesHasSum ↗ζ s (riemannZeta s) :=
  LSeries_zeta_eq_riemannZeta hs ▸ (zeta_LSeriesSummable_iff_one_lt_re.mpr hs).LSeriesHasSum

/-- The L-series of the constant sequence `1` equals the Riemann Zeta Function on its
domain of convergence `1 < re s`. -/
lemma _root_.LSeriesHasSum_one {s : ℂ} (hs : 1 < s.re) : LSeriesHasSum 1 s (riemannZeta s) :=
  LSeries_one_eq_riemannZeta hs ▸ (LSeriesSummable.one_iff_one_lt_re.mpr hs).LSeriesHasSum

-- Rename `zeta_LSeriesSummable_iff_one_lt_re` → `zeta_LSeriesSummable_iff`

lemma convolution_zeta_moebius : ↗ζ ⍟ ↗μ = δ := by
  have hζ : ↗ζ = ↗(ζ : ArithmeticFunction ℂ) := by
    simp only [zeta_apply, cast_ite, CharP.cast_eq_zero, cast_one, natCoe_apply]
  have hμ : ↗μ = ↗(μ : ArithmeticFunction ℂ) := by
    simp only [intCoe_apply]
  ext
  simp only [hμ, hζ, mul_to_convolution, coe_zeta_mul_coe_moebius, one_apply, delta]

/-- The L-series of the constant sequence `1` and of the Möbius function are inverses. -/
lemma _root_.LSeries_one_mul_Lseries_moebius {s : ℂ} (hs : 1 < s.re) : L 1 s * L ↗μ s = 1 := by
  rw [← LSeries_zeta_eq, ← LSeries_convolution (zeta_LSeriesSummable_iff_one_lt_re.mpr hs)
    (moebius_LSeriesSummable_iff.mpr hs),
    convolution_zeta_moebius, LSeries_delta, Pi.one_apply]

/-- The L-series of the constant sequence `1` does not vanish on the right half-plane
`re s > 1`.-/
lemma _root_.LSeries_one_ne_zero {s : ℂ} (hs : 1 < s.re) : L 1 s ≠ 0 :=
  fun h ↦ by simpa [h] using LSeries_one_mul_Lseries_moebius hs

/-- The L-series of the arithmetic function `ζ` does not vanish on the right half-plane
`re s > 1`.-/
lemma LSeries_zeta_ne_zero {s : ℂ} (hs : 1 < s.re) : L ↗ζ s ≠ 0 :=
  LSeries_zeta_eq ▸ LSeries_one_ne_zero hs

  --fun h ↦ by simpa [h] using LSeries_one_mul_Lseries_moebius hs

/-- The Riemann Zeta Function does not vanish on the half-plane `re s > 1`. -/
lemma _root_.riemannZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : riemannZeta s ≠ 0 :=
  LSeries_one_eq_riemannZeta hs ▸ LSeries_one_ne_zero hs

end ArithmeticFunction

end zeta


section vonMangoldt

/-!
### The L-series of the von Mangoldt function
-/

namespace ArithmeticFunction

open LSeries Nat Complex

/-- `ArithmeticFunction.vonMangoldtℂ` is a version of the von Mangoldt function
with values in `ℂ`. -/
noncomputable
abbrev vonMangoldtℂ : ArithmeticFunction ℂ where
  toFun n := Λ n
  map_zero' := by simp

@[inherit_doc]
scoped[ArithmeticFunction.vonMangoldt] notation "Λℂ" => vonMangoldtℂ

@[inherit_doc]
scoped[ArithmeticFunction] notation "Λℂ" => vonMangoldtℂ

lemma vonMangoldtℂ_eq_vonMangoldt : ↗Λℂ = ↗Λ := rfl

-- Maybe use `Complex.log` on the rhs?
lemma vonMangoldtℂ_mul_zeta :
    ↗(Λℂ * (ζ : ArithmeticFunction ℂ)) = ↗(log : ArithmeticFunction ℝ) := by
  rw [← vonMangoldt_mul_zeta]
  ext n
  simp only [mul_apply, coe_mk, natCoe_apply, zeta_apply, cast_ite, CharP.cast_eq_zero, cast_one,
    mul_ite, mul_zero, mul_one, ofReal_sum, apply_ite ofReal', ofReal_zero]

/-- The L-series of the von Mangoldt function `Λ` is summable at `s` when `re s > 1`. -/
lemma LSeriesSummable_vonMangoldt {s : ℂ} (hs : 1 < s.re) : LSeriesSummable ↗Λ s := by
  have hs' : abscissaOfAbsConv 1 < s.re := by
    rw [abscissaOfAbsConv_one]
    exact_mod_cast hs
  have hf := LSeriesSummable_logMul_of_lt_re hs'
  rw [LSeriesSummable, ← summable_norm_iff] at hf ⊢
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ norm_term_le s ?_) hf
  have hΛ : ‖↗Λ n‖ ≤ ‖Complex.log n‖ := by
    simp only [norm_eq_abs, abs_ofReal, _root_.abs_of_nonneg vonMangoldt_nonneg,
      ← Complex.natCast_log, _root_.abs_of_nonneg <| Real.log_nat_cast_nonneg n]
    exact ArithmeticFunction.vonMangoldt_le_log
  refine hΛ.trans ?_
  simp only [norm_eq_abs, norm_mul, Pi.one_apply, norm_one, mul_one, le_refl]

/-- The L-series of the von Mangoldt function `Λ` equals the negative logarithmic derivative
of the L-series of the constant sequence `1` on its domain of convergence `re s > 1`. -/
lemma LSeries_vonMangoldt_eq {s : ℂ} (hs : 1 < s.re) : L ↗Λ s = - deriv (L 1) s / L 1 s := by
  rw [← LSeries_zeta_eq]
  have hs' : abscissaOfAbsConv ↗ζ < s.re := by
    rwa [abscissaOfAbsConv_zeta, ← EReal.coe_one, EReal.coe_lt_coe_iff]
  have hΛ : LSeriesSummable ↗Λℂ s := LSeriesSummable_vonMangoldt hs
  have hζ : LSeriesSummable ↗(ζ : ArithmeticFunction ℂ) s :=
    zeta_LSeriesSummable_iff_one_lt_re.mpr hs
  rw [eq_div_iff <| LSeries_zeta_ne_zero hs, show ↗ζ = ↗(ζ : ArithmeticFunction ℂ) from rfl,
    ← vonMangoldtℂ_eq_vonMangoldt,
    ← LSeries_mul hΛ hζ,
    ← neg_eq_iff_eq_neg, show ↗(ζ : ArithmeticFunction ℂ) = ↗ζ from rfl,
     LSeries_deriv hs', vonMangoldtℂ_mul_zeta]
  congr
  ext ⟨- | n⟩
  · simp
  · rw [log_apply, logMul, zeta_apply, natCast_log]
    simp only [succ_ne_zero, ↓reduceIte, cast_one, mul_one]

/-- The L-series of the von Mangoldt function `Λ` equals the negative logarithmic derivative
of the Riemann zeta function on its domain of convergence `re s > 1`. -/
lemma LSeries_vonMangoldt_eq_deriv_riemannZeta_div {s : ℂ} (hs : 1 < s.re) :
    L ↗Λ s = - deriv riemannZeta s / riemannZeta s := by
  convert LSeries_vonMangoldt_eq hs using 2
  · refine neg_inj.mpr <| Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨{z | 1 < z.re}, (isOpen_lt continuous_const continuous_re).mem_nhds hs, ?_⟩
    exact fun _ hz ↦ (LSeries_one_eq_riemannZeta hz).symm
  · exact (LSeries_one_eq_riemannZeta hs).symm
