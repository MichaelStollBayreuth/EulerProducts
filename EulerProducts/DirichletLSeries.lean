import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.ArithmeticFunction
import EulerProducts.LSeries
import EulerProducts.Logarithm

/-!
### Dirichlet characters as arithmetic functions
-/

namespace DirichletCharacter

open Nat ArithmeticFunction

@[coe, simps]
noncomputable def toArithmeticFunction {R : Type*} [CommMonoidWithZero R]
    {N : ℕ} (χ : DirichletCharacter R N) : ArithmeticFunction R where
      toFun n := if n = 0 then 0 else χ n
      map_zero' := by simp

attribute [simp] toArithmeticFunction_apply

noncomputable
instance {R : Type*} [CommSemiring R] {N : ℕ} :
    CoeOut (DirichletCharacter R N) (ArithmeticFunction R) where
      coe := DirichletCharacter.toArithmeticFunction

@[simp]
lemma toArithmeticFunction_apply_of_ne_zero {R : Type*} [CommMonoidWithZero R] {N : ℕ}
    (χ : DirichletCharacter R N) {n : ℕ} (hn : n ≠ 0) :
    χ.toArithmeticFunction n = χ (n : ZMod N) := by
  rw [toArithmeticFunction_apply]
  simp only [hn, ite_false]

noncomputable
instance {R : Type*} [CommSemiring R] {N : ℕ} :
    HSMul (DirichletCharacter R N) (ArithmeticFunction R) (ArithmeticFunction R) where
      hSMul := fun χ f ↦ pmul χ f

lemma hsmul_arithmeticFunction_def {R : Type*} [CommSemiring R] {N : ℕ}
    (χ : DirichletCharacter R N) (f : ArithmeticFunction R) : χ • f = pmul χ f := rfl

@[simp]
lemma hsmul_arithmeticFunction_apply {R : Type*} [CommSemiring R] {N : ℕ}
    (χ : DirichletCharacter R N) (f : ArithmeticFunction R) (n : ℕ) : (χ • f) n = χ n * f n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, cast_zero, mul_zero]
  · simp only [hsmul_arithmeticFunction_def, pmul_apply, ne_eq, hn, not_false_eq_true,
      toArithmeticFunction_apply_of_ne_zero]

lemma hsmul_arithmeticFunction_mul_distrib {R : Type*} [CommSemiring R] {N : ℕ}
    (χ : DirichletCharacter R N) (f g : ArithmeticFunction R) :
    χ • (f * g) = (χ • f) * (χ • g) := by
  ext
  simp only [hsmul_arithmeticFunction_apply, mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun km hkm ↦ ?_
  rw [mul_mul_mul_comm, ← map_mul, ← Nat.cast_mul, (mem_divisorsAntidiagonal.mp hkm).1]

lemma hsmul_arithmeticFunction_mul_assoc {R : Type*} [CommSemiring R] {N : ℕ}
    (χ ψ : DirichletCharacter R N) (f : ArithmeticFunction R) :
    χ • (ψ • f) = (χ * ψ) • f := by
  ext
  simp only [hsmul_arithmeticFunction_apply, MulChar.coeToFun_mul, Pi.mul_apply, mul_assoc]

lemma hsmul_zeta_eq_self {R : Type*} [CommSemiring R] {N : ℕ} (χ : DirichletCharacter R N) :
    χ • (ζ : ArithmeticFunction R) = χ := by
  ext n
  rw [toArithmeticFunction_apply χ n]
  simp only [hsmul_arithmeticFunction_apply, natCoe_apply, zeta_apply, cast_ite, cast_zero,
    cast_one, mul_ite, mul_zero, mul_one]

lemma hsmul_one {R : Type*} [CommSemiring R] {N : ℕ} (χ : DirichletCharacter R N) :
    χ • (1 : ArithmeticFunction R) = 1 := by
  ext
  simp (config := { contextual := true })
    only [hsmul_arithmeticFunction_apply, one_apply, mul_ite, mul_one, mul_zero, cast_one, map_one]

end DirichletCharacter


namespace Nat.ArithmeticFunction

open Complex

/-!
### L-series of Dirichlet characters
-/

scoped notation (name := Lseries) "L" => LSeries

local notation (name := Dchar_one) "χ₁" => (1 : DirichletCharacter ℂ 1)

open DirichletCharacter in
lemma dirichletCharModZero_eq_one {R : Type*} [CommSemiring R] {χ : DirichletCharacter R 0} :
    (χ : ArithmeticFunction R) = 1 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [map_zero]
  rcases eq_or_ne n 1 with rfl | hn'
  · simp only [ne_eq, one_ne_zero, not_false_eq_true, toArithmeticFunction_apply_of_ne_zero,
      cast_one, map_one, one_one]
  have : ¬ IsUnit (n : ZMod 0)
  · contrapose! hn'
    exact ZMod.eq_one_of_isUnit_natCast hn'
  simp only [ne_eq, hn, not_false_eq_true, toArithmeticFunction_apply_of_ne_zero,
    MulChar.map_nonunit χ this, hn', one_apply_ne]

open DirichletCharacter in
lemma dirichletCharModZero_hsmul {R : Type*} [CommSemiring R] {χ : DirichletCharacter R 0}
    {f : ArithmeticFunction R} (hf : f 1 = 1) : χ • f = 1 := by
  ext n
  simp only [hsmul_arithmeticFunction_apply, one_apply]
  rcases eq_or_ne n 1 with rfl | hn
  · simp only [cast_one, map_one, hf, mul_one, ite_true]
  · simp only [MulChar.map_nonunit χ <| ZMod.eq_one_of_isUnit_natCast.mt hn, zero_mul, hn,
      ite_false]

lemma dirichletCharModOne_eq_zeta {R : Type*} [CommSemiring R] {χ : DirichletCharacter R 1} :
    (χ : ArithmeticFunction R) = ζ := by
  ext n
  have : χ = (MulChar.trivial (ZMod 1) _) := χ.level_one
  rw [χ.toArithmeticFunction_apply, this, natCoe_apply, zeta_apply, MulChar.trivial_apply]
  simp only [isUnit_of_subsingleton, ite_true, cast_ite, cast_zero, cast_one]

lemma trivialDirichletCharModOne_eq_zeta : χ₁ = (ζ : ArithmeticFunction ℂ) :=
  dirichletCharModOne_eq_zeta

lemma not_LSeriesSummable_dirichlet_at_one {N : ℕ} (hN : N ≠ 0) (χ : DirichletCharacter ℂ N) :
    ¬ LSeriesSummable χ 1 := by
  by_contra! h
  refine (Real.not_summable_indicator_one_div_nat_cast hN 1) ?_
  refine Summable.of_nonneg_of_le (fun m ↦ Set.indicator_apply_nonneg (fun _ ↦ by positivity))
    (fun n ↦ ?_) h.norm
  rw [norm_div, cpow_one, norm_nat]
  by_cases hn : n ∈ {(m : ℕ) | (m : ZMod N) = 1}
  · rw [Set.indicator_of_mem hn]
    rcases eq_or_ne n 0 with rfl | hn₀
    · simp
    gcongr
    rw [χ.toArithmeticFunction_apply_of_ne_zero hn₀, hn]
    simp only [map_one, norm_one, le_refl]
  · rw [Set.indicator_of_not_mem hn]
    positivity

lemma LSeriesSummable_dirichlet_iff {N : ℕ} (hN : N ≠ 0) (χ : DirichletCharacter ℂ N) {s : ℂ} :
    LSeriesSummable χ s ↔ 1 < s.re := by
  refine ⟨fun H ↦? _, LSeriesSummable_of_bounded_of_one_lt_re (m := 1) fun n ↦ ?_⟩
  · by_contra! h
    have h' : s.re ≤ (1 : ℂ).re := by simp only [one_re, h]
    exact not_LSeriesSummable_dirichlet_at_one hN χ <| LSeriesSummable.of_re_le_re h' H
  · rw [← norm_eq_abs]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [χ.toArithmeticFunction_apply_of_ne_zero hn]
    exact χ.norm_le_one _

lemma abscissaOfAbsConv_dirichlet {N : ℕ} (hn : N ≠ 0) (χ : DirichletCharacter ℂ N) :
    abscissaOfAbsConv χ = 1 := by
  simpa only [abscissaOfAbsConv, LSeriesSummable_dirichlet_iff hn χ, ofReal_re, Set.Ioi_def,
    EReal.image_coe_Ioi, EReal.coe_one] using csInf_Ioo <| EReal.coe_lt_top _

open EulerProduct in
/-- A variant of the Euler product for Dirichlet L-series. -/
theorem LSeries_dirichlet_eulerProduct' {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - χ p * p ^ (-s))) = L χ s := by
  rw [LSeries]
  convert exp_sum_primes_log_eq_tsum (f := dirichletSummandHom χ <| ne_zero_of_one_lt_re hs) <|
    summable_dirichletSummand χ hs with _ n -- bug: should just be `... with n`
  simp only [div_eq_mul_inv, dirichletSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, mul_eq_mul_right_iff, inv_eq_zero, cpow_eq_zero_iff, cast_eq_zero]
  -- ↑χ n = χ ↑n ∨ n = 0 ∧ s ≠ 0
  rcases eq_or_ne n 0 with rfl | hn
  · exact .inr ⟨rfl, ne_zero_of_one_lt_re hs⟩
  · exact .inl <| DirichletCharacter.toArithmeticFunction_apply_of_ne_zero χ hn

/-!
### L-series of the arithmetic function 1
-/

/-- The L-series of the arithmetic function `1` (taking the value `1` at `1` and zero else)
is the constant function `1`. -/
lemma LSeries.one : L 1 = 1 := by
  ext s
  simp only [LSeries, one_apply]
  have H (n : ℕ) : (if n = 1 then 1 / (n : ℂ) ^ s else 0) = if n = 1 then 1 else 0 :=
    ite_congr rfl (fun h ↦ by simp [h]) (fun _ ↦ rfl)
  conv => enter [1, 1, n]; simp only [apply_ite (· / (n : ℂ) ^ s), zero_div, H]
  exact tsum_ite_eq 1 1

/-!
### L-series of the Möbius function
-/

lemma not_LSeriesSummable_moebius_at_one : ¬ LSeriesSummable μ 1 := by
  by_contra! h
  refine not_summable_one_div_on_primes <| summable_ofReal.mp <| Summable.of_neg ?_
  simp only [← Pi.neg_def, indicator_ofReal, ofReal_inv, ofReal_nat_cast]
  convert h.indicator {n | n.Prime} using 1
  ext n
  by_cases hn : n ∈ {p | p.Prime}
  · simpa [Set.indicator_of_mem hn, moebius_apply_prime hn] using neg_div' (n : ℂ) 1
  · simp [Set.indicator_of_not_mem hn]

lemma moebius_LSeriesSummable_iff {s : ℂ} : LSeriesSummable μ s ↔ 1 < s.re := by
  refine ⟨fun H ↦? _, LSeriesSummable_of_bounded_of_one_lt_re (m := 1) fun n ↦ ?_⟩
  · by_contra! h
    have h' : s.re ≤ (1 : ℂ).re := by simp only [one_re, h]
    exact not_LSeriesSummable_moebius_at_one <| LSeriesSummable.of_re_le_re h' H
  · rw [intCoe_apply, ← int_cast_abs, ← Int.cast_abs]
    norm_cast
    rcases eq_or_ne (μ n) 0 with h | h
    · simp [h]
    · rcases moebius_ne_zero_iff_eq_or.mp h with h | h <;> simp [h]

lemma abscissaOfAbsConv_mu : abscissaOfAbsConv μ = 1 := by
  simpa only [abscissaOfAbsConv, moebius_LSeriesSummable_iff, ofReal_re, Set.Ioi_def,
    EReal.image_coe_Ioi, EReal.coe_one] using csInf_Ioo <| EReal.coe_lt_top _

/-!
### L-series of Dirichlet characters do not vanish on re s > 1
-/

lemma LSeriesSummable.smul {N : ℕ} (χ : DirichletCharacter ℂ N) {f : ArithmeticFunction ℂ} {s : ℂ}
    (h : LSeriesSummable f s) :
    LSeriesSummable (χ • f) s := by
  refine Summable.of_norm <| h.norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  simp only [DirichletCharacter.hsmul_arithmeticFunction_apply, norm_div, norm_mul]
  rw [← one_mul (‖_‖ / _), mul_div_assoc]
  gcongr
  exact DirichletCharacter.norm_le_one ..

open DirichletCharacter in
lemma LSeries.dirichlet_mul_mu_eq_one {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) : L χ s * L (χ • μ) s = 1 := by
  rcases eq_or_ne N 0 with rfl | hN
  · rw [dirichletCharModZero_eq_one, LSeries.one, Pi.one_apply, one_mul,
      dirichletCharModZero_hsmul ?h]
    exact congrFun LSeries.one s
    case h =>
      simp only [intCoe_apply, isUnit_one, IsUnit.squarefree, moebius_apply_of_squarefree,
        cardFactors_one, _root_.pow_zero, Int.cast_one]
  rw [← LSeries_mul ((LSeriesSummable_dirichlet_iff hN χ).mpr hs)
          <| (moebius_LSeriesSummable_iff.mpr hs).smul ..,
    ← hsmul_zeta_eq_self, ← hsmul_arithmeticFunction_mul_distrib, coe_zeta_mul_coe_moebius,
    hsmul_one]
  exact congrFun LSeries.one s

lemma LSeries.dirichlet_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    L χ s ≠ 0 :=
  fun h ↦ by simpa [h] using LSeries.dirichlet_mul_mu_eq_one χ hs

/-!
### The L-series of ζ
-/

/-- The abscissa of convergence of `ζ` is `1`. -/
lemma abscissaOfAbsConv_zeta : abscissaOfAbsConv ζ = 1 :=
  trivialDirichletCharModOne_eq_zeta ▸ abscissaOfAbsConv_dirichlet one_ne_zero χ₁

/-- The L-series of the arithmetic function `ζ` equals the Riemann Zeta Function on its
domain of convergence `1 < re s`. -/
lemma LSeries.zeta_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    L ζ s = riemannZeta s := by
  simp only [LSeries, natCoe_apply, zeta_apply, cast_ite, CharP.cast_eq_zero, cast_one]
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  refine tsum_congr fun n ↦ ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [ne_zero_of_one_lt_re hs]
  simp only [hn.ne', ite_false]

lemma LSeriesHasSum_zeta {s : ℂ} (hs : 1 < s.re) : LSeriesHasSum ζ s (riemannZeta s) :=
  LSeries.zeta_eq_riemannZeta hs ▸ (zeta_LSeriesSummable_iff_one_lt_re.mpr hs).LSeriesHasSum

open EulerProduct in
/-- A variant of the Euler product for the L-series of `ζ`. -/
theorem LSeries_zeta_eulerProduct' {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = L ζ s := by
  convert trivialDirichletCharModOne_eq_zeta ▸ LSeries_dirichlet_eulerProduct' χ₁ hs using 7
  rw [MulChar.one_apply _ <| isUnit_of_subsingleton _, one_mul]

open EulerProduct in
/-- A variant of the Euler product for the Riemann zeta function. -/
theorem _root_.riemannZeta_eulerProduct'  {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = riemannZeta s :=
  LSeries.zeta_eq_riemannZeta hs ▸ LSeries_zeta_eulerProduct' hs

-- Rename `zeta_LSeriesSummable_iff_one_lt_re` → `zeta_LSeriesSummable_iff`

lemma LSeries.zeta_mul_mu_eq_one {s : ℂ} (hs : 1 < s.re) : L ζ s * L μ s = 1 := by
  rw [← LSeries_mul (zeta_LSeriesSummable_iff_one_lt_re.mpr hs)
          (moebius_LSeriesSummable_iff.mpr hs),
    coe_zeta_mul_coe_moebius]
  exact congrFun LSeries.one s

lemma LSeries.zeta_ne_zero {s : ℂ} (hs : 1 < s.re) : L ζ s ≠ 0 :=
  fun h ↦ by simpa [h] using LSeries.zeta_mul_mu_eq_one hs

/-- The Riemann Zeta Function does not vanish on the half-plane `re s > 1`. -/
lemma _root_.riemannZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : riemannZeta s ≠ 0 :=
  LSeries.zeta_eq_riemannZeta hs ▸ LSeries.zeta_ne_zero hs

/-!
### The L-series of the von Mangoldt function
-/

/-- The L-series of the von Mangoldt function `Λ` is summable at `s` when `re s > 1`. -/
lemma LSeriesSummable_vonMangoldt {s : ℂ} (hs : 1 < s.re) : LSeriesSummable Λ s := by
  let s' : ℂ := 1 + (s.re - 1) / 2
  have Hs : s'.re ∈ Set.Ioo 1 s.re
  · simp only [add_re, one_re, div_ofNat_re, sub_re, ofReal_re, Set.mem_Ioo]
    constructor <;> linarith
  have hf := (zeta_LSeriesSummable_iff_one_lt_re.mpr Hs.1).log_pmul_of_re_lt_re Hs.2
  rw [LSeriesSummable, ← summable_norm_iff] at hf ⊢
  rw [pmul_zeta] at hf
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hf
  simp only [norm_div]
  refine div_le_div_of_le (norm_nonneg _) ?_
  simp only [realCoe_apply, norm_eq_abs, abs_ofReal, log_apply]
  rw [_root_.abs_of_nonneg vonMangoldt_nonneg, _root_.abs_of_nonneg <| Real.log_nat_cast_nonneg n]
  exact vonMangoldt_le_log

/-- The L-series of the von Mangoldt function `Λ` equals the negative logarithmic derivative
of the L-series of the arithmetic function `ζ` on its domain of convergence `1 < re s`. -/
lemma LSeries_vonMangoldt_eq {s : ℂ} (hs : 1 < s.re) :
    L Λ s = - deriv (L ζ) s / L ζ s := by
  have hs' : abscissaOfAbsConv ζ < s.re
  · rwa [abscissaOfAbsConv_zeta, ← EReal.coe_one, EReal.coe_lt_coe_iff]
  rw [eq_div_iff <| LSeries.zeta_ne_zero hs,
    ← LSeries_mul (LSeriesSummable_vonMangoldt hs) (zeta_LSeriesSummable_iff_one_lt_re.mpr hs),
    ← neg_eq_iff_eq_neg, LSeries_deriv hs']
  congr
  norm_cast
  simp only [vonMangoldt_mul_zeta, pmul_zeta]

/-- The L-series of the von Mangoldt function `Λ` equals the negative logarithmic derivative
of the Riemann zeta function on its domain of convergence `1 < re s`. -/
lemma LSeries_vonMangoldt_eq_deriv_riemannZeta_div {s : ℂ} (hs : 1 < s.re) :
    L Λ s = - deriv riemannZeta s / riemannZeta s := by
  convert LSeries_vonMangoldt_eq hs using 2
  · refine neg_inj.mpr <| Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨{z | 1 < z.re}, (isOpen_lt continuous_const continuous_re).mem_nhds hs, ?_⟩
    exact fun _ hz ↦ (LSeries.zeta_eq_riemannZeta hz).symm
  · exact (LSeries.zeta_eq_riemannZeta hs).symm

end Nat.ArithmeticFunction
