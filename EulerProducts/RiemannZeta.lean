import EulerProducts.EulerProduct
import Mathlib.NumberTheory.ZetaFunction
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
## The Euler Product for the Riemann Zeta Function
-/

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

lemma DirichletCharacter.norm_le_one {n : ℕ} (χ : DirichletCharacter ℂ n) (m : ZMod n) :
    ‖χ m‖ ≤ 1 := by
  by_cases h : IsUnit m
  · match n with
    | 0 =>
        rcases Int.isUnit_iff.mp h with rfl | rfl
        · rw [map_one, norm_one]
        · refine (sq_le_one_iff <| norm_nonneg _).mp ?_
          rw [← norm_pow, ← map_pow, neg_one_sq, map_one, norm_one]
    | n + 1 =>
      · have H := congr_arg ((↑) : _ → ZMod n.succ) <| ZMod.pow_totient h.unit
        push_cast at H
        rw [h.unit_spec.symm]
        refine (pow_le_one_iff_of_nonneg (norm_nonneg _) (Nat.totient_pos n.succ_pos).ne').mp ?_
        rw [← norm_pow, ← map_pow, H, map_one, norm_one]
  · rw [χ.map_nonunit h, norm_zero]
    exact zero_le_one

open Complex

-- should perhaps go to `Mathlib.Analysis.SpecialFunctions.Pow.Real`
lemma Nat.complex_norm_cpow_eq_rpow_re (n : ℕ) {s : ℂ} (h : s.re ≠ 0) :
    ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re := by
  rcases n.eq_zero_or_pos with rfl | H
  · have hs : s ≠ 0 := fun H ↦ H ▸ h <| rfl
    simp [zero_cpow hs, Real.zero_rpow h]
  · exact abs_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr H) s

/-- The `n`th summand in the Dirichlet series giving the Riemann ζ function at `s`. -/
noncomputable
def riemannZetaSummand (s : ℂ) (n : ℕ) : ℂ := (n : ℂ) ^ (-s)

lemma riemannZetaSummand.mul (s : ℂ) (m n : ℕ) :
    riemannZetaSummand s (m * n) = riemannZetaSummand s m * riemannZetaSummand s n := by
  simpa [riemannZetaSummand] using mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg _

variable {s : ℂ}

/-- When `s ≠ 0`, the map `n ↦ n^(-s)` is completely multiplicative and vanishes at zero. -/
noncomputable
def riemannZetaSummandHom (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun := riemannZetaSummand s
  map_zero' := by simpa [riemannZetaSummand]
  map_one' := by simp [riemannZetaSummand]
  map_mul' := riemannZetaSummand.mul s

/-- When `χ` is a Dirichlet character and `s ≠ 0`, the map `n ↦ n^(-s)` is completely
multiplicative and vanishes at zero. -/
noncomputable
def dirichletSummandHom {n : ℕ} (χ : DirichletCharacter ℂ n) (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := χ n * riemannZetaSummand s n
  map_zero' := by simp [riemannZetaSummand, hs]
  map_one' := by simp [riemannZetaSummand]
  map_mul' m n := by
    simpa only [Nat.cast_mul, IsUnit.mul_iff, not_and, map_mul, riemannZetaSummand.mul]
      using mul_mul_mul_comm ..

lemma Complex.ne_zero_of_one_lt_re (hs : 1 < s.re) : s ≠ 0 :=
  fun h ↦ ((zero_re ▸ h ▸ hs).trans zero_lt_one).false

lemma Complex.re_neg_ne_zero_of_one_lt_re (hs : 1 < s.re) : (-s).re ≠ 0 := by
  intro h
  rw [neg_re, neg_eq_zero] at h
  exact lt_irrefl (1 : ℝ) <| (h ▸ hs).trans zero_lt_one

/-- When `s.re > 1`, the map `n ↦ n^(-s)` is norm-summable. -/
lemma summable_riemannZetaSummand (hs : 1 < s.re) :
  Summable (fun n ↦ ‖riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) n‖) := by
  simp only [riemannZetaSummandHom, riemannZetaSummand, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  convert Real.summable_nat_rpow_inv.mpr hs with n
  rw [n.complex_norm_cpow_eq_rpow_re <| Complex.re_neg_ne_zero_of_one_lt_re hs, neg_re,
    Real.rpow_neg <| Nat.cast_nonneg _]

/-- When `s.re > 1`, the map `n ↦ χ(n) * n^(-s)` is norm-summable. -/
lemma summable_dirichletSummand {N : ℕ} (χ : DirichletCharacter ℂ N) (hs : 1 < s.re) :
  Summable (fun n ↦ ‖dirichletSummandHom χ (Complex.ne_zero_of_one_lt_re hs) n‖) := by
  simp only [dirichletSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul]
  refine summable_of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_) <| summable_riemannZetaSummand hs
  · positivity
  · exact mul_le_of_le_one_left (norm_nonneg _) <| χ.norm_le_one n

open Filter Nat Topology BigOperators EulerProduct in
/-- The Euler product for the Riemann ζ function, valid for `s.re > 1`. -/
theorem riemannZeta_eulerProduct (hs : 1 < s.re) :
    Tendsto (fun n : ℕ ↦ ∏ p in primesBelow n, (1 - (p : ℂ) ^ (-s))⁻¹) atTop (𝓝 (riemannZeta s))
    := by
  have hsum := summable_riemannZetaSummand hs
  convert euler_product_multiplicative hsum
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, tsum_eq_zero_add <| summable_of_summable_norm hsum,
    map_zero, zero_add]
  simp [riemannZetaSummandHom, riemannZetaSummand, cpow_neg]

open Filter Nat Topology BigOperators EulerProduct in
/-- The Euler product for Dirichlet L-series, valid for `s.re > 1`. -/
theorem dirichletLSeries_eulerProduct {N : ℕ} (χ : DirichletCharacter ℂ N) (hs : 1 < s.re) :
    Tendsto (fun n : ℕ ↦ ∏ p in primesBelow n, (1 - χ p * (p : ℂ) ^ (-s))⁻¹) atTop
      (𝓝 (∑' n : ℕ, dirichletSummandHom χ (Complex.ne_zero_of_one_lt_re hs) n)) := by
  convert euler_product_multiplicative <| summable_dirichletSummand χ hs
