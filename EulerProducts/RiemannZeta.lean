import EulerProducts.EulerProduct
import Mathlib.NumberTheory.ZetaFunction

/-!
## The Euler Product for the Riemann Zeta Function
-/

-- local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

open Complex

-- should perhaps go to `Mathlib.Analysis.SpecialFunctions.Pow.Real`
lemma Nat.complex_norm_cpow_eq_rpow_re (n : ℕ) {s : ℂ} (h : s.re ≠ 0) :
    ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re := by
  rcases Nat.eq_zero_or_pos n with rfl | H
  · have hs : s ≠ 0 := fun H ↦ H ▸ h <| rfl
    simp [zero_cpow hs, Real.zero_rpow h]
  · exact abs_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr H) s

/-- The `n`th summand in the Dirichlet series giving the Riemann ζ function at `s`. -/
noncomputable
def riemannZetaSummand (s : ℂ) (n : ℕ) : ℂ := (n : ℂ) ^ (-s)

variable {s : ℂ}

/-- When `s ≠ 0`, the map `n ↦ n^(-s)` is completely multiplicative and vanishes at zero. -/
noncomputable
def riemannZetaSummandHom (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun := riemannZetaSummand s
  map_zero' := by simpa [riemannZetaSummand]
  map_one' := by simp [riemannZetaSummand]
  map_mul' m n := by
    simpa [riemannZetaSummand]
      using mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) _

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
