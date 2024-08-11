import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Logarithms of Euler Products

Here we consider `f : ℕ →*₀ ℂ` and the goal is to prove that
`exp (∑ p in Primes, log (1 - f p)⁻¹) = ∑ n : ℕ, f n`
under suitable conditions on `f`.
-/

-- namespace Complex

/- lemma norm_mul_natCast_cpow_le {a s : ℂ} (n : ℕ) (ha : ‖a‖ ≤ 1) (hs : 1 < s.re) :
    ‖a * n ^ (-s)‖ ≤ (n : ℝ) ^ (-s.re) := by
  rw [norm_mul, norm_natCast_cpow_of_re_ne_zero n <| by rw [neg_re]; linarith only [hs]]
  conv => enter [2]; rw [← one_mul ((n : ℝ) ^ (-s.re))]
  gcongr -/

/- lemma norm_natCast_cpow_div_one_sub_mul_cpow_le {n : ℕ} {a s : ℂ} (hn : 1 < n) (ha : ‖a‖ ≤ 1)
    (hs : 1 < s.re) :
    ‖(n : ℂ) ^ (-s) / (1 - a * n ^ (-s))‖ ≤ 2 * (n : ℝ) ^ (-s.re) := by
  have hs₀ : (-s).re ≠ 0 := by rw [neg_re]; linarith only [hs]
  have hs₁ : -s.re < 0 := by linarith only [hs]
  have hn₂ : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn
  have H : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
    rw [norm_eq_abs, ← ofReal_nat_cast, abs_cpow_eq_rpow_re_of_nonneg n.cast_nonneg hs₀, neg_re]
  have h : ‖a * n ^ (-s)‖ ≤ 1 / 2 := by
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) ha).trans ?_
    rw [H]
    refine (Real.rpow_le_rpow_of_nonpos zero_lt_two hn₂ hs₁.le).trans ?_
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two <| (neg_lt_neg hs).le
  have h' : 1 / 2 ≤ ‖1 - a * n ^ (-s)‖ := by
    suffices this : 1 ≤ 1 / 2 + ‖1 - a * n ^ (-s)‖ by linarith only [this]
    calc (1 : ℝ)
      _ = ‖(1 : ℂ)‖ := CstarRing.norm_one.symm
      _ ≤ ‖a * n ^ (-s)‖ + ‖1 - a * n ^ (-s)‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ 1 / 2 + ‖1 - a * n ^ (-s)‖ := add_le_add_right h _
  rw [norm_div, H, div_le_iff, mul_comm, ← mul_assoc]
  · refine le_mul_of_one_le_left (Real.rpow_nonneg n.cast_nonneg (-s.re)) ?_
    linarith only [h']
  · linarith only [h'] -/

open BigOperators

lemma sum_primesBelow_eq_sum_range_indicator {R : Type*} [AddCommMonoid R] (f :  ℕ → R) (n : ℕ) :
    ∑ p in n.primesBelow, f p = ∑ m in Finset.range n, Set.indicator {p : ℕ | p.Prime} f m := by
  convert (Finset.sum_indicator_subset f Finset.mem_of_mem_filter).symm using 2 with _ _ m hm
   -- `with m hm` does not work (a bug)
  simp only [Set.mem_setOf_eq, Finset.mem_range, Finset.coe_filter, not_and, Set.indicator_apply]
  split_ifs with h₁ h₂ h₃
  · rfl
  · exact (h₂ ⟨Finset.mem_range.mp hm, h₁⟩).elim
  · exact (h₁ h₃.2).elim
  · rfl

open Filter Topology

/-- If `f : ℕ → R` is summable, then the limit as `n` tends to infinity of the sum of `f p`
over the primes `p < n` is the same as the sum of `f p` over all primes. -/
lemma tendsto_sum_primesBelow_tsum {R : Type*} [AddCommGroup R] [UniformSpace R] [UniformAddGroup R]
    [CompleteSpace R] [T2Space R] {f : ℕ → R} (hsum : Summable f) :
    Tendsto (fun n : ℕ ↦ ∑ p in n.primesBelow, f p) atTop (𝓝 (∑' p : Nat.Primes, f p)) := by
  rw [(show ∑' p : Nat.Primes, f p = ∑' p : {p : ℕ | p.Prime}, f p from rfl)]
  simp_rw [tsum_subtype, sum_primesBelow_eq_sum_range_indicator]
  exact (Summable.hasSum_iff_tendsto_nat <| hsum.indicator _).mp <| (hsum.indicator _).hasSum

/-- If `f : ℕ → ℂ` is summable, then the limit as `n` tends to infinity of the product
of `exp (f p)` over the primes `p < n` is the same as the exponential of the sum of `f p`
over all primes. -/
lemma Complex.exp_tsum_primes {f : ℕ → ℂ} (hsum : Summable f) :
    Tendsto (fun n : ℕ ↦ ∏ p in n.primesBelow, exp (f p)) atTop (𝓝 (exp (∑' p : Nat.Primes, f p)))
    := by
  simpa only [← exp_sum] using Tendsto.cexp <| tendsto_sum_primesBelow_tsum hsum

open Complex

open Topology in
/-- If `f : α → ℂ` is summable, then so is `n ↦ -log (1 - f n)`. -/
lemma Summable.neg_clog_one_sub {α  : Type*} {f : α → ℂ} (hsum : Summable f) :
    Summable (fun n ↦ -log (1 - f n)) := by
  let g (z : ℂ) : ℂ := -log (1 - z)
  have hg : DifferentiableAt ℂ g 0 :=
    DifferentiableAt.neg <| ((differentiableAt_const 1).sub differentiableAt_id').clog <|
      by simp only [sub_zero, one_mem_slitPlane]
  have : g =O[𝓝 0] id := by
    simpa only [g, sub_zero, log_one, neg_zero] using DifferentiableAt.isBigO_sub hg
  exact Asymptotics.IsBigO.comp_summable this hsum

namespace EulerProduct

/-- A variant of the Euler Product formula in terms of the exponential of a sum of logarithms. -/
theorem exp_sum_primes_log_eq_tsum {f : ℕ →*₀ ℂ} (hsum : Summable (‖f ·‖)) :
    exp (∑' p : Nat.Primes, -log (1 - f p)) = ∑' n : ℕ, f n := by
  have hs {p : ℕ} (hp : 1 < p) : ‖f p‖ < 1 := hsum.of_norm.norm_lt_one (f := f.toMonoidHom) hp
  have H := Complex.exp_tsum_primes hsum.of_norm.neg_clog_one_sub
  have help (n : ℕ) : n.primesBelow.prod (fun p ↦ cexp (-log (1 - f p))) =
      n.primesBelow.prod fun p ↦ (1 - f p)⁻¹ := by
    refine Finset.prod_congr rfl (fun p hp ↦ ?_)
    rw [exp_neg, exp_log ?_]
    rw [ne_eq, sub_eq_zero, ← ne_eq]
    exact fun h ↦ (norm_one (α := ℂ) ▸ h.symm ▸ hs (Nat.prime_of_mem_primesBelow hp).one_lt).false
  simp_rw [help] at H
  exact tendsto_nhds_unique H <| eulerProduct_completely_multiplicative hsum

/-- A variant of the Euler Product formula in terms of the exponential of a sum of logarithms. -/
theorem exp_sum_primes_log_eq_tsum' {f : ℕ → ℂ} (h₀ : f 0 = 0) (h₁ : f 1 = 1)
    (hf : ∀ m n, f (m * n) = f m * f n) (hsum : Summable (‖f ·‖)) :
    exp (∑' p : Nat.Primes, -log (1 - f p)) = ∑' n : ℕ, f n :=
  exp_sum_primes_log_eq_tsum (f := {toFun := f, map_zero' := h₀, map_one' := h₁, map_mul' := hf})
    hsum

end EulerProduct
