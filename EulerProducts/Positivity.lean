import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Positivity
import Mathlib.Data.Real.StarOrdered
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LSeries.Deriv

open Complex

open scoped ComplexOrder


#exit

namespace ArithmeticFunction

open Complex

/-!
### Positivity of values on the real axis

We show that when `f` is an arithmetic function taking only nonnegative real
values such that there is an entire function `F` extending its L-series and the L-series
converges at `s : ℝ`, then `F x ≥ f 1` for all real `x`.
-/

open scoped LSeries.notation

open LSeries

open scoped ComplexOrder in
lemma LSeries_ge_of_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (h : abscissaOfAbsConv ↗f < ⊤)
    (hFf : {s | abscissaOfAbsConv f < s.re}.EqOn F (LSeries f)) (x : ℝ) :
    (f : ArithmeticFunction ℂ) 1 ≤ F x := by
  have Hgt {x : ℝ} (hx : abscissaOfAbsConv ↑f < ↑x) : (f : ArithmeticFunction ℂ) 1 ≤ F x := by
    unfold Set.EqOn at hFf
    have hx' : (x : ℂ) ∈ {s | abscissaOfAbsConv f < s.re} := by
      simp only [Set.mem_setOf_eq, ofReal_re, hx]
    have H : (f : ArithmeticFunction ℂ) 1 =
        ∑' n : ℕ,
          Set.indicator {1} (fun n ↦ (f : ArithmeticFunction ℂ) n / (n : ℂ) ^ (x : ℂ)) n := by
      simp only [toComplexArithmeticFunction_apply, coe_algebraMap]
      rw [← tsum_subtype, tsum_singleton 1 (f := fun n : ℕ ↦ (f n : ℂ) / (n : ℂ) ^ (x : ℂ)),
        Nat.cast_one, one_cpow, div_one]
    have H' (g : ℕ → ℝ) (n : ℕ) : Set.indicator ({1} : Set ℕ) (fun n ↦ ((g n) : ℂ)) n =
        ((Set.indicator ({1} : Set ℕ) g n) : ℝ) := by
      simp_rw [Set.indicator_apply]
      split_ifs <;> rfl
    rw [hFf hx', LSeries, H]
    simp_rw [← ofReal_nat_cast, ← ofReal_cpow (Nat.cast_nonneg _),
      toComplexArithmeticFunction_apply, coe_algebraMap, ← ofReal_div, H', ← ofReal_tsum]
    norm_cast
    have Hs : Summable fun n ↦ f n / ↑n ^ x := by
      have hxre : (x : ℂ).re = x := rfl
      have := LSeriesSummable_of_abscissaOfAbsConv_lt_re (hxre.symm ▸ hx)
      simpa only [LSeriesSummable, coe_algebraMap, ← ofReal_nat_cast,
        ← ofReal_cpow (Nat.cast_nonneg _), toComplexArithmeticFunction_apply, ← ofReal_div,
        summable_ofReal] using this
    refine tsum_le_tsum (fun n ↦ ?_) (Hs.indicator _) Hs
    have hnn (n : ℕ) : 0 ≤ (f n) / (n : ℝ) ^ x :=
      div_nonneg (hf n) <| Real.rpow_nonneg n.cast_nonneg x
    exact (Set.indicator_le_self' fun n _ ↦ hnn n) n
  rcases le_or_lt ↑x (abscissaOfAbsConv f) with hx | hx
  · have ⟨y, hy₁, hy₂⟩:= EReal.exists_between_coe_real h
    have hxy := EReal.coe_lt_coe_iff.mp (hx.trans_lt hy₁)
    refine (Hgt hy₁).trans ?_
    let F₁ : ℂ → ℂ := fun z ↦ F (y + z)
    convert Complex.at_zero_le_of_iteratedDeriv_alternating (f := F₁) (z := x - y)
      (hF.comp <| Differentiable.const_add differentiable_id' (y : ℂ)) (fun n hn ↦ ?_) ?_ using 1
    · simp only [add_zero]
    · simp only [add_sub_cancel'_right]
    · sorry
    · norm_cast
      exact sub_nonpos.mpr hxy.le
  · exact Hgt hx
