import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Data.Real.StarOrdered
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LSeries.Deriv

section iteratedDeriv

variable {𝕜 F} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

-- the lemmas in this section should go to Mathlib.Analysis.Calculus.Deriv.Shift
lemma iteratedDeriv_comp_const_add (n : ℕ) (f : 𝕜 → F) (s : 𝕜) :
    iteratedDeriv n (fun z ↦ f (s + z)) = fun t ↦ iteratedDeriv n f (s + t) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n IH =>
      simp only [iteratedDeriv_succ, IH]
      ext1 z
      exact deriv_comp_const_add (iteratedDeriv n f) s z

lemma iteratedDeriv_comp_add_const (n : ℕ) (f : 𝕜 → F) (s : 𝕜) :
    iteratedDeriv n (fun z ↦ f (z + s)) = fun t ↦ iteratedDeriv n f (t + s) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n IH =>
      simp only [iteratedDeriv_succ, IH]
      ext1 z
      exact deriv_comp_add_const (iteratedDeriv n f) s z

lemma iteratedDeriv_eq_on_open (n : ℕ) {f g : 𝕜 → F} {s : Set 𝕜} (hs : IsOpen s) (x : s)
    (hfg : Set.EqOn f g s) : iteratedDeriv n f x = iteratedDeriv n g x := by
  induction' n with n IH generalizing f g
  · simpa only [iteratedDeriv_zero] using hfg x.2
  · simp only [iteratedDeriv_succ']
    exact IH fun y hy ↦ Filter.EventuallyEq.deriv_eq <|
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨s, IsOpen.mem_nhds hs hy, hfg⟩

end iteratedDeriv


open Complex

open scoped ComplexOrder

namespace DifferentiableOn

/-- An function that is holomorphic on the open disk around `c` with radius `r` and whose iterated
derivatives at `c` are all nonnegative real has nonnegative real values on `c + [0,r)`. -/
theorem nonneg_of_iteratedDeriv_nonneg {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) (h : ∀ n, 0 ≤ iteratedDeriv n f c) ⦃z : ℂ⦄
    (hz₁ : c ≤ z) (hz₂ : z ∈ Metric.ball c r):
    0 ≤ f z := by
  have H := taylorSeries_eq_on_ball' hz₂ hf
  rw [← sub_nonneg] at hz₁
  have hz' : z - c = (z - c).re := eq_re_of_ofReal_le hz₁
  rw [hz'] at hz₁ H
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ n, 0 ≤ D n ∧ iteratedDeriv n f c = D n := by
    refine ⟨fun n ↦ (iteratedDeriv n f c).re, fun n ↦ ⟨?_, ?_⟩⟩
    · exact zero_le_real.mp <| eq_re_of_ofReal_le (h n) ▸ h n
    · rw [eq_re_of_ofReal_le (h n)]
  simp_rw [← H, hD, ← ofReal_natCast, ← ofReal_pow, ← ofReal_inv, ← ofReal_mul, ← ofReal_tsum]
  norm_cast
  refine tsum_nonneg fun n ↦ ?_
  norm_cast at hz₁
  have := (hD n).1
  positivity

end DifferentiableOn

namespace Differentiable

/-- An entire function whose iterated derivatives at `c` are all nonnegative real has nonnegative
real values on `c + ℝ≥0`. -/
theorem nonneg_of_iteratedDeriv_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c : ℂ} (h : ∀ n, 0 ≤ iteratedDeriv n f c) ⦃z : ℂ⦄ (hz : c ≤ z) : 0 ≤ f z := by
  refine hf.differentiableOn.nonneg_of_iteratedDeriv_nonneg
    (r := (z - c).re + 1) h hz ?_
  rw [← sub_nonneg] at hz
  have : (z - c) = (z - c).re := eq_re_of_ofReal_le hz
  simp only [Metric.mem_ball, dist_eq]
  nth_rewrite 1 [this]
  rewrite [abs_ofReal, _root_.abs_of_nonneg (nonneg_iff.mp hz).1]
  exact lt_add_one _

/-- An entire function whose iterated derivatives at `c` are all nonnegative real (except
possibly the value itself) has values of the form `f c + nonneg. real` on the set `c + ℝ≥0`. -/
theorem apply_le_of_iteratedDeriv_nonneg {f : ℂ → ℂ} {c : ℂ}
    (hf : Differentiable ℂ f) (h : ∀ n ≠ 0, 0 ≤ iteratedDeriv n f c) ⦃z : ℂ⦄ (hz : c ≤ z) :
    f c ≤ f z := by
  have h' (n : ℕ) : 0 ≤ iteratedDeriv n (f · - f c) c := by
    cases n with
    | zero => simp only [iteratedDeriv_zero, sub_self, le_refl]
    | succ n =>
      specialize h (n + 1) n.succ_ne_zero
      rw [iteratedDeriv_succ'] at h ⊢
      rwa [funext_iff.mpr <| fun x ↦ deriv_sub_const (f := f) (x := x) (f c)]
  exact sub_nonneg.mp <| nonneg_of_iteratedDeriv_nonneg (hf.sub_const _) h' hz

/-- An entire function whose iterated derivatives at `c` are all real with alternating signs
(except possibly the value itself) has values of the form `f c + nonneg. real` along the
set `c - ℝ≥0`. -/
theorem apply_le_of_iteratedDeriv_alternating {f : ℂ → ℂ} {c : ℂ}
    (hf : Differentiable ℂ f) (h : ∀ n ≠ 0, 0 ≤ (-1) ^ n * iteratedDeriv n f c) ⦃z : ℂ⦄
    (hz : z ≤ c) :
    f c ≤ f z := by
  let F : ℂ → ℂ := fun z ↦ f (-z)
  convert apply_le_of_iteratedDeriv_nonneg (f := F) (c := -c) (z := -z)
    (hf.comp <| differentiable_neg) (fun n hn ↦ ?_) (neg_le_neg_iff.mpr hz) using 1
  · simp only [neg_neg, F]
  · simp only [neg_neg, F]
  · simpa only [iteratedDeriv_comp_neg, neg_neg, smul_eq_mul, F] using h n hn

end Differentiable


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
