import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Convex.Star

namespace Complex

/-!
### Define the "slit plane" `ℂ ∖ ℝ≤0` and provide some API
-/

/-- The *slit plane* is the complex plane with the closed negative real axis removed. -/
def slitPlane : Set ℂ := {z | 0 < z.re ∨ z.im ≠ 0}

lemma mem_slitPlane_iff {z : ℂ} : z ∈ slitPlane ↔ 0 < z.re ∨ z.im ≠ 0 := Iff.rfl

lemma slitPlane_eq_union : slitPlane = {z | 0 < z.re} ∪ {z | z.im ≠ 0} := by
  ext
  simp [mem_slitPlane_iff]

/-- An alternative description of the slit plane as consisting of nonzero complex numbers
whose argument is not π. -/
lemma mem_slitPlane_iff' {z : ℂ} : z ∈ slitPlane ↔ z.arg ≠ Real.pi ∧ z ≠ 0 := by
  simp only [mem_slitPlane_iff, ne_eq, arg_eq_pi_iff, not_and]
  refine ⟨fun H ↦ ⟨fun h ↦ H.resolve_left fun h' ↦ lt_irrefl 0 <| h'.trans h, fun h ↦ ?_⟩,
          fun H ↦ ?_⟩
  · simp only [h, zero_re, lt_self_iff_false, zero_im, not_true_eq_false, or_self] at H
  · by_contra! h
    simp only [h.2, not_true_eq_false] at H
    have h₁ : z = 0 ↔ z.re = 0 ∧ z.im = 0 := ext_iff
    have h₂ : z.re ≤ 0 ↔ z.re = 0 ∨ z.re < 0 := le_iff_eq_or_lt
    tauto

lemma slitPlane_ne_zero {z : ℂ} (hz : z ∈ slitPlane) : z ≠ 0 :=
  (mem_slitPlane_iff'.mp hz).2

lemma slitPlane_arg_ne_pi {z : ℂ} (hz : z ∈ slitPlane) : z.arg ≠ Real.pi :=
  (mem_slitPlane_iff'.mp hz).1

/-- The slit plane is star-shaped with respect to the point `1`. -/
lemma slitPlane_star_shaped {z : ℂ} (hz : 1 + z ∈ slitPlane) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    1 + t * z ∈ slitPlane := by
  rw [Set.mem_Icc] at ht
  simp only [slitPlane, Set.mem_setOf_eq, add_re, one_re, add_im, one_im, zero_add, mul_re,
    ofReal_re, ofReal_im, zero_mul, sub_zero, mul_im, add_zero, mul_eq_zero] at hz ⊢
  by_contra! H
  simp only [mul_eq_zero] at H hz
  have ht₀ : t ≠ 0
  · rintro rfl
    simp only [zero_mul, add_zero, true_or, and_true] at H
    norm_num at H
  simp only [ht₀, false_or] at H
  replace hz := hz.neg_resolve_right H.2
  replace H := H.1
  have H' := mul_pos (ht.1.eq_or_lt.resolve_left ht₀.symm) hz
  nlinarith

/-- The slit plane is star-convex with respect to the point `1`. -/
lemma slitPlane_starConvex : StarConvex ℝ (1 : ℂ) slitPlane := by
  refine (starConvex_iff_forall_pos ?_).mpr fun x hx a b apos bpos hsum ↦ ?_
  · refine Or.inl <| by simp only [one_re, zero_lt_one]
  · let z := x - 1
    have hz : x = 1 + z := eq_add_of_sub_eq' rfl
    rw [hz, smul_add, ← add_assoc, ← add_smul, hsum, one_smul]
    exact slitPlane_star_shaped (hz ▸ hx) <| by constructor <;> linarith

    /-- The slit plane contains the open unit ball of radius `1` around `1`. -/
lemma mem_slitPlane_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 1 + z ∈ slitPlane := by
  simp only [slitPlane, Set.mem_setOf_eq, add_re, one_re, add_im, one_im, zero_add]
  simp only [norm_eq_abs] at hz
  by_contra! H
  linarith only [H.1, neg_lt_of_abs_lt <| (abs_re_le_abs z).trans_lt hz]

end Complex
