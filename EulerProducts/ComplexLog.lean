import Mathlib

/-- Translation in the domain does not change the derivative. -/
lemma HasDerivAt.comp_const_add {𝕜 : Type*} [NontriviallyNormedField 𝕜] (a x : 𝕜) {𝕜' : Type*}
    [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {h : 𝕜 → 𝕜'} {h' : 𝕜'}
    (hh : HasDerivAt h h' (a + x)) :
    HasDerivAt (fun x ↦ h (a + x)) h' x  := by
  simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hh <| hasDerivAt_id' x |>.const_add a

/-- Translation in the domain does not change the derivative. -/
lemma HasDerivAt.comp_add_const {𝕜 : Type*} [NontriviallyNormedField 𝕜] (x a : 𝕜) {𝕜' : Type*}
    [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {h : 𝕜 → 𝕜'} {h' : 𝕜'}
    (hh : HasDerivAt h h' (x + a)) :
    HasDerivAt (fun x ↦ h (x + a)) h' x  := by
  simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hh <| hasDerivAt_id' x |>.add_const a


namespace intervalIntegral

/-- A variant of the Fundamental theorem of calculus-2 involving integrating over the
unit interval. -/
lemma integral_unitInterval_eq_sub {C E : Type*} [NontriviallyNormedField C]
    [NormedAlgebra ℝ C] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace C E]
    [CompleteSpace E] [IsScalarTower ℝ C E] {f f' : C → E} {z₀ z₁ : C}
    (hcont : ContinuousOn (fun t : ℝ ↦ f' (z₀ + t • z₁)) (Set.Icc 0 1))
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' (z₀ + t • z₁)) (z₀ + t • z₁)) :
    z₁ • ∫ t in (0 : ℝ)..1, f' (z₀ + t • z₁) = f (z₀ + z₁) - f z₀ := by
  let γ (t : ℝ) : C := z₀ + t • z₁
  have hint : IntervalIntegrable (z₁ • (f' ∘ γ)) MeasureTheory.volume 0 1 :=
    (ContinuousOn.const_smul hcont z₁).intervalIntegrable_of_Icc zero_le_one
  have hderiv' : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (f ∘ γ) (z₁ • (f' ∘ γ) t) t
  · intro t ht
    refine (hderiv t <| (Set.uIcc_of_le (α := ℝ) zero_le_one).symm ▸ ht).scomp t ?_
    have : HasDerivAt (fun t : ℝ ↦ t • z₁) z₁ t
    · convert (hasDerivAt_id t).smul_const (F := C) _ using 1
      simp only [one_smul]
    exact this.const_add z₀
  convert (integral_eq_sub_of_hasDerivAt hderiv' hint) using 1
  · simp_rw [← integral_smul, Function.comp_apply]
  · simp only [Function.comp_apply, one_smul, zero_smul, add_zero]

end intervalIntegral


namespace Complex

/-!
### Define the "slit plane" `ℂ ∖ ℝ≤0` and provide some API
-/

/-- The *slit plane* is the complex plane with the closed negative real axis removed. -/
def slitPlane : Set ℂ := {z | 0 < z.re ∨ z.im ≠ 0}

lemma mem_slitPlane_iff {z : ℂ} : z ∈ slitPlane ↔ 0 < z.re ∨ z.im ≠ 0 := Iff.rfl

/-- An alternative description of the slit plane as consisting of nonzero complex numbers
whose argument is not π. -/
lemma mem_slitPlane_iff' {z : ℂ} : z ∈ slitPlane ↔ z.arg ≠ Real.pi ∧ z ≠ 0 := by
  simp only [mem_slitPlane_iff, ne_eq, arg_eq_pi_iff, not_and]
  refine ⟨fun H ↦ ⟨fun h ↦ H.resolve_left fun h' ↦ lt_irrefl 0 <| h'.trans h, fun h ↦ ?_⟩,
          fun H ↦ ?_⟩
  · simp only [h, zero_re, lt_self_iff_false, zero_im, not_true_eq_false, or_self] at H
  · by_contra' h
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
  by_contra' H
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

/-- The slit plane contains the open unit ball of radius `1` around `1`. -/
lemma mem_slitPlane_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 1 + z ∈ slitPlane := by
  simp only [slitPlane, Set.mem_setOf_eq, add_re, one_re, add_im, one_im, zero_add]
  simp only [norm_eq_abs] at hz
  by_contra' H
  linarith only [H.1, neg_lt_of_abs_lt <| (abs_re_le_abs z).trans_lt hz]

/-!
### Some missing differentiability statements on the complex log
-/

lemma hasDerivAt_log {z : ℂ} (hz : z ∈ slitPlane) : HasDerivAt log z⁻¹ z :=
  HasStrictDerivAt.hasDerivAt <| hasStrictDerivAt_log hz

lemma differentiableAt_log {z : ℂ} (hz : z ∈ slitPlane) : DifferentiableAt ℂ log z :=
  (hasDerivAt_log hz).differentiableAt

/-!
### Integral representation of the complex log
-/

lemma continousOn_one_add_mul_inv {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    ContinuousOn (fun t : ℝ ↦ (1 + t * z)⁻¹) (Set.Icc 0 1) :=
  ContinuousOn.inv₀ (Continuous.continuousOn (by continuity))
    (fun t ht ↦ slitPlane_ne_zero <| slitPlane_star_shaped hz ht)

open intervalIntegral in
/-- Represent `log (1 + z)` as an integral over the unit interval -/
lemma log_eq_integral {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    log (1 + z) = z * ∫ (t : ℝ) in (0 : ℝ)..1, (1 + t * z)⁻¹ := by
  convert (integral_unitInterval_eq_sub (continousOn_one_add_mul_inv hz)
    (fun _ ht ↦ hasDerivAt_log <| slitPlane_star_shaped hz ht)).symm using 1
  simp only [log_one, sub_zero]

/-- Represent `log (1 - z)⁻¹` as an integral over the unit interval -/
lemma log_inv_eq_integral {z : ℂ} (hz : 1 - z ∈ slitPlane) :
    log (1 - z)⁻¹ = z * ∫ (t : ℝ) in (0 : ℝ)..1, (1 - t * z)⁻¹ := by
  rw [sub_eq_add_neg 1 z] at hz ⊢
  rw [log_inv _ <| slitPlane_arg_ne_pi hz, neg_eq_iff_eq_neg, ← neg_mul]
  convert log_eq_integral hz using 5
  rw [sub_eq_add_neg, mul_neg]

/-!
### The Taylor polynomials of the logarithm
-/

open BigOperators

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

/-- The `n`th Taylor polynomial of `log` at `1`, as a function `ℂ → ℂ` -/
noncomputable
def logTaylor (n : ℕ) : ℂ → ℂ := fun z ↦ ∑ j in Finset.range n, (-1) ^ (j + 1) * z ^ j / j

lemma logTaylor_zero : logTaylor 0 = fun _ ↦ 0 := by
  funext
  simp only [logTaylor, Finset.range_zero, Nat.odd_iff_not_even, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Finset.sum_empty]

lemma logTaylor_succ (n : ℕ) :
    logTaylor (n + 1) = logTaylor n + (fun z : ℂ ↦ (-1) ^ (n + 1) * z ^ n / n) := by
  funext
  simpa only [logTaylor] using Finset.sum_range_succ ..

lemma logTaylor_at_zero (n : ℕ) : logTaylor n 0 = 0 := by
  induction n with
  | zero => simp [logTaylor_zero]
  | succ n ih => simpa [logTaylor_succ, ih] using (Nat.eq_zero_or_pos n).symm

lemma hasDerivAt_logTaylor (n : ℕ) (z : ℂ) :
    HasDerivAt (logTaylor (n + 1)) (∑ j in Finset.range n, (-1) ^ j * z ^ j) z := by
  induction n with
  | zero => simp [logTaylor_succ, logTaylor_zero, Pi.add_def, hasDerivAt_const]
  | succ n ih =>
    rw [logTaylor_succ]
    simp only [cpow_nat_cast, Nat.cast_add, Nat.cast_one, Nat.odd_iff_not_even,
      Finset.sum_range_succ, (show (-1) ^ (n + 1 + 1) = (-1) ^ n by ring)]
    refine HasDerivAt.add ih ?_
    simp only [Nat.odd_iff_not_even, Int.cast_pow, Int.cast_neg, Int.cast_one, mul_div_assoc]
    have : HasDerivAt (fun x : ℂ ↦ (x ^ (n + 1) / (n + 1))) (z ^ n) z
    · simp_rw [div_eq_mul_inv]
      convert HasDerivAt.mul_const (hasDerivAt_pow (n + 1) z) (((n : ℂ) + 1)⁻¹) using 1
      field_simp [Nat.cast_add_one_ne_zero n]
      ring
    exact HasDerivAt.const_mul _ this

/-!
### Bounds for the difference between log and its Taylor polynomials
-/

lemma hasDerivAt_log_sub_logTaylor (n : ℕ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ ↦ log (1 + z) - logTaylor (n + 1) z) ((-z) ^ n * (1 + z)⁻¹) z := by
  convert HasDerivAt.sub ((hasDerivAt_log hz).comp_const_add 1 z) (hasDerivAt_logTaylor n z) using 1
  push_cast
  have hz' : -z ≠ 1
  · intro H
    rw [neg_eq_iff_eq_neg] at H
    simp only [H, add_right_neg] at hz
    exact slitPlane_ne_zero hz rfl
  simp_rw [← mul_pow, neg_one_mul, geom_sum_eq hz', ← neg_add', div_neg, add_comm z]
  field_simp [add_comm z 1 ▸ slitPlane_ne_zero hz]

/-- Bound `‖(1 + t * z)⁻¹‖` for `0 ≤ t ≤ 1` and `‖z‖ < 1` -/
lemma norm_one_add_mul_inv_le {t : ℝ} (ht : t ∈ Set.Icc 0 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖(1 + t * z)⁻¹‖ ≤ (1 - ‖z‖)⁻¹ := by
  rw [Set.mem_Icc] at ht
  rw [norm_inv, norm_eq_abs]
  refine inv_le_inv_of_le (by linarith) ?_
  calc 1 - ‖z‖
    _ ≤ 1 - t * ‖z‖ := by
      nlinarith [norm_nonneg z]
    _ = 1 - ‖t * z‖ := by
      rw [norm_mul, norm_eq_abs (t :ℂ), abs_of_nonneg ht.1]
    _ ≤ ‖1 + t * z‖ := by
      rw [← norm_neg (t * z), ← sub_neg_eq_add]
      convert norm_sub_norm_le 1 (-(t * z))
      exact norm_one.symm

lemma integrable_pow_mul_norm_one_add_mul_inv (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
  IntervalIntegrable (fun t : ℝ ↦ t ^ n * ‖(1 + t * z)⁻¹‖) MeasureTheory.volume 0 1 := by
  have := continousOn_one_add_mul_inv <| mem_slitPlane_of_norm_lt_one hz
  rw [← Set.uIcc_of_le zero_le_one] at this
  exact ContinuousOn.intervalIntegrable <|
    Continuous.continuousOn (by continuity) |>.mul <| ContinuousOn.norm this

open intervalIntegral in
/-- The difference of `log (1+z)` and its `(n+1)`st Taylor polynomial can be bounded in
terms of `‖z‖`. -/
lemma log_sub_logTaylor_norm_le (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 + z) - logTaylor (n + 1) z‖ ≤ ‖z‖ ^ (n + 1) * (1 - ‖z‖)⁻¹ / (n + 1) := by
  have help : IntervalIntegrable (fun t : ℝ ↦ t ^ n * (1 - ‖z‖)⁻¹) MeasureTheory.volume 0 1 :=
    IntervalIntegrable.mul_const (Continuous.intervalIntegrable (by continuity) 0 1) (1 - ‖z‖)⁻¹
  let f (z : ℂ) : ℂ := log (1 + z) - logTaylor (n + 1) z
  let f' (z : ℂ) : ℂ := (-z) ^ n * (1 + z)⁻¹
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' (0 + t * z)) (0 + t * z)
  · intro t ht
    rw [zero_add]
    exact hasDerivAt_log_sub_logTaylor n <|
      slitPlane_star_shaped (mem_slitPlane_of_norm_lt_one hz) ht
  have hcont : ContinuousOn (fun t : ℝ ↦ f' (0 + t * z)) (Set.Icc 0 1)
  · simp only [zero_add, zero_le_one, not_true_eq_false]
    exact (Continuous.continuousOn (by continuity)).mul <|
      continousOn_one_add_mul_inv <| mem_slitPlane_of_norm_lt_one hz
  have H : f z = z * ∫ t in (0 : ℝ)..1, (-(t * z)) ^ n * (1 + t * z)⁻¹
  · convert (integral_unitInterval_eq_sub hcont hderiv).symm using 1
    · simp only [zero_add, add_zero, log_one, logTaylor_at_zero, sub_self, sub_zero]
    · simp only [add_zero, log_one, logTaylor_at_zero, sub_self, real_smul, zero_add, smul_eq_mul]
  simp only [H, norm_mul]
  simp_rw [neg_pow (_ * z) n, mul_assoc, intervalIntegral.integral_const_mul, mul_pow,
    mul_comm _ (z ^ n), mul_assoc, intervalIntegral.integral_const_mul, norm_mul, norm_pow,
    norm_neg, norm_one, one_pow, one_mul, ← mul_assoc, ← pow_succ, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (norm_nonneg z) (n + 1))
  calc ‖∫ t in (0 : ℝ)..1, (t : ℂ) ^ n * (1 + t * z)⁻¹‖
    _ ≤ ∫ t in (0 : ℝ)..1, ‖(t : ℂ) ^ n * (1 + t * z)⁻¹‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ = ∫ t in (0 : ℝ)..1, t ^ n * ‖(1 + t * z)⁻¹‖ := by
        refine intervalIntegral.integral_congr <| fun t ht ↦ ?_
        rw [Set.uIcc_of_le zero_le_one, Set.mem_Icc] at ht
        simp_rw [norm_mul, norm_pow, norm_eq_abs, abs_of_nonneg ht.1]
    _ ≤ ∫ t in (0 : ℝ)..1, t ^ n * (1 - ‖z‖)⁻¹ :=
        intervalIntegral.integral_mono_on zero_le_one
          (integrable_pow_mul_norm_one_add_mul_inv n hz) help <|
          fun t ht ↦ mul_le_mul_of_nonneg_left (norm_one_add_mul_inv_le ht hz)
                       (pow_nonneg ((Set.mem_Icc.mp ht).1) _)
    _ = (1 - ‖z‖)⁻¹ / (n + 1) := by
        rw [intervalIntegral.integral_mul_const, mul_comm, integral_pow]
        field_simp

lemma norm_log_sub_self_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 + z) - z‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
  convert log_sub_logTaylor_norm_le 1 hz using 2
  · simp [logTaylor_succ, logTaylor_zero, sub_eq_add_neg]
  · norm_num

lemma log_inv_add_logTaylor_neg_norm_le (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 - z)⁻¹ + logTaylor (n + 1) (-z)‖ ≤ ‖z‖ ^ (n + 1) * (1 - ‖z‖)⁻¹ / (n + 1) := by
  rw [sub_eq_add_neg,
    log_inv _ <| slitPlane_arg_ne_pi <| mem_slitPlane_of_norm_lt_one <| (norm_neg z).symm ▸ hz,
    ← sub_neg_eq_add, ← neg_sub', norm_neg]
  convert log_sub_logTaylor_norm_le n <| (norm_neg z).symm ▸ hz using 4 <;> rw [norm_neg]

lemma norm_log_inv_sub_self_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 - z)⁻¹ - z‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
  convert log_inv_add_logTaylor_neg_norm_le 1 hz using 2
  · simp [logTaylor_succ, logTaylor_zero, sub_eq_add_neg]
  · norm_num

end Complex
