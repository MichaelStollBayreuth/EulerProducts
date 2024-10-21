import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Positivity
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LSeries.Deriv

/-!
### Auxiliary lemmas
-/

open Complex in
lemma continuous_cpow_natCast_neg (n : ℕ) [NeZero n] : Continuous fun s : ℂ ↦ (n : ℂ) ^ (-s) :=
  Continuous.const_cpow continuous_neg (.inl <| NeZero.ne (n : ℂ))

-- not really needed here

namespace Complex

lemma summable_re {α : Type _} {f : α → ℂ} (h : Summable f) : Summable fun x ↦ (f x).re :=
  (Complex.hasSum_re h.hasSum).summable

lemma summable_im {α : Type _} {f : α → ℂ} (h : Summable f) : Summable fun x ↦ (f x).im :=
  (Complex.hasSum_im h.hasSum).summable

-- #find_home summable_re -- [Mathlib.Analysis.Complex.Basic]

open scoped ComplexOrder

lemma inv_natCast_pow_ofReal_pos {n : ℕ} (hn : n ≠ 0) (x : ℝ) : 0 < ((n : ℂ) ^ (x : ℂ))⁻¹ := by
  refine RCLike.inv_pos_of_pos ?_
  rw [show (n : ℂ) ^ (x : ℂ) = (n : ℝ) ^ (x : ℂ) from rfl, ← ofReal_cpow n.cast_nonneg']
  positivity

end Complex

open Complex

open scoped ComplexOrder

namespace LSeries

private lemma inv_ofNat_cpow_ofReal_pos {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    0 < ((n : ℂ) ^ (x : ℂ))⁻¹ := by
  refine RCLike.inv_pos_of_pos ?_
  rw [show (n : ℂ) = (n : ℝ) from rfl, ← ofReal_cpow (n.cast_nonneg), zero_lt_real]
  positivity


lemma term_nonneg {a : ℕ → ℂ} {n : ℕ} (h : 0 ≤ a n) (x : ℝ) : 0 ≤ term a x n := by
  rw [term_def]
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [↓reduceIte, le_refl]
  · simp only [hn, ↓reduceIte]
    refine mul_nonneg h (inv_ofNat_cpow_ofReal_pos hn x).le

lemma term_pos {a : ℕ → ℂ} {n : ℕ} (hn : n ≠ 0) (h : 0 < a n) (x : ℝ) : 0 < term a x n := by
  simp only [ne_eq, hn, not_false_eq_true, term_of_ne_zero]
  refine mul_pos h <| inv_ofNat_cpow_ofReal_pos hn x

/-- If all values of a `ℂ`-valued arithmetic function are nonnegative reals and `x` is a
real number in the domain of absolute convergence, then the `n`th iterated derivative
of the associated L-series is nonnegative real when `n` is even and nonpositive real
when `n` is odd. -/
lemma iteratedDeriv_alternating {a : ℕ → ℂ} (hn : 0 ≤ a) {x : ℝ}
    (h : LSeries.abscissaOfAbsConv a < x) (n : ℕ) :
    0 ≤ (-1) ^ n * iteratedDeriv n (LSeries a) x := by
  rw [LSeries_iteratedDeriv _ h, LSeries, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨n, rfl⟩,
    one_mul]
  refine tsum_nonneg fun k ↦ ?_
  rw [LSeries.term_def]
  split
  · exact le_rfl
  · refine mul_nonneg ?_ <| (inv_natCast_pow_ofReal_pos (by assumption) x).le
    induction n with
    | zero => simp only [Function.iterate_zero, id_eq]; exact hn k
    | succ n IH =>
        rw [Function.iterate_succ_apply']
        refine mul_nonneg ?_ IH
        simp only [← natCast_log, zero_le_real, Real.log_natCast_nonneg]

/-- If all values of `a : ℕ → ℂ` are nonnegative reals and `a 1` is positive,
then `L a x` is positive real for all real `x` larger than `abscissaOfAbsConv a`. -/
lemma positive {a : ℕ → ℂ} (ha₀ : 0 ≤ a) (ha₁ : 0 < a 1) {x : ℝ} (hx : abscissaOfAbsConv a < x) :
    0 < LSeries a x := by
  rw [LSeries]
  refine tsum_pos ?_ (fun n ↦ term_nonneg (ha₀ n) x) 1 <| term_pos one_ne_zero ha₁ x
  exact LSeriesSummable_of_abscissaOfAbsConv_lt_re <| by simpa only [ofReal_re] using hx

/-- If all values of `a : ℕ → ℂ` are nonnegative reals and `a 1`
is positive, and the L-series of `a` agrees with an entire function `f` on some open
right half-plane where it converges, then `f` is real and positive on `ℝ`. -/
lemma positive_of_eq_differentiable {a : ℕ → ℂ} (ha₀ : 0 ≤ a) (ha₁ : 0 < a 1)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℝ} (hx : abscissaOfAbsConv a < x)
    (hf' : {s | x < s.re}.EqOn f (LSeries a)) (y : ℝ) :
    0 < f y := by
  have hxy : x < max x y + 1 := (le_max_left x y).trans_lt (lt_add_one _)
  have hxy' : abscissaOfAbsConv a < max x y + 1 := hx.trans <| mod_cast hxy
  have hys : (max x y + 1 : ℂ) ∈ {s | x < s.re} := by
    simp only [Set.mem_setOf_eq, add_re, ofReal_re, one_re, hxy]
  have hfx : 0 < f (max x y + 1) := by
    rw [hf' hys]
    convert positive ha₀ ha₁ hxy'
    simp only [ofReal_add, ofReal_one]
  refine (hfx.trans_le <| hf.apply_le_of_iteratedDeriv_alternating (fun n _ ↦ ?_) ?_)
  · have hs : IsOpen {s : ℂ | x < s.re} := by refine isOpen_lt ?_ ?_ <;> fun_prop
    convert iteratedDeriv_alternating ha₀ hxy' n using 2
    convert hf'.iteratedDeriv_of_isOpen hs n hys
    simp only [ofReal_add, ofReal_one]
  · exact_mod_cast (le_max_right x y).trans (lt_add_one _).le

end LSeries

namespace ArithmeticFunction

/-- If all values of a `ℂ`-valued arithmetic function are nonnegative reals and `x` is a
real number in the domain of absolute convergence, then the `n`th iterated derivative
of the associated L-series is nonnegative real when `n` is even and nonpositive real
when `n` is odd. -/
lemma iteratedDeriv_LSeries_alternating (a : ArithmeticFunction ℂ)
    (hn : ∀ n, 0 ≤ a n) {x : ℝ} (h : LSeries.abscissaOfAbsConv a < x) (n : ℕ) :
    0 ≤ (-1) ^ n * iteratedDeriv n (LSeries (a ·)) x :=
  LSeries.iteratedDeriv_alternating hn h n

/-- If all values of a `ℂ`-valued arithmetic function `a` are nonnegative reals and `a 1`
is positive, and the L-series of `a` agrees with an entire function `f` on some open
right half-plane where it converges, then `f` is real and positive on `ℝ`. -/
lemma LSeries_positive_of_eq_differentiable {a : ArithmeticFunction ℂ} (ha₀ : 0 ≤ (a ·))
    (ha₁ : 0 < a 1) {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℝ}
    (hx : LSeries.abscissaOfAbsConv a < x) (hf' : {s | x < s.re}.EqOn f (LSeries a)) (y : ℝ) :
    0 < f y :=
  LSeries.positive_of_eq_differentiable ha₀ ha₁ hf hx hf' y

end ArithmeticFunction


section Topology

open Filter

namespace Asymptotics



end Asymptotics


open Topology Asymptotics

lemma DifferentiableAt.isBigO_of_eq_zero {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z)
    (hz : f z = 0) : (fun w ↦ f (w + z)) =O[𝓝 0] id := by
  rw [← zero_add z] at hf
  simpa only [zero_add, hz, sub_zero]
    using (hf.hasDerivAt.comp_add_const 0 z).differentiableAt.isBigO_sub

lemma ContinuousAt.isBigO {f : ℂ → ℂ} {z : ℂ} (hf : ContinuousAt f z) :
    (fun w ↦ f (w + z)) =O[𝓝 0] (fun _ ↦ (1 : ℂ)) := by
  rw [isBigO_iff']
  replace hf : ContinuousAt (fun w ↦ f (w + z)) 0 := by
    convert (Homeomorph.comp_continuousAt_iff' (Homeomorph.addLeft (-z)) _ z).mp ?_
    · simp
    · simp [Function.comp_def, hf]
  simp_rw [Metric.continuousAt_iff', dist_eq_norm_sub, zero_add] at hf
  specialize hf 1 zero_lt_one
  refine ⟨‖f z‖ + 1, by positivity, ?_⟩
  refine Eventually.mp hf <| Eventually.of_forall fun w hw ↦ le_of_lt ?_
  calc ‖f (w + z)‖
    _ ≤ ‖f z‖ + ‖f (w + z) - f z‖ := norm_le_insert' ..
    _ < ‖f z‖ + 1 := add_lt_add_left hw _
    _ = _ := by simp only [norm_one, mul_one]

lemma Complex.isBigO_comp_ofReal {f g : ℂ → ℂ} {x : ℝ} (h : f =O[𝓝 (x : ℂ)] g) :
    (fun y : ℝ ↦ f y) =O[𝓝 x] (fun y : ℝ ↦ g y) :=
  Asymptotics.IsBigO.comp_tendsto (k := fun y : ℝ ↦ (y : ℂ)) h <|
    Continuous.tendsto Complex.continuous_ofReal x

lemma Complex.isBigO_comp_ofReal_nhds_ne {f g : ℂ → ℂ} {x : ℝ} (h : f =O[𝓝[≠] (x : ℂ)] g) :
    (fun y : ℝ ↦ f y) =O[𝓝[≠] x] (fun y : ℝ ↦ g y) :=
  Asymptotics.IsBigO.comp_tendsto (k := fun y : ℝ ↦ (y : ℂ)) h <|
    ((hasDerivAt_id (x : ℂ)).comp_ofReal).tendsto_punctured_nhds one_ne_zero

end Topology

namespace Complex
-- see https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Differentiability.20of.20the.20natural.20map.20.E2.84.9D.20.E2.86.92.20.E2.84.82/near/418095234

lemma hasDerivAt_ofReal (x : ℝ) : HasDerivAt ofReal 1 x :=
  HasDerivAt.ofReal_comp <| hasDerivAt_id x

lemma deriv_ofReal (x : ℝ) : deriv ofReal x = 1 :=
  (hasDerivAt_ofReal x).deriv

lemma differentiableAt_ofReal (x : ℝ) : DifferentiableAt ℝ ofReal x :=
  (hasDerivAt_ofReal x).differentiableAt

lemma differentiable_ofReal : Differentiable ℝ ofReal :=
  ofRealCLM.differentiable

-- #find_home hasDerivAt_ofReal -- [Mathlib.Analysis.SpecialFunctions.NonIntegrable]
-- Mathlib.Analysis.Complex.RealDeriv ?

end Complex

lemma DifferentiableAt.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z :=
  hf.hasDerivAt.comp_ofReal.differentiableAt

lemma deriv.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    deriv (fun x : ℝ ↦ e x) z = deriv e z :=
  hf.hasDerivAt.comp_ofReal.deriv

lemma Differentiable.comp_ofReal {e : ℂ → ℂ} (h : Differentiable ℂ e) :
    Differentiable ℝ (fun x : ℝ ↦ e x) :=
  fun _ ↦ h.differentiableAt.comp_ofReal

lemma DifferentiableAt.ofReal_comp {z : ℝ} {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z :=
  hf.hasDerivAt.ofReal_comp.differentiableAt

lemma Differentiable.ofReal_comp {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) :=
  fun _ ↦ hf.differentiableAt.ofReal_comp

open Complex ContinuousLinearMap in
lemma HasDerivAt.of_hasDerivAt_ofReal_comp {z : ℝ} {f : ℝ → ℝ} {u : ℂ}
    (hf : HasDerivAt (fun y ↦ (f y : ℂ)) u z) :
    ∃ u' : ℝ, u = u' ∧ HasDerivAt f u' z := by
  lift u to ℝ
  · have H := (imCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt.deriv
    simp only [Function.comp_def, imCLM_apply, ofReal_im, deriv_const] at H
    rwa [eq_comm, comp_apply, imCLM_apply, smulRight_apply, one_apply, one_smul] at H
  refine ⟨u, rfl, ?_⟩
  convert (reCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt
  rw [comp_apply, smulRight_apply, one_apply, one_smul, reCLM_apply, ofReal_re]

lemma DifferentiableAt.ofReal_comp_iff {z : ℝ} {f : ℝ → ℝ} :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z ↔ DifferentiableAt ℝ f z := by
  refine ⟨fun H ↦ ?_, ofReal_comp⟩
  obtain ⟨u, _, hu₂⟩ := H.hasDerivAt.of_hasDerivAt_ofReal_comp
  exact HasDerivAt.differentiableAt hu₂

lemma Differentiable.ofReal_comp_iff {f : ℝ → ℝ} :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) ↔ Differentiable ℝ f :=
  forall_congr' fun _ ↦ DifferentiableAt.ofReal_comp_iff

lemma deriv.ofReal_comp {z : ℝ} {f : ℝ → ℝ} :
    deriv (fun (y : ℝ) ↦ (f y : ℂ)) z = deriv f z := by
  by_cases hf : DifferentiableAt ℝ f z
  · exact hf.hasDerivAt.ofReal_comp.deriv
  · have hf' := mt DifferentiableAt.ofReal_comp_iff.mp hf
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hf',
      Complex.ofReal_zero]

namespace Complex

open Nat

/-- A function that is complex differentiable on the open ball of radius `r` around `c`,
where `c` is real, and all whose iterated derivatives at `c` are real can be given by a real
differentiable function on the real open interval from `c-r` to `c+r`. -/
lemma realValued_of_iteratedDeriv_real_on_ball {f : ℂ → ℂ} ⦃r : ℝ⦄ {c : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (c : ℂ) r)) ⦃D : ℕ → ℝ⦄
    (hd : ∀ n, iteratedDeriv n f c = D n) :
    ∃ F : ℝ → ℝ, DifferentiableOn ℝ F (Set.Ioo (c - r) (c + r)) ∧
      Set.EqOn (f ∘ ofReal) (ofReal ∘ F) (Set.Ioo (c - r) (c + r)) := by
  have Hz : ∀ x ∈ Set.Ioo (c - r) (c + r), (x : ℂ) ∈ Metric.ball (c : ℂ) r := by
    intro x hx
    refine Metric.mem_ball.mpr ?_
    rw [dist_eq, ← ofReal_sub, abs_ofReal, abs_sub_lt_iff, sub_lt_iff_lt_add', sub_lt_comm]
    exact and_comm.mpr hx
  have H ⦃z : ℂ⦄ (hz : z ∈ Metric.ball (c : ℂ) r) := taylorSeries_eq_on_ball' hz hf
  refine ⟨fun x ↦ ∑' (n : ℕ), (↑n !)⁻¹ * (D n) * (x - c) ^ n, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have Hx := Hz _ hx
    refine DifferentiableAt.differentiableWithinAt ?_
    replace hf := ((hf x Hx).congr (fun _ hz ↦ H hz) (H Hx)).differentiableAt
      (Metric.isOpen_ball.mem_nhds Hx) |>.comp_ofReal
    simp_rw [hd, ← ofReal_sub, ← ofReal_natCast, ← ofReal_inv, ← ofReal_pow, ← ofReal_mul,
      ← ofReal_tsum] at hf
    exact DifferentiableAt.ofReal_comp_iff.mp hf
  · simp only [Function.comp_apply, ← H (Hz _ hx), hd, ofReal_tsum]
    push_cast
    rfl

/-- A function that is complex differentiable on the complex plane and all whose iterated
derivatives at a real point `c` are real can be given by a real differentiable function
on the real line. -/
lemma realValued_of_iteratedDeriv_real {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℝ} {D : ℕ → ℝ}
    (hd : ∀ n, iteratedDeriv n f c = D n) :
    ∃ F : ℝ → ℝ, Differentiable ℝ F ∧ (f ∘ ofReal) = (ofReal ∘ F) := by
  have H (z : ℂ) := taylorSeries_eq_of_entire' c z hf
  simp_rw [hd] at H
  refine ⟨fun x ↦ ∑' (n : ℕ), (↑n !)⁻¹ * (D n) * (x - c) ^ n, ?_, ?_⟩
  · have := hf.comp_ofReal
    simp_rw [← H, ← ofReal_sub, ← ofReal_natCast, ← ofReal_inv, ← ofReal_pow, ← ofReal_mul,
      ← ofReal_tsum] at this
    exact Differentiable.ofReal_comp_iff.mp this
  · ext x
    simp only [Function.comp_apply, ← H, ofReal_tsum, ofReal_mul, ofReal_inv, ofReal_natCast,
      ofReal_pow, ofReal_sub]

end Complex

open scoped ComplexOrder

/-- An entire function whose iterated derivatives at zero are all nonnegative real is
monotonic on the nonnegative real axis. -/
theorem monotoneOn_of_iteratedDeriv_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : ∀ n, 0 ≤ iteratedDeriv n f 0) : MonotoneOn (f ∘ ofReal) (Set.Ici (0 : ℝ)) := by
  let D : ℕ → ℝ := fun n ↦ (iteratedDeriv n f 0).re
  have hD (n : ℕ) : iteratedDeriv n f 0 = D n := by
    refine Complex.ext rfl ?_
    simp only [ofReal_im]
    exact (le_def.mp (h n)).2.symm
  obtain ⟨F, hFd, hF⟩ := realValued_of_iteratedDeriv_real hf hD
  rw [hF]
  refine monotone_ofReal.comp_monotoneOn <| monotoneOn_of_deriv_nonneg (convex_Ici 0)
    hFd.continuous.continuousOn hFd.differentiableOn fun x hx ↦ ?_
  have hD' (n : ℕ) : 0 ≤ iteratedDeriv n (deriv f) 0 := by
    rw [← iteratedDeriv_succ']
    exact h (n + 1)
  have hf' := (contDiff_succ_iff_deriv.mp <| hf.contDiff (n := 2)).2.differentiable rfl.le
  have hx : (0 : ℂ) ≤ x := by
    norm_cast
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
    exact hx.le
  have H := Differentiable.nonneg_of_iteratedDeriv_nonneg hf' hD' hx
  rw [← deriv.comp_ofReal hf.differentiableAt] at H
  change 0 ≤ deriv (f ∘ ofReal) x at H
  erw [hF, deriv.ofReal_comp] at H
  norm_cast at H
