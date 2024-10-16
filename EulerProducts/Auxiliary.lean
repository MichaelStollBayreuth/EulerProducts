import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Data.Real.StarOrdered
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LSeries.Deriv

/-!
### Auxiliary lemmas
-/

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

namespace ArithmeticFunction

open Complex

open scoped ComplexOrder

/-- If all values of a `ℂ`-valued arithmetic function are nonnegative reals and `x` is a
real number in the domain of absolute convergence, then the `n`th iterated derivative
of the associated L-series is nonnegative real when `n` is even and nonpositive real
when `n` is odd. -/
lemma iteratedDeriv_LSeries_alternating (a : ArithmeticFunction ℂ)
    (hn : ∀ n, 0 ≤ a n) {x : ℝ} (h : LSeries.abscissaOfAbsConv (a ·) < x) (n : ℕ) :
    0 ≤ (-1) ^ n * iteratedDeriv n (LSeries (a ·)) x := by
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

namespace Complex

open Nat

/-- A function that is complex differentiable on the closed ball of radius `r` around `c`,
where `c` is real, and all whose iterated derivatives at `c` are real can be give by a real
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


open scoped ComplexOrder

/-- An entire function whose iterated derivatives at zero are all nonnegative real has nonnegative
real values for nonnegative real arguments. -/
theorem nonneg_of_iteratedDeriv_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : ∀ n, 0 ≤ iteratedDeriv n f 0) ⦃z : ℂ⦄ (hz : 0 ≤ z) : 0 ≤ f z := by
  have H := taylorSeries_eq_of_entire' 0 z hf
  have hz' := eq_re_of_ofReal_le hz
  rw [hz'] at hz H ⊢
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ n, 0 ≤ D n ∧ iteratedDeriv n f 0 = D n := by
    refine ⟨fun n ↦ (iteratedDeriv n f 0).re, fun n ↦ ⟨?_, ?_⟩⟩
    · have := eq_re_of_ofReal_le (h n) ▸ h n
      norm_cast at this
    · rw [eq_re_of_ofReal_le (h n)]
  simp_rw [← H, hD, ← ofReal_natCast, sub_zero, ← ofReal_pow, ← ofReal_inv, ← ofReal_mul,
    ← ofReal_tsum]
  norm_cast
  refine tsum_nonneg fun n ↦ ?_
  norm_cast at hz
  have := (hD n).1
  positivity

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
  have H := nonneg_of_iteratedDeriv_nonneg hf' hD' hx
  rw [← deriv.comp_ofReal hf.differentiableAt] at H
  change 0 ≤ deriv (f ∘ ofReal) x at H
  erw [hF, deriv.ofReal_comp] at H
  norm_cast at H

/-- An entire function whose iterated derivatives at zero are all nonnegative real (except
possibly the value itself) has values of the form `f 0 + nonneg. real` along the nonnegative
real axis. -/
theorem at_zero_le_of_iteratedDeriv_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : ∀ n ≠ 0, 0 ≤ iteratedDeriv n f 0) {z : ℂ} (hz : 0 ≤ z) : f 0 ≤ f z := by
  have h' (n : ℕ) : 0 ≤ iteratedDeriv n (f · - f 0) 0 := by
    cases n with
    | zero => simp only [iteratedDeriv_zero, sub_self, le_refl]
    | succ n =>
      specialize h n.succ <| succ_ne_zero n
      rw [iteratedDeriv_succ'] at h ⊢
      convert h using 2
      ext w
      exact deriv_sub_const (f 0)
  exact sub_nonneg.mp <| nonneg_of_iteratedDeriv_nonneg (hf.sub_const (f 0)) h' hz

/-- An entire function whose iterated derivatives at `s`` are all nonnegative real (except
possibly the value itself) has values of the form `f s + nonneg. real` along the set `s + ℝ≥0`. -/
theorem apply_le_of_iteratedDeriv_nonneg {f : ℂ → ℂ} {s : ℂ} (hf : Differentiable ℂ f)
    (h : ∀ n ≠ 0, 0 ≤ iteratedDeriv n f s) {z : ℂ} (hz : s ≤ z) : f s ≤ f z := by
  let g := fun z ↦ f (s + z)
  convert at_zero_le_of_iteratedDeriv_nonneg (f := g) ?_ (fun n hn ↦ ?_) ?_ using 1
  · simp only [add_zero, g]
  · rw [show z = s + (-s + z) by ring]
  · exact Differentiable.comp hf <| Differentiable.const_add differentiable_id s
  · simpa only [iteratedDeriv_comp_const_add, add_zero, g] using h n hn
  · exact le_neg_add_iff_le.mpr hz

/-- An entire function whose iterated derivatives at zero are all real with alternating signs
(except possibly the value itself) has values of the form `f 0 + nonneg. real` along the nonpositive
real axis. -/
theorem at_zero_le_of_iteratedDeriv_alternating {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : ∀ n ≠ 0, 0 ≤ (-1) ^ n * iteratedDeriv n f 0) {z : ℂ} (hz : z ≤ 0) : f 0 ≤ f z := by
  let F : ℂ → ℂ := fun z ↦ f (-z)
  convert at_zero_le_of_iteratedDeriv_nonneg (f := F) (hf.comp <| differentiable_neg)
    (fun n hn ↦ ?_) (neg_nonneg.mpr hz) using 1
  · simp only [F, neg_zero]
  · simp only [F, neg_neg]
  · simpa only [F, iteratedDeriv_comp_neg, neg_zero] using h n hn

/-- An entire function whose iterated derivatives at `s` are all real with alternating signs
(except possibly the value itself) has values of the form `f s + nonneg. real` along the
set `s - ℝ≥0`. -/
theorem apply_le_of_iteratedDeriv_alternating {f : ℂ → ℂ} {s : ℂ} (hf : Differentiable ℂ f)
    (h : ∀ n ≠ 0, 0 ≤ (-1) ^ n * iteratedDeriv n f s) {z : ℂ} (hz : z ≤ s) : f s ≤ f z := by
  let g := fun z ↦ f (s + z)
  convert at_zero_le_of_iteratedDeriv_alternating (f := g) ?_ (fun n hn ↦ ?_) ?_ using 1
  · simp only [add_zero, g]
  · rw [show z = s + (-s + z) by ring]
  · exact Differentiable.comp hf <| Differentiable.const_add differentiable_id s
  · simpa only [iteratedDeriv_comp_const_add, add_zero, g] using h n hn
  · exact neg_add_nonpos_iff.mpr hz

end Complex
