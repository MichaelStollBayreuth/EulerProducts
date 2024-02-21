import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
### Auxiliary lemmas
-/

namespace Real

-- This can be generalized to series of decreasing nonnegative terms
lemma not_summable_indicator_one_div_natCast {m : ℕ} (hm : m ≠ 0) (k : ZMod m) :
    ¬ Summable (Set.indicator {n : ℕ | (n : ZMod m) = k} fun n : ℕ ↦ (1 / n : ℝ)) := by
  have : NeZero m := { out := hm }
  suffices this : ¬ Summable fun n : ℕ ↦ (1 / (m * n + k.val) : ℝ) by
    set f : ℕ → ℝ := Set.indicator {n : ℕ | (n : ZMod m) = k} fun n : ℕ ↦ (1 / n : ℝ)
    contrapose! this
    let g : ℕ → ℕ := fun n ↦ m * n + k.val
    have hg : Function.Injective g := by
      intro m n hmn
      simpa [g, hm] using hmn
    have hg' : ∀ n ∉ Set.range g, f n = 0 := by
      intro n hn
      contrapose! hn
      convert Set.mem_of_indicator_ne_zero hn
      ext n
      simp only [Set.mem_range, Set.mem_setOf_eq, ZMod.nat_coe_zmod_eq_iff]
      conv => enter [1, 1, y]; rw [add_comm, eq_comm]
    convert (Function.Injective.summable_iff hg hg').mpr this with n
    simp [g]
  by_contra! h
  refine not_summable_one_div_nat_cast <| (summable_nat_add_iff 2).mp <|
    (summable_mul_left_iff (one_div_ne_zero <| Nat.cast_ne_zero.mpr hm)).mp <|
    Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) <| (summable_nat_add_iff 1).mpr h
  field_simp
  rw [← ZMod.nat_cast_val k]
  gcongr
  norm_cast
  linarith only [ZMod.val_le k]

-- generalize ℝ?
lemma summable_indicator_mod_iff {m : ℕ} (hm : m ≠ 0) (k : ZMod m) {f : ℕ → ℝ} (hf : Antitone f)
    (hf₀ : ∀ n, 0 ≤ f n) :
    Summable (Set.indicator {n : ℕ | (n : ZMod m) = k} f) ↔ Summable f := by
  refine ⟨fun H ↦ ?_, fun H ↦ Summable.indicator H _⟩

  sorry

end Real

-- not really needed here

namespace Complex

lemma summable_re {α : Type u_1} {f : α → ℂ} (h : Summable f) : Summable fun x ↦ (f x).re :=
  (Complex.hasSum_re h.hasSum).summable

lemma summable_im {α : Type u_1} {f : α → ℂ} (h : Summable f) : Summable fun x ↦ (f x).im :=
  (Complex.hasSum_im h.hasSum).summable

-- #find_home summable_re -- [Mathlib.Analysis.Complex.Basic]

end Complex


section Topology

open Filter

namespace Asymptotics

lemma isBigO_mul_iff_isBigO_div {α F : Type*} [NormedField F] {l : Filter α} {f g h : α → F}
    (hf : ∀ᶠ x in l, f x ≠ 0) :
    (fun x ↦ f x * g x) =O[l] h ↔ g =O[l] (fun x ↦ h x / f x) := by
  rw [isBigO_iff', isBigO_iff']
  refine ⟨fun ⟨c, hc, H⟩ ↦ ⟨c, hc, ?_⟩, fun ⟨c, hc, H⟩ ↦ ⟨c, hc, ?_⟩⟩ <;>
  { refine H.congr <| Eventually.mp hf <| eventually_of_forall fun x hx ↦ ?_
    rw [norm_mul, norm_div, ← mul_div_assoc, mul_comm]
    have hx' : ‖f x‖ > 0 := norm_pos_iff.mpr hx
    rw [le_div_iff hx', mul_comm] }

lemma isLittleO_id_nhdsWithin {F : Type*} [NormedField F] (s : Set F) :
    (id : F → F) =o[nhdsWithin 0 s] (fun _ ↦ (1 : F)) :=
  ((isLittleO_one_iff F).mpr tendsto_id).mono nhdsWithin_le_nhds

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
  refine Eventually.mp hf <| eventually_of_forall fun w hw ↦ le_of_lt ?_
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


namespace deriv

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open ContinuousLinearMap in
lemma comp_neg (f : 𝕜 → F) (a : 𝕜) : deriv (fun x ↦ f (-x)) a = -deriv f (-a) := by
  by_cases h : DifferentiableAt 𝕜 f (-a)
  · simp_rw [← fderiv_deriv]
    change (fderiv 𝕜 (f ∘ fun x ↦ -x) a) 1 = _
    rw [fderiv.comp _ h differentiable_neg.differentiableAt, show @Neg.neg 𝕜 _ = (- ·) from rfl,
      coe_comp', Function.comp_apply, fderiv_neg, fderiv_id', neg_apply, coe_id', id_eq, map_neg]
  · have H : ¬ DifferentiableAt 𝕜 (fun x ↦ f (-x)) a := by
      contrapose! h
      rw [← neg_neg a] at h
      convert h.comp (-a) differentiable_neg.differentiableAt
      ext
      simp only [Function.comp_apply, neg_neg]
    rw [deriv_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt H, neg_zero]

-- #find_home comp_neg -- [Mathlib.Analysis.Calculus.Deriv.Add]

/-- A variant of `deriv_const_smul` without differentiability assumption when the scalar
multiplication is by field elements. -/
lemma const_smul {f : 𝕜 → F} {x : 𝕜} {R : Type*} [Field R] [Module R F] [SMulCommClass 𝕜 R F]
    [ContinuousConstSMul R F] (c : R) :
    deriv (fun y ↦ c • f y) x = c • deriv f x := by
  by_cases hf : DifferentiableAt 𝕜 f x
  · exact deriv_const_smul c hf
  · rcases eq_or_ne c 0 with rfl | hc
    · simp only [zero_smul, deriv_const']
    · have H : ¬DifferentiableAt 𝕜 (fun y ↦ c • f y) x := by
        contrapose! hf
        change DifferentiableAt 𝕜 (fun y ↦ f y) x
        conv => enter [2, y]; rw [← inv_smul_smul₀ hc (f y)]
        exact DifferentiableAt.const_smul hf c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt H, smul_zero]

-- #find_home const_smul -- [Mathlib.Analysis.Calculus.Deriv.Mul]

end deriv


namespace iteratedDeriv

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

lemma neg (n : ℕ) (f : 𝕜 → F) (a : 𝕜) :
    iteratedDeriv n (fun x ↦ -(f x)) a = -(iteratedDeriv n f a) := by
  induction' n with n ih generalizing a
  · simp only [Nat.zero_eq, iteratedDeriv_zero]
  · have ih' : iteratedDeriv n (fun x ↦ -f x) = fun x ↦ -iteratedDeriv n f x := funext ih
    rw [iteratedDeriv_succ, iteratedDeriv_succ, ih', deriv.neg]

lemma comp_neg (n : ℕ) (f : 𝕜 → F) (a : 𝕜) :
    iteratedDeriv n (fun x ↦ f (-x)) a = (-1 : 𝕜) ^ n • iteratedDeriv n f (-a) := by
  induction' n with n ih generalizing a
  · simp only [Nat.zero_eq, iteratedDeriv_zero, pow_zero, one_smul]
  · have ih' : iteratedDeriv n (fun x ↦ f (-x)) = fun x ↦ (-1 : 𝕜) ^ n • iteratedDeriv n f (-x) :=
      funext ih
    rw [iteratedDeriv_succ, iteratedDeriv_succ, ih', pow_succ, neg_mul, one_mul,
      deriv.comp_neg (f := fun x ↦ (-1 : 𝕜) ^ n • iteratedDeriv n f x), deriv.const_smul, neg_smul]

end iteratedDeriv


namespace Complex
-- see https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Differentiability.20of.20the.20natural.20map.20.E2.84.9D.20.E2.86.92.20.E2.84.82/near/418095234

lemma hasDerivAt_ofReal (x : ℝ) : HasDerivAt ofReal' 1 x :=
  HasDerivAt.ofReal_comp <| hasDerivAt_id x

lemma deriv_ofReal (x : ℝ) : deriv ofReal' x = 1 :=
  (hasDerivAt_ofReal x).deriv

lemma differentiableAt_ofReal (x : ℝ) : DifferentiableAt ℝ ofReal' x :=
  (hasDerivAt_ofReal x).differentiableAt

lemma differentiable_ofReal : Differentiable ℝ ofReal' :=
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

/-- A function that is complex differentiable on the closed ball of radius `r` around `c`,
where `c` is real, and all whose iterated derivatives at `c` are real can be give by a real
differentiable function on the real open interval from `c-r` to `c+r`. -/
lemma realValued_of_iteratedDeriv_real_on_ball {f : ℂ → ℂ} ⦃r : ℝ⦄ {c : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (c : ℂ) r)) ⦃D : ℕ → ℝ⦄
    (hd : ∀ n, iteratedDeriv n f c = D n) :
    ∃ F : ℝ → ℝ, DifferentiableOn ℝ F (Set.Ioo (c - r) (c + r)) ∧
      Set.EqOn (f ∘ ofReal') (ofReal' ∘ F) (Set.Ioo (c - r) (c + r)) := by
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
    simp_rw [hd, ← ofReal_sub, ← ofReal_nat_cast, ← ofReal_inv, ← ofReal_pow, ← ofReal_mul,
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
    ∃ F : ℝ → ℝ, Differentiable ℝ F ∧ (f ∘ ofReal') = (ofReal' ∘ F) := by
  have H (z : ℂ) := taylorSeries_eq_of_entire' c z hf
  simp_rw [hd] at H
  refine ⟨fun x ↦ ∑' (n : ℕ), (↑n !)⁻¹ * (D n) * (x - c) ^ n, ?_, ?_⟩
  · have := hf.comp_ofReal
    simp_rw [← H, ← ofReal_sub, ← ofReal_nat_cast, ← ofReal_inv, ← ofReal_pow, ← ofReal_mul,
      ← ofReal_tsum] at this
    exact Differentiable.ofReal_comp_iff.mp this
  · ext x
    simp only [Function.comp_apply, ofReal_eq_coe, ← H, ofReal_tsum]
    push_cast
    rfl

open scoped ComplexOrder

/-- An entire function whose iterated derivatives at zero are all nonnegative real has nonnegative
real values for nonnegative real arguments. -/
theorem nonneg_of_iteratedDeriv_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : ∀ n, 0 ≤ iteratedDeriv n f 0) ⦃z : ℂ⦄ (hz : 0 ≤ z) : 0 ≤ f z := by
  have H := taylorSeries_eq_of_entire' 0 z hf
  have hz' := eq_re_of_ofReal_le hz
  rw [hz'] at hz H ⊢
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ n, 0 ≤ D n ∧ iteratedDeriv n f 0 = D n
  · refine ⟨fun n ↦ (iteratedDeriv n f 0).re, fun n ↦ ⟨?_, ?_⟩⟩
    · have := eq_re_of_ofReal_le (h n) ▸ h n
      norm_cast at this
    · rw [eq_re_of_ofReal_le (h n)]
  simp_rw [← H, hD, ← ofReal_nat_cast, sub_zero, ← ofReal_pow, ← ofReal_inv, ← ofReal_mul,
    ← ofReal_tsum]
  norm_cast
  refine tsum_nonneg fun n ↦ ?_
  norm_cast at hz
  have := (hD n).1
  positivity

/-- An entire function whose iterated derivatives at zero are all nonnegative real is
monotonic on the nonnegative real axis. -/
theorem monotoneOn_of_iteratedDeriv_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : ∀ n, 0 ≤ iteratedDeriv n f 0) : MonotoneOn (f ∘ ofReal') (Set.Ici (0 : ℝ)) := by
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
  change 0 ≤ deriv (f ∘ ofReal') x at H
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

/-- An entire function whose iterated derivatives at zero are all real with alternating signs
(except possibly the value itself) has values of the form `f 0 + nonneg. real` along the nonpositive
real axis. -/
theorem at_zero_le_of_iteratedDeriv_alternating {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : ∀ n ≠ 0, 0 ≤ (-1) ^ n * iteratedDeriv n f 0) {z : ℂ} (hz : z ≤ 0) : f 0 ≤ f z := by
  let F : ℂ → ℂ := fun z ↦ f (-z)
  convert at_zero_le_of_iteratedDeriv_nonneg (f := F) (hf.comp <| differentiable_neg)
    (fun n hn ↦ ?_) (neg_nonneg.mpr hz) using 1
  · simp only [neg_zero]
  · simp only [neg_neg]
  · simpa only [iteratedDeriv.comp_neg, neg_zero] using h n hn

end Complex
