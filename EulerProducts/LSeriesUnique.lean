import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Linearity

open LSeries Complex

lemma Complex.cpow_natCast_add_one_ne_zero (n : ℕ) (z : ℂ) : (n + 1 : ℂ) ^ z ≠ 0 :=
  mt (cpow_eq_zero_iff ..).mp fun H ↦ by norm_cast at H; exact H.1

-- TODO: change argument order in `LSeries_congr` to have `s` last.

/-- If `F` is a binary operation on `ℕ → ℂ` with the property that the `LSeries` of `F f g`
converges whenever the `LSeries` of `f` and `g` do, then the abscissa of absolute convergence
of `F f g` is at most the maximum of the abscissa of absolute convergence of `f` and that of `g`. -/
lemma LSeries.abscissaOfAbsConv_binop_le {F : (ℕ → ℂ) → (ℕ → ℂ) → (ℕ → ℂ)}
    (hF : ∀ {f g s}, LSeriesSummable f s → LSeriesSummable g s → LSeriesSummable (F f g) s)
    (f g : ℕ → ℂ) :
    abscissaOfAbsConv (F f g) ≤ max (abscissaOfAbsConv f) (abscissaOfAbsConv g) := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun x hx ↦  hF ?_ ?_
  · exact LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      (ofReal_re x).symm ▸ (le_max_left ..).trans_lt hx
  · exact LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
        (ofReal_re x).symm ▸ (le_max_right ..).trans_lt hx

/-- The abscissa of absolute convergence of `f + g` is at most the maximum of those
of `f` and `g`. -/
lemma LSeries.abscissaOfAbsConv_add_le (f g : ℕ → ℂ) :
    abscissaOfAbsConv (f + g) ≤ max (abscissaOfAbsConv f) (abscissaOfAbsConv g) :=
  abscissaOfAbsConv_binop_le LSeriesSummable.add f g

/-- The abscissa of absolute convergence of `f - g` is at most the maximum of those
of `f` and `g`. -/
lemma LSeries.abscissaOfAbsConv_sub_le (f g : ℕ → ℂ) :
    abscissaOfAbsConv (f - g) ≤ max (abscissaOfAbsConv f) (abscissaOfAbsConv g) :=
  abscissaOfAbsConv_binop_le LSeriesSummable.sub f g

private
lemma foo (m n : ℕ) (z : ℂ) (x : ℝ) :
    (n + 1) ^ (x : ℂ) * (z / m ^ (x : ℂ)) = z / (m / (n + 1)) ^ (x : ℂ) := by
  have Hm : (0 : ℝ) ≤ m := m.cast_nonneg
  have Hn : (0 : ℝ) ≤ (n + 1 : ℝ)⁻¹ := by positivity
  rw [← mul_div_assoc, mul_comm, div_eq_mul_inv z, mul_div_assoc]
  congr
  simp_rw [div_eq_mul_inv]
  rw [show (n + 1 : ℂ)⁻¹ = (n + 1 : ℝ)⁻¹ by
        simp only [ofReal_inv, ofReal_add, ofReal_natCast, ofReal_one],
    show (n + 1 : ℂ) = (n + 1 : ℝ) by norm_cast, show (m : ℂ) = (m : ℝ) by norm_cast,
    mul_cpow_ofReal_nonneg Hm Hn, mul_inv, mul_comm]
  congr
  rw [← cpow_neg, show (-x : ℂ) = (-1 : ℝ) * x by simp only [ofReal_neg, ofReal_one,
    neg_mul, one_mul], cpow_mul_ofReal_nonneg Hn, Real.rpow_neg_one, inv_inv]

lemma LSeries.pow_mul_term_eq (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    (n + 1) ^ s * term f s (n + 1) = f (n + 1) := by
  simp only [term, add_eq_zero, one_ne_zero, and_false, ↓reduceIte, Nat.cast_add, Nat.cast_one,
    mul_div_assoc', ne_eq, cpow_natCast_add_one_ne_zero n _, not_false_eq_true, div_eq_iff,
    mul_comm (f _)]

open Filter Real in
/-- If the coefficients `f m` of an L-series are zero for `m ≤ n` and the L-series converges
at some point, then `f (n+1)` is the limit of `(n+1)^x * LSeries f x` as `x → ∞`. -/
lemma LSeries.tendsto_pow_mul_atTop {f : ℕ → ℂ} {n : ℕ} (h : ∀ m ≤ n, f m = 0)
    (ha : abscissaOfAbsConv f < ⊤):
    Tendsto (fun x : ℝ ↦ ((n + 1) ^ (x : ℂ)) * LSeries f x) atTop (nhds (f (n + 1))) := by
  obtain ⟨y, hay, hyt⟩ := exists_between ha
  lift y to ℝ using ⟨hyt.ne, ((OrderBot.bot_le _).trans_lt hay).ne'⟩
  -- `F x m` is the `m`th term of `(n+1)^x * LSeries f x`, except that `F x (n+1) = 0`
  let F := fun (x : ℝ) ↦ {m | n + 1 < m}.indicator (fun m ↦ f m / (m / (n + 1) : ℂ) ^ (x : ℂ))
  have hF₀ (x : ℝ) {m : ℕ} (hm : m ≤ n + 1) : F x m = 0 := by
    simp only [Set.mem_setOf_eq, not_lt_of_le hm, not_false_eq_true, Set.indicator_of_not_mem, F]
  have hF (x : ℝ) {m : ℕ} (hm : m ≠ n + 1) : F x m = ((n + 1) ^ (x : ℂ)) * term f x m := by
    rcases lt_trichotomy m (n + 1) with H | rfl | H
    · simp only [Set.mem_setOf_eq, Nat.not_lt_of_gt H, not_false_eq_true, Set.indicator_of_not_mem,
        term, h m <| Nat.lt_succ_iff.mp H, zero_div, ite_self, mul_zero, F]
    · exact (hm rfl).elim
    · simp only [Set.mem_setOf_eq, H, Set.indicator_of_mem, term, (n.zero_lt_succ.trans H).ne',
        ↓reduceIte, foo, F]
  have hs {x : ℝ} (hx : x ≥ y) : Summable fun m ↦ (n + 1) ^ (x : ℂ) * term f x m := by
    refine (summable_mul_left_iff <| cpow_natCast_add_one_ne_zero n _).mpr <|
       LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
    simpa only [ofReal_re] using hay.trans_le <| EReal.coe_le_coe_iff.mpr hx
  -- we can write `(n+1)^x * LSeries f x` as `f (n+1)` plus the series over `F x`
  have key : ∀ x ≥ y, (n + 1) ^ (x : ℂ) * LSeries f x = f (n + 1) + ∑' m : ℕ, F x m := by
    intro x hx
    rw [LSeries, ← tsum_mul_left, tsum_eq_add_tsum_ite (hs hx) (n + 1)]
    congr
    · exact pow_mul_term_eq f x n
    · ext m
      rcases eq_or_ne m (n + 1) with rfl | hm
      · simp only [↓reduceIte, hF₀ x le_rfl]
      · simp only [hm, ↓reduceIte, ne_eq, not_false_eq_true, hF]
  -- reduce to showing that `∑' m, F x m → 0` as `x → ∞`
  conv => enter [3, 1]; rw [← add_zero (f _)]
  refine Tendsto.congr'
    (eventuallyEq_of_mem (s := {x | y ≤ x}) (mem_atTop y) key).symm <| tendsto_const_nhds.add ?_
  -- get the prerequisites for applying dominated convergence
  have hys : Summable (F y) := by
    refine ((hs le_rfl).indicator {m | n + 1 < m}).congr fun m ↦ ?_
    by_cases hm : n + 1 < m
    · simp only [Set.mem_setOf_eq, hm, Set.indicator_of_mem, ne_eq, hm.ne', not_false_eq_true, hF]
    · simp only [Set.mem_setOf_eq, hm, not_false_eq_true, Set.indicator_of_not_mem,
        hF₀ _ (le_of_not_lt hm)]
  have hc (k : ℕ) : Tendsto (F · k) atTop (nhds 0) := by
    rcases lt_or_le (n + 1) k with H | H
    · have H₀ : (0 : ℝ) ≤ k / (n + 1) := by positivity
      have H₀' : (0 : ℝ) ≤ (n + 1) / k := by positivity
      have H₁ : (k / (n + 1) : ℂ) = (k / (n + 1) : ℝ) := by
        simp only [ofReal_div, ofReal_natCast, ofReal_add, ofReal_one]
      have H₂ : (n + 1) / k < (1 : ℝ) :=
        (div_lt_one <| by exact_mod_cast n.succ_pos.trans H).mpr <| by exact_mod_cast H
      simp only [Set.mem_setOf_eq, H, Set.indicator_of_mem, F]
      conv =>
        enter [1, x]
        rw [div_eq_mul_inv, H₁, ← ofReal_cpow H₀, ← ofReal_inv, ← Real.inv_rpow H₀, inv_div]
      conv => enter [3, 1]; rw [← mul_zero (f k)]
      exact
        (tendsto_rpow_atTop_of_base_lt_one _ (neg_one_lt_zero.trans_le H₀') H₂).ofReal.const_mul _
    · simp only [hF₀ _ H, tendsto_const_nhds_iff]
  rw [show (0 : ℂ) = tsum (fun _ : ℕ ↦ 0) from tsum_zero.symm]
  refine tendsto_tsum_of_dominated_convergence hys.norm hc <| eventually_iff.mpr ?_
  filter_upwards [mem_atTop y] with y' hy' k
  -- it remains to show that `‖F y' k‖ ≤ ‖F y k‖` (for `y' ≥ y`)
  rcases lt_or_le (n + 1) k with H | H
  · simp only [Set.mem_setOf_eq, H, Set.indicator_of_mem, norm_div, Complex.norm_eq_abs,
      abs_cpow_real, map_div₀, abs_natCast, F]
    rw [← Nat.cast_one, ← Nat.cast_add, abs_natCast]
    have hkn : 1 ≤ (k / (n + 1 :) : ℝ) :=
      (one_le_div (by positivity)).mpr <| by norm_cast; exact Nat.le_of_succ_le H
    exact div_le_div_of_nonneg_left (Complex.abs.nonneg _)
      (rpow_pos_of_pos (zero_lt_one.trans_le hkn) _) <| rpow_le_rpow_of_exponent_le hkn hy'
  · simp only [hF₀ _ H, norm_zero, le_refl]

open Filter in
/-- If the L-series of `f` converges at some point, then `f 1` is the limit of `LSeries f x`
as `x → ∞`. -/
lemma LSeries.tendsto_atTop {f : ℕ → ℂ} (ha : abscissaOfAbsConv f < ⊤):
    Tendsto (fun x : ℝ ↦ LSeries f x) atTop (nhds (f 1)) := by
  let F (n : ℕ) : ℂ := if n = 0 then 0 else f n
  have hF₀ : F 0 = 0 := rfl
  have hF {n : ℕ} (hn : n ≠ 0) : F n = f n := by simp only [hn, ↓reduceIte, F]
  have ha' : abscissaOfAbsConv F < ⊤ := (abscissaOfAbsConv_congr hF).symm ▸ ha
  simp_rw [← LSeries_congr _ hF]
  convert LSeries.tendsto_pow_mul_atTop (n := 0) (fun _ hm ↦ Nat.le_zero.mp hm ▸ hF₀) ha' using 1
  simp only [Nat.cast_zero, zero_add, one_cpow, one_mul]

lemma LSeries_eq_zero_of_abscissaOfAbsConv_eq_top {f : ℕ → ℂ} (h : abscissaOfAbsConv f = ⊤) :
    LSeries f = 0 := by
  ext s
  exact LSeries.eq_zero_of_not_LSeriesSummable f s <| mt LSeriesSummable.abscissaOfAbsConv_le <|
    h ▸ fun H ↦ (H.trans_lt <| EReal.coe_lt_top _).false

open Filter Nat in
/-- The `LSeries` of `f` is zero for large real arguments if and only if either `f n = 0`
for all `n ≠ 0` or the L-series converges nowhere. -/
lemma LSeries_eventually_eq_zero_iff' {f : ℕ → ℂ} :
    (fun x : ℝ ↦ LSeries f x) =ᶠ[atTop] 0 ↔ (∀ n ≠ 0, f n = 0) ∨ abscissaOfAbsConv f = ⊤ := by
  by_cases h : abscissaOfAbsConv f = ⊤ <;> simp only [h, or_true, or_false, iff_true]
  · refine Eventually.of_forall ?_
    simp only [LSeries_eq_zero_of_abscissaOfAbsConv_eq_top h, Pi.zero_apply, forall_const]
  · refine ⟨fun H ↦ ?_, fun H ↦ Eventually.of_forall fun x ↦ ?_⟩
    · let F (n : ℕ) : ℂ := if n = 0 then 0 else f n
      have hF₀ : F 0 = 0 := rfl
      have hF {n : ℕ} (hn : n ≠ 0) : F n = f n := by simp only [hn, ↓reduceIte, F]
      suffices ∀ n, F n = 0 by
        peel hF with n hn h
        exact (this n ▸ h).symm
      have ha : ¬ abscissaOfAbsConv F = ⊤ := abscissaOfAbsConv_congr hF ▸ h
      have h' (x : ℝ) : LSeries F x = LSeries f x := LSeries_congr x hF
      have H' (n : ℕ) : (fun x : ℝ ↦ (n ^ (x : ℂ)) * LSeries F x) =ᶠ[atTop] (fun _ ↦ 0) := by
        simp only [h']
        rw [eventuallyEq_iff_exists_mem] at H ⊢
        peel H with s hs
        refine ⟨hs.1, fun x hx ↦ ?_⟩
        simp only [hs.2 hx, Pi.zero_apply, mul_zero]
      intro n
      induction' n using Nat.strongRecOn with n ih
      -- it suffices to show that `n ^ x * LSeries F x` tends to `F n` as `x` tends to `∞`
      suffices Tendsto (fun x : ℝ ↦ (n ^ (x : ℂ)) * LSeries F x) atTop (nhds (F n)) by
        replace this := this.congr' <| H' n
        simp only [tendsto_const_nhds_iff] at this
        exact this.symm
      cases n with
      | zero =>
          refine Tendsto.congr' (H' 0).symm ?_
          simp only [zero_eq, hF₀, tendsto_const_nhds_iff]
      | succ n =>
          simp only [succ_eq_add_one, cast_add, cast_one]
          exact LSeries.tendsto_pow_mul_atTop (fun m hm ↦ ih m <| lt_succ_of_le hm) <| Ne.lt_top ha
    · simp only [LSeries_congr x fun {n} ↦ H n, show (fun _ : ℕ ↦ (0 : ℂ)) = 0 from rfl,
        LSeries_zero, Pi.zero_apply]

open Nat in
/-- Assuming `f 0 = 0`, the `LSeries` of `f` is zero if and only if either `f = 0` or the
L-series converges nowhere. -/
lemma LSeries_eq_zero_iff {f : ℕ → ℂ} (hf : f 0 = 0) :
    LSeries f = 0 ↔ f = 0 ∨ abscissaOfAbsConv f = ⊤ := by
  by_cases h : abscissaOfAbsConv f = ⊤ <;> simp only [h, or_true, or_false, iff_true]
  · exact LSeries_eq_zero_of_abscissaOfAbsConv_eq_top h
  · refine ⟨fun H ↦ ?_, fun H ↦ H ▸ LSeries_zero⟩
    convert (LSeries_eventually_eq_zero_iff'.mp ?_).resolve_right h
    · refine ⟨fun H' _ _ ↦ by rw [H', Pi.zero_apply], fun H' ↦ ?_⟩
      ext ⟨- | m⟩ -- the introduced variable in the second case is still `n✝` ?
      · simp only [zero_eq, hf, Pi.zero_apply]
      · simp only [ne_eq, succ_ne_zero, not_false_eq_true, H', Pi.zero_apply]
    · simp only [H, Pi.zero_apply]
      exact Filter.EventuallyEq.rfl

open Filter in
/-- If the `LSeries` of `f` and of `g` converge somewhere and agree on large real arguments,
then the L-series of `f - g` is zero for large real arguments. -/
lemma LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq {f g : ℕ → ℂ}
    (hf : abscissaOfAbsConv f < ⊤) (hg : abscissaOfAbsConv g < ⊤)
    (h : (fun x : ℝ ↦ LSeries f x) =ᶠ[atTop] fun x ↦ LSeries g x) :
    (fun x : ℝ ↦ LSeries (f - g) x) =ᶠ[atTop] (0 : ℝ → ℂ) := by
  rw [EventuallyEq, eventually_atTop] at h ⊢
  obtain ⟨x₀, hx₀⟩ := h
  obtain ⟨yf, hyf₁, hyf₂⟩ := exists_between hf
  obtain ⟨yg, hyg₁, hyg₂⟩ := exists_between hg
  lift yf to ℝ using ⟨hyf₂.ne, ((OrderBot.bot_le _).trans_lt hyf₁).ne'⟩
  lift yg to ℝ using ⟨hyg₂.ne, ((OrderBot.bot_le _).trans_lt hyg₁).ne'⟩
  refine ⟨max x₀ (max yf yg), fun x hx ↦ ?_⟩
  have Hf : LSeriesSummable f x := by
    refine LSeriesSummable_of_abscissaOfAbsConv_lt_re <| (ofReal_re x).symm ▸ hyf₁.trans_le ?_
    refine (le_max_left _ (yg : EReal)).trans <| (le_max_right (x₀ : EReal) _).trans ?_
    simpa only [max_le_iff, EReal.coe_le_coe_iff] using hx
  have Hg : LSeriesSummable g x := by
    refine LSeriesSummable_of_abscissaOfAbsConv_lt_re <| (ofReal_re x).symm ▸ hyg₁.trans_le ?_
    refine (le_max_right (yf : EReal) _).trans <| (le_max_right (x₀ : EReal) _).trans ?_
    simpa only [max_le_iff, EReal.coe_le_coe_iff] using hx
  rw [LSeries_sub Hf Hg, hx₀ x <| (le_max_left ..).trans hx, sub_self, Pi.zero_apply]

open Filter in
/-- If the `LSeries` of `f` and of `g` converge somewhere and agree on large real arguments,
then `f n = g n` whenever `n ≠ 0`. -/
lemma LSeries.eq_of_LSeries_eventually_eq {f g : ℕ → ℂ} (hf : abscissaOfAbsConv f < ⊤)
    (hg : abscissaOfAbsConv g < ⊤) (h : (fun x : ℝ ↦ LSeries f x) =ᶠ[atTop] fun x ↦ LSeries g x)
    {n : ℕ} (hn : n ≠ 0) :
    f n = g n := by
  have hsub : (fun x : ℝ ↦ LSeries (f - g) x) =ᶠ[atTop] (0 : ℝ → ℂ) :=
    LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq hf hg h
  have ha : abscissaOfAbsConv (f - g) ≠ ⊤ :=
    lt_top_iff_ne_top.mp <| (abscissaOfAbsConv_sub_le f g).trans_lt <| max_lt hf hg
  simpa only [Pi.sub_apply, sub_eq_zero]
    using (LSeries_eventually_eq_zero_iff'.mp hsub).resolve_right ha n hn

/-- If the `LSeries` of `f` and of `g` both converge somewhere, then they are equal if and only
if `f n = g n` whenever `n ≠ 0`. -/
lemma LSeries_eq_iff_of_abscissaOfAbsConv_lt_top {f g : ℕ → ℂ} (hf : abscissaOfAbsConv f < ⊤)
    (hg : abscissaOfAbsConv g < ⊤) :
    LSeries f = LSeries g ↔ ∀ n ≠ 0, f n = g n := by
  refine ⟨fun H n hn ↦ ?_, fun H ↦ funext (LSeries_congr · fun {n} ↦ H n)⟩
  refine eq_of_LSeries_eventually_eq hf hg ?_ hn
  exact Filter.Eventually.of_forall fun x ↦ congr_fun H x
