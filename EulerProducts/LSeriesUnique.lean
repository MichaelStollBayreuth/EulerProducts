import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.Normed.Group.Tannery

open LSeries Complex

lemma LSeries_zero : LSeries 0 = 0 := by
  ext
  simp only [LSeries, term, Pi.zero_apply, zero_div, ite_self, tsum_zero]

private
lemma foo (m n : ℕ) (z : ℂ) (x : ℝ) :
    (n + 1) ^ (x : ℂ) * (z / m ^ (x : ℂ)) = z / (m / (n + 1)) ^ (x : ℂ) := by
  have Hm : (0 : ℝ) ≤ m := m.cast_nonneg
  have Hn : (0 : ℝ) ≤ (n + 1 : ℝ)⁻¹ := by positivity
  rw [← mul_div_assoc, mul_comm, div_eq_mul_inv z, mul_div_assoc]
  congr
  simp_rw [div_eq_mul_inv]
  rw [show (n + 1 : ℂ)⁻¹ = (n + 1 : ℝ)⁻¹ by
        simp only [ofReal_inv, ofReal_add, ofReal_nat_cast, ofReal_one],
    show (n + 1 : ℂ) = (n + 1 : ℝ) by norm_cast, show (m : ℂ) = (m : ℝ) by norm_cast,
    mul_cpow_ofReal_nonneg Hm Hn, mul_inv, mul_comm]
  congr
  rw [← cpow_neg, show (-x : ℂ) = (-1 : ℝ) * x by simp only [ofReal_neg, ofReal_one,
    neg_mul, one_mul], cpow_mul_ofReal_nonneg Hn, Real.rpow_neg_one, inv_inv]

lemma Complex.cpow_natCast_succ_ne_zero (n : ℕ) (z : ℂ) : (n + 1 : ℂ) ^ z ≠ 0 :=
  mt (cpow_eq_zero_iff ..).mp fun H ↦ by norm_cast at H; exact Nat.succ_ne_zero n H.1

open Filter in
/-- If the coefficients `f m` of an L-series are zero for `m ≤ n` and the L-series converges
at some point, then `f (n+1)` is the limit of `(n+1)^x * LSeries f x` as `x → ∞`. -/
lemma LSeries_limit {f : ℕ → ℂ} {n : ℕ} (h : ∀ m ≤ n, f m = 0) (ha : abscissaOfAbsConv f < ⊤):
    Tendsto (fun x : ℝ ↦ ((n + 1) ^ (x : ℂ)) * LSeries f x) atTop (nhds (f (n + 1))) := by
  obtain ⟨y, hay, hyt⟩ := exists_between ha
  lift y to ℝ using ⟨hyt.ne, ((OrderBot.bot_le _).trans_lt hay).ne'⟩
  -- `F x m` is the `m`th term of `(n+1)^x * LSeries f x`, except that `F x (n+1) = 0`
  let F := fun (x : ℝ) ↦ Set.indicator {m | n + 1 < m} (fun m ↦ f m / (m / (n + 1) : ℂ) ^ (x : ℂ))
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
    refine (summable_mul_left_iff <| cpow_natCast_succ_ne_zero n _).mpr <|
       LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
    simpa only [ofReal_re] using hay.trans_le <| EReal.coe_le_coe_iff.mpr hx
  -- we can write `(n+1)^x * LSeries f x` as `f (n+1)` plus the series over `F x`
  have key : ∀ x ≥ y, (n + 1) ^ (x : ℂ) * LSeries f x = f (n + 1) + ∑' m : ℕ, F x m := by
    intro x hx
    rw [LSeries, ← tsum_mul_left, tsum_eq_add_tsum_ite (hs hx) (n + 1)]
    congr
    · field_simp [term, mul_comm (f _), cpow_natCast_succ_ne_zero n _]
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
        simp only [ofReal_div, ofReal_nat_cast, ofReal_add, ofReal_one]
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
  rw [show (0 : ℂ) = tsum (fun _ : ℕ ↦ 0) by simp]
  refine tendsto_tsum_of_dominated_convergence hys.norm hc <| eventually_iff.mpr ?_
  filter_upwards [mem_atTop y] with y' hy' k
  -- it remains to show that `‖F y' k‖ ≤ ‖F y k‖` (for `y' ≥ y`)
  rcases lt_or_le (n + 1) k with H | H
  · simp only [Set.mem_setOf_eq, H, Set.indicator_of_mem, norm_div, norm_eq_abs,
      abs_cpow_real, map_div₀, abs_natCast, F]
    rw [← Nat.cast_one, ← Nat.cast_add, abs_natCast]
    have hkn : 1 ≤ (k / (n + 1 :) : ℝ) :=
      (one_le_div (by positivity)).mpr <| by norm_cast; exact Nat.le_of_succ_le H
    refine div_le_div_of_nonneg_left (Complex.abs.nonneg _)
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le hkn) _) ?_
    exact Real.rpow_le_rpow_of_exponent_le hkn hy'
  · simp only [hF₀ _ H, norm_zero, le_refl]

/-- The `LSeries` of `f` is zero if and only if either `f = 0`
or the L-series converges nowhere. -/
lemma LSeries_eq_zero_iff {f : ℕ → ℂ} (hf : f 0 = 0) :
    LSeries f = 0 ↔ f = 0 ∨ abscissaOfAbsConv f = ⊤ := by
  by_cases h : abscissaOfAbsConv f = ⊤ <;> simp only [h, or_true, or_false, iff_true]
  · ext s
    exact LSeries.eq_zero_of_not_LSeriesSummable f s <| mt LSeriesSummable.abscissaOfAbsConv_le <|
      h ▸ fun H ↦ (H.trans_lt <| EReal.coe_lt_top _).false
  · refine ⟨fun H ↦ ?_, fun H ↦ H ▸ LSeries_zero⟩
    ext n
    induction' n using Nat.strongInductionOn with n ih
    -- it suffices to show that `n ^ x * LSeries f x` tends to `f n` as `x` tends to `∞`
    suffices Filter.Tendsto (fun x : ℝ ↦ (n ^ (x : ℂ)) * LSeries f x) Filter.atTop (nhds (f n)) by
      simp only [H, Pi.zero_apply, mul_zero, tendsto_const_nhds_iff] at this
      exact this.symm
    cases n with
    | zero =>
        simp only [Nat.zero_eq, H, Pi.zero_apply, mul_zero, hf, tendsto_const_nhds_iff]
    | succ n =>
        simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
        exact LSeries_limit (fun m hm ↦ ih m <| Nat.lt_succ_of_le hm) <| Ne.lt_top h
