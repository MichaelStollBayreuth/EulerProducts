import Mathlib.Analysis.PSeries
import Mathlib.Topology.CompletelyRegular
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LegendreSymbol.MulCharacter
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
### Auxiliary lemmas
-/

namespace Nat

-- #10025

lemma Prime.one_le {p : ℕ} (hp : p.Prime) : 1 ≤ p := hp.one_lt.le

/- lemma pow_eq_one_iff {m n : ℕ} : m ^ n = 1 ↔ m = 1 ∨ n = 0 := by
  refine ⟨fun H ↦ (eq_or_ne n 0).elim Or.inr fun h ↦ Or.inl ?_, fun H ↦ ?_⟩
  · exact (_root_.pow_eq_one_iff h).mp H
  · rcases H with rfl | rfl <;> simp -/

lemma Prime.pow_injective {p q m n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p ^ (m + 1) = q ^ (n + 1)) : p = q ∧ m = n := by
  have H := dvd_antisymm (Prime.dvd_of_dvd_pow hp <| h ▸ dvd_pow_self p (succ_ne_zero m))
    (Prime.dvd_of_dvd_pow hq <| h.symm ▸ dvd_pow_self q (succ_ne_zero n))
  exact ⟨H, succ_inj'.mp <| Nat.pow_right_injective hq.two_le (H ▸ h)⟩

end Nat


namespace ZMod

-- #10028

open Nat

lemma eq_one_of_isUnit_natCast {n : ℕ} (h : IsUnit (n : ZMod 0)) : n = 1 := by
  have := Int.isUnit_iff.mp h
  norm_cast at this
  exact this.resolve_right not_false

lemma isUnit_iff_coprime (m n : ℕ) : IsUnit (m : ZMod n) ↔ m.Coprime n := by
  refine ⟨fun H ↦ ?_, fun H ↦ (unitOfCoprime m H).isUnit⟩
  have H' := val_coe_unit_coprime H.unit
  rw [IsUnit.unit_spec, val_nat_cast m, coprime_iff_gcd_eq_one] at H'
  rw [coprime_iff_gcd_eq_one, Nat.gcd_comm, ← H']
  exact gcd_rec n m

lemma isUnit_prime_of_not_dvd {n p : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) : IsUnit (p : ZMod n) := by
  rw [isUnit_iff_coprime]
  exact (Nat.Prime.coprime_iff_not_dvd hp).mpr h

-- needs primeFactors
lemma not_isUnit_of_mem_primeFactors {n p : ℕ} (h : p ∈ n.primeFactors) :
    ¬ IsUnit (p : ZMod n) := by
  rw [isUnit_iff_coprime]
  exact (Prime.dvd_iff_not_coprime <| prime_of_mem_primeFactors h).mp <| dvd_of_mem_primeFactors h

end ZMod


namespace Real

-- #10029

lemma log_le_mul_rpow {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) : log x ≤ ε⁻¹ * x ^ ε := by
  rcases hx.eq_or_lt with rfl | h
  · rw [log_zero, zero_rpow hε.ne', mul_zero]
  suffices : ε * log x ≤ x ^ ε
  · apply_fun (ε⁻¹ * ·) at this using monotone_mul_left_of_nonneg (inv_pos.mpr hε).le
    simp only at this
    rwa [← mul_assoc, inv_mul_cancel hε.ne', one_mul] at this
  exact (log_rpow h ε).symm.trans_le <| (log_le_sub_one_of_pos <| rpow_pos_of_pos h ε).trans
    (sub_one_lt _).le

lemma log_ofNat_le_mul_rpow (n : ℕ) {ε : ℝ} (hε : 0 < ε) : log n ≤ ε⁻¹ * n ^ ε :=
  log_le_mul_rpow n.cast_nonneg hε

-- This can be generalized to series of decreasing nonnegative terms
lemma not_summable_indicator_one_div_nat_cast {m : ℕ} (hm : m ≠ 0) (k : ZMod m) :
    ¬ Summable (Set.indicator {n : ℕ | (n : ZMod m) = k} fun n : ℕ ↦ (1 / n : ℝ)) := by
  have : NeZero m := { out := hm }
  suffices : ¬ Summable fun n : ℕ ↦ (1 / (m * n + k.val) : ℝ)
  · set f : ℕ → ℝ := Set.indicator {n : ℕ | (n : ZMod m) = k} fun n : ℕ ↦ (1 / n : ℝ)
    contrapose! this
    let g : ℕ → ℕ := fun n ↦ m * n + k.val
    have hg : Function.Injective g
    · intro m n hmn
      simpa [g, hm] using hmn
    have hg' : ∀ n ∉ Set.range g, f n = 0
    · intro n hn
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

end Real


namespace Complex

-- #10034

@[simp, norm_cast]
lemma nat_cast_log {n : ℕ} : Real.log n = log n := ofReal_nat_cast n ▸ ofReal_log n.cast_nonneg

@[simp, norm_cast]
lemma nat_cast_arg {n : ℕ} : arg n = 0 :=
  ofReal_nat_cast n ▸ arg_ofReal_of_nonneg n.cast_nonneg

lemma nat_cast_mul_nat_cast_cpow (m n : ℕ) (s : ℂ) : (m * n : ℂ) ^ s = m ^ s * n ^ s :=
  ofReal_nat_cast m ▸ ofReal_nat_cast n ▸ mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg s

lemma nat_cast_cpow_nat_cast_mul (n m : ℕ) (z : ℂ) : (n : ℂ) ^ (m * z) = ((n : ℂ) ^ m) ^ z := by
  refine cpow_nat_mul' (x := n) (n := m) ?_ ?_ z
  · simp only [nat_cast_arg, mul_zero, Left.neg_neg_iff, Real.pi_pos]
  · simp only [nat_cast_arg, mul_zero, Real.pi_pos.le]

-- #10029 for the following five

lemma norm_ofNat_cpow_of_re_ne_zero (n : ℕ) {s : ℂ} (hs : s.re ≠ 0) :
    ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ (s.re) := by
  rw [norm_eq_abs, ← ofReal_nat_cast, abs_cpow_eq_rpow_re_of_nonneg n.cast_nonneg hs]

lemma norm_ofNat_cpow_of_pos {n : ℕ} (hn : 0 < n) (s : ℂ) :
    ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ (s.re) := by
  rw [norm_eq_abs, ← ofReal_nat_cast, abs_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn) _]

lemma norm_ofNat_cpow_pos_of_pos {n : ℕ} (hn : 0 < n) (s : ℂ) : 0 < ‖(n : ℂ) ^ s‖ :=
  (norm_ofNat_cpow_of_pos hn _).symm ▸ Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

lemma norm_prime_cpow_le_one_half (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  rw [norm_ofNat_cpow_of_re_ne_zero p <| by rw [neg_re]; linarith only [hs]]
  refine (Real.rpow_le_rpow_of_nonpos zero_lt_two (Nat.cast_le.mpr p.prop.two_le) <|
    by rw [neg_re]; linarith only [hs]).trans ?_
  rw [one_div, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two <| (neg_lt_neg hs).le

lemma one_sub_prime_cpow_ne_zero {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  refine sub_ne_zero_of_ne fun H ↦ ?_
  have := norm_prime_cpow_le_one_half ⟨p, hp⟩ hs
  simp only at this
  rw [← H, norm_one] at this
  norm_num at this

lemma norm_ofNat_cpow_le_norm_ofNat_cpow_of_pos {n : ℕ} (hn : 0 < n) {w z : ℂ} (h : w.re ≤ z.re) :
    ‖(n : ℂ) ^ w‖ ≤ ‖(n : ℂ) ^ z‖ := by
  simp_rw [norm_ofNat_cpow_of_pos hn]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) h

--

lemma summable_re {α : Type u_1} {f : α → ℂ} (h : Summable f) : Summable fun x ↦ (f x).re :=
  (Complex.hasSum_re h.hasSum).summable

lemma summable_im {α : Type u_1} {f : α → ℂ} (h : Summable f) : Summable fun x ↦ (f x).im :=
  (Complex.hasSum_im h.hasSum).summable

-- #find_home summable_re -- [Mathlib.Analysis.Complex.Basic]

-- needs #10029
lemma norm_log_ofNat_le_mul_rpow (n : ℕ) {ε : ℝ} (hε : 0 < ε) : ‖log n‖ ≤ ε⁻¹ * n ^ ε := by
  rcases n.eq_zero_or_pos with rfl | h
  · rw [Nat.cast_zero, Nat.cast_zero, log_zero, norm_zero, Real.zero_rpow hε.ne', mul_zero]
  rw [norm_eq_abs, ← nat_cast_log, abs_ofReal,
    _root_.abs_of_nonneg <| Real.log_nonneg <| by exact_mod_cast Nat.one_le_of_lt h.lt]
  exact Real.log_ofNat_le_mul_rpow n hε

end Complex


namespace MulChar

-- #10039

@[coe]
def toMonoidWithZeroHom {R R' : Type*} [CommMonoidWithZero R] [CommMonoidWithZero R']
    [Nontrivial R] (χ : MulChar R R') : R →*₀ R' where
      toFun := χ.toFun
      map_zero' := χ.map_zero
      map_one' := χ.map_one'
      map_mul' := χ.map_mul'

lemma one_apply {R : Type*} [CommMonoid R] (R' : Type*) [CommMonoidWithZero R'] {x : R}
    (hx : IsUnit x) : (1 : MulChar R R') x = 1 :=  one_apply_coe hx.unit

end MulChar


section Topology

namespace Asymptotics

open Filter

lemma isBigO_mul_iff_isBigO_div {α F : Type*} [NormedField F] {l : Filter α} {f g h : α → F}
    (hf : ∀ᶠ x in l, f x ≠ 0) :
    (fun x ↦ f x * g x) =O[l] h ↔ g =O[l] (fun x ↦ h x / f x) := by
  rw [isBigO_iff', isBigO_iff']
  refine ⟨fun ⟨c, hc, H⟩ ↦ ⟨c, hc, ?_⟩, fun ⟨c, hc, H⟩ ↦ ⟨c, hc, ?_⟩⟩ <;>
  { refine H.congr <| Eventually.mp hf <| eventually_of_forall fun x hx ↦ ?_
    rw [norm_mul, norm_div, ← mul_div_assoc, mul_comm]
    have hx' : ‖f x‖ > 0 := norm_pos_iff.mpr hx
    rw [le_div_iff hx', mul_comm] }

lemma isLittleO_id {F : Type*} [NormedField F] (s : Set F) :
    (id : F → F) =o[nhdsWithin 0 s] (fun _ ↦ (1 : F)) :=
  ((isLittleO_one_iff F).mpr tendsto_id).mono nhdsWithin_le_nhds

end Asymptotics


open Topology Asymptotics in
lemma DifferentiableAt.isBigO_of_eq_zero {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z)
    (hz : f z = 0) : (fun w ↦ f (w + z)) =O[𝓝 0] id := by
  rw [← zero_add z] at hf
  have := (hf.hasDerivAt.comp_add_const 0 z).differentiableAt.isBigO_sub
  simp only [zero_add, hz, sub_zero] at this
  exact this.trans <| isBigO_refl ..

open Topology Asymptotics Filter in
lemma ContinuousAt.isBigO {f : ℂ → ℂ} {z : ℂ} (hf : ContinuousAt f z) :
    (fun w ↦ f (w + z)) =O[𝓝 0] (fun _ ↦ (1 : ℂ)) := by
  rw [isBigO_iff']
  replace hf : ContinuousAt (fun w ↦ f (w + z)) 0
  · convert (Homeomorph.comp_continuousAt_iff' (Homeomorph.addLeft (-z)) _ z).mp ?_
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

open Topology in
lemma Complex.isBigO_comp_ofReal {f g : ℂ → ℂ} {x : ℝ} (h : f =O[𝓝 (x : ℂ)] g) :
    (fun y : ℝ ↦ f y) =O[𝓝 x] (fun y : ℝ ↦ g y) :=
  Asymptotics.IsBigO.comp_tendsto (k := fun y : ℝ ↦ (y : ℂ)) h <|
    Continuous.tendsto Complex.continuous_ofReal x

open Topology in
lemma Complex.isBigO_comp_ofReal_nhds_ne {f g : ℂ → ℂ} {x : ℝ} (h : f =O[𝓝[≠] (x : ℂ)] g) :
    (fun y : ℝ ↦ f y) =O[𝓝[≠] x] (fun y : ℝ ↦ g y) :=
  Asymptotics.IsBigO.comp_tendsto (k := fun y : ℝ ↦ (y : ℂ)) h <|
    ((hasDerivAt_id (x : ℂ)).comp_ofReal).tendsto_punctured_nhds one_ne_zero

end Topology

-- #10087

namespace Fin

lemma snoc_zero {α : Type*} (p : Fin 0 → α) (x : α) :
    Fin.snoc p x = fun _ ↦ x := by
  ext y
  have : Subsingleton (Fin (0 + 1)) := Fin.subsingleton_one
  simp only [Subsingleton.elim y (Fin.last 0), snoc_last]

end Fin

namespace Finset

lemma piecewise_same {α : Type*} {δ : α → Sort*} (s : Finset α)
    (f : (i : α) → δ i) [(j : α) → Decidable (j ∈ s)] :
    s.piecewise f f = f := by
  ext i
  by_cases h : i ∈ s <;> simp [h]

end Finset


namespace FormalMultilinearSeries

universe u v

variable {𝕜 : Type*} {E : Type u} {F : Type v} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (p : FormalMultilinearSeries 𝕜 E F)

/-- This series appears in `HasFPowerSeriesOnBall.fderiv` -/
noncomputable
def derivSeries : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F) :=
  (continuousMultilinearCurryFin1 𝕜 E F : (E[×1]→L[𝕜] F) →L[𝕜] E →L[𝕜] F)
    |>.compFormalMultilinearSeries (p.changeOriginSeries 1)

open Fintype ContinuousLinearMap in
theorem derivSeries_apply_diag (n : ℕ) (x : E) :
    derivSeries p n (fun _ ↦ x) x = (n + 1) • p (n + 1) fun _ ↦ x := by
  simp only [derivSeries, strongUniformity_topology_eq, compFormalMultilinearSeries_apply,
    changeOriginSeries, compContinuousMultilinearMap_coe, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_coe, Function.comp_apply, ContinuousMultilinearMap.sum_apply, map_sum,
    coe_sum', Finset.sum_apply, continuousMultilinearCurryFin1_apply, Matrix.zero_empty]
  convert Finset.sum_const _
  · rw [Fin.snoc_zero, changeOriginSeriesTerm_apply, Finset.piecewise_same, add_comm]
  · erw [← card, card_subtype, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard, ← card,
      card_fin, eq_comm, add_comm, Nat.choose_succ_self_right]

end FormalMultilinearSeries

namespace HasFPowerSeriesOnBall

universe u v

open FormalMultilinearSeries ENNReal Nat

variable {𝕜 : Type*} {E : Type u} {F : Type v} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {p : FormalMultilinearSeries 𝕜 E F} {f : E → F} {x : E} {r : ℝ≥0∞}
  (h : HasFPowerSeriesOnBall f p x r) (y : E)

theorem iteratedFDeriv_zero_apply_diag :
    iteratedFDeriv 𝕜 0 f x (fun _ ↦ y) = p 0 (fun _ ↦ y) := by
  convert (h.hasSum <| EMetric.mem_ball_self h.r_pos).tsum_eq.symm
  · rw [iteratedFDeriv_zero_apply, add_zero]
  · rw [tsum_eq_single 0 <| fun n hn ↦ by haveI := NeZero.mk hn; exact (p n).map_zero]
    exact congr(p 0 $(Subsingleton.elim _ _))

open ContinuousLinearMap

private theorem factorial_smul' : ∀ {F : Type max u v} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] {p : FormalMultilinearSeries 𝕜 E F}
    {f : E → F}, HasFPowerSeriesOnBall f p x r →
    n ! • p n (fun _ ↦ y) = iteratedFDeriv 𝕜 n f x (fun _ ↦ y) := by
  induction' n with n ih <;> intro F _ _ _ p f h
  · rw [factorial_zero, one_smul, h.iteratedFDeriv_zero_apply_diag]
  · rw [factorial_succ, mul_comm, mul_smul, ← derivSeries_apply_diag, ← smul_apply, derivSeries,
      ih h.fderiv, iteratedFDeriv_succ_apply_right]
    rfl

variable [CompleteSpace F]

theorem factorial_smul (n : ℕ) :
    n ! • p n (fun _ ↦ y) = iteratedFDeriv 𝕜 n f x (fun _ ↦ y) := by
  cases n
  · rw [factorial_zero, one_smul, h.iteratedFDeriv_zero_apply_diag]
  · erw [factorial_succ, mul_comm, mul_smul, ← derivSeries_apply_diag, ← smul_apply,
      factorial_smul'.{_,u,v} _ h.fderiv, iteratedFDeriv_succ_apply_right]
    rfl

theorem hasSum_iteratedFDeriv [CharZero 𝕜] {y : E} (hy : y ∈ EMetric.ball 0 r) :
    HasSum (fun n ↦ (n ! : 𝕜)⁻¹ • iteratedFDeriv 𝕜 n f x fun _ ↦ y) (f (x + y)) := by
  convert h.hasSum hy with n
  rw [← h.factorial_smul y n, smul_comm, ← smul_assoc, nsmul_eq_mul,
    mul_inv_cancel <| cast_ne_zero.mpr n.factorial_ne_zero, one_smul]

/- We can't quite show
  `HasFPowerSeriesOnBall f (fun n ↦ (1 / n !) • iteratedFDeriv 𝕜 n f x) x r`
  because `r_le` requires bounding the norm of a multilinear map using values on
  the diagonal, so some polarization identity would be required. -/

end HasFPowerSeriesOnBall


namespace Complex

open BigOperators Nat

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A function that is complex differentiable on the open ball of radius `r` around `c`
is given by evaluating its Taylor series at `c` on this open ball. -/
lemma hasSum_taylorSeries_on_ball {f : ℂ → E} ⦃r : NNReal⦄
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) ⦃z : ℂ⦄ (hz : z ∈ Metric.ball c r) :
    HasSum (fun n : ℕ ↦ (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) := by
  obtain ⟨r', hr', hr'₀, hzr'⟩ : ∃ r' < r, 0 < r' ∧ z ∈ Metric.ball c r'
  · obtain ⟨r', h₁, h₂⟩ := exists_between (Metric.mem_ball'.mp hz)
    lift r' to NNReal using dist_nonneg.trans h₁.le
    exact ⟨r', h₂, pos_of_gt h₁, Metric.mem_ball'.mpr h₁⟩
  have hz' : z - c ∈ EMetric.ball 0 r'
  · rw [Metric.emetric_ball_nnreal]
    exact mem_ball_zero_iff.mpr hzr'
  have H := (hf.mono <| Metric.closedBall_subset_ball hr').hasFPowerSeriesOnBall hr'₀
      |>.hasSum_iteratedFDeriv hz'
  simp only [add_sub_cancel'_right] at H
  convert H using 4 with n
  simpa only [iteratedDeriv_eq_iteratedFDeriv, smul_eq_mul, mul_one, Finset.prod_const,
    Finset.card_fin]
    using ((iteratedFDeriv ℂ n f c).map_smul_univ (fun _ ↦ z - c) (fun _ ↦ 1)).symm

-- import Mathlib.Analysis.Complex.CauchyIntegral

/-- A function that is complex differentiable on the open ball of radius `r` around `c`
is given by evaluating its Taylor series at `c` on theis open ball. -/
lemma taylorSeries_eq_on_ball {f : ℂ → E} ⦃r : NNReal⦄
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) ⦃z : ℂ⦄ (hz : z ∈ Metric.ball c r) :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c = f z :=
  (hasSum_taylorSeries_on_ball hf hz).tsum_eq

/-- A function that is complex differentiable on the open ball of radius `r` around `c`
is given by evaluating its Taylor series at `c` on this open ball. -/
lemma taylorSeries_eq_on_ball' {f : ℂ → ℂ} ⦃r : NNReal⦄
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) ⦃z : ℂ⦄ (hz : z ∈ Metric.ball c r) :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ * iteratedDeriv n f c * (z - c) ^ n = f z := by
  convert taylorSeries_eq_on_ball hf hz using 3 with n
  rw [mul_right_comm, smul_eq_mul, smul_eq_mul, mul_assoc]

/-- A function that is complex differentiable on the complex plane is given by evaluating
its Taylor series at any point `c`. -/
lemma hasSum_taylorSeries_of_entire {f : ℂ → E} (hf : Differentiable ℂ f) (c z : ℂ) :
    HasSum (fun n : ℕ ↦ (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) := by
  have hf' : DifferentiableOn ℂ f
      (Metric.ball c (⟨1 + ‖z - c‖, add_nonneg zero_le_one <| norm_nonneg _⟩ : NNReal)) :=
    hf.differentiableOn
  refine hasSum_taylorSeries_on_ball hf' ?_
  rw [mem_ball_iff_norm, NNReal.coe_mk, lt_add_iff_pos_left]
  exact zero_lt_one

/-- A function that is complex differentiable on the complex plane is given by evaluating
its Taylor series at any point `c`. -/
lemma taylorSeries_eq_of_entire {f : ℂ → E} (hf : Differentiable ℂ f) (c z : ℂ) :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c = f z :=
  (hasSum_taylorSeries_of_entire hf c z).tsum_eq

/-- A function that is complex differentiable on the complex plane is given by evaluating
its Taylor series at any point `c`. -/
lemma taylorSeries_eq_of_entire' {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c z : ℂ) :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ * iteratedDeriv n f c * (z - c) ^ n = f z := by
  convert taylorSeries_eq_of_entire hf c z using 3 with n
  rw [mul_right_comm, smul_eq_mul, smul_eq_mul, mul_assoc]

end Complex

-- (until here: #10087)


namespace deriv

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open ContinuousLinearMap in
lemma comp_neg (f : 𝕜 → F) (a : 𝕜) : deriv (fun x ↦ f (-x)) a = -deriv f (-a) := by
  by_cases h : DifferentiableAt 𝕜 f (-a)
  · simp_rw [← fderiv_deriv]
    change (fderiv 𝕜 (f ∘ fun x ↦ -x) a) 1 = _
    rw [fderiv.comp _ h differentiable_neg.differentiableAt, show @Neg.neg 𝕜 _ = (- ·) from rfl,
      coe_comp', Function.comp_apply, fderiv_neg, fderiv_id', neg_apply, coe_id', id_eq, map_neg]
  · have H : ¬ DifferentiableAt 𝕜 (fun x ↦ f (-x)) a
    · contrapose! h
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
    · have H : ¬DifferentiableAt 𝕜 (fun y ↦ c • f y) x
      · contrapose! hf
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
    DifferentiableAt ℝ (fun (y : ℝ) => (f y : ℂ)) z :=
  hf.hasDerivAt.ofReal_comp.differentiableAt

lemma Differentiable.ofReal_comp {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    Differentiable ℝ (fun (y : ℝ) => (f y : ℂ)) :=
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
    DifferentiableAt ℝ (fun (y : ℝ) => (f y : ℂ)) z ↔ DifferentiableAt ℝ f z := by
  refine ⟨fun H ↦ ?_, ofReal_comp⟩
  obtain ⟨u, _, hu₂⟩ := H.hasDerivAt.of_hasDerivAt_ofReal_comp
  exact HasDerivAt.differentiableAt hu₂

lemma Differentiable.ofReal_comp_iff {f : ℝ → ℝ} :
    Differentiable ℝ (fun (y : ℝ) => (f y : ℂ)) ↔ Differentiable ℝ f :=
  forall_congr' fun _ ↦ DifferentiableAt.ofReal_comp_iff

lemma deriv.ofReal_comp {z : ℝ} {f : ℝ → ℝ} :
    deriv (fun (y : ℝ) => (f y : ℂ)) z = deriv f z := by
  by_cases hf : DifferentiableAt ℝ f z
  · exact hf.hasDerivAt.ofReal_comp.deriv
  · have hf' := mt DifferentiableAt.ofReal_comp_iff.mp hf
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hf',
      Complex.ofReal_zero]

-- #10112

namespace Complex

section OrderInstance

open scoped ComplexOrder

instance : OrderClosedTopology ℂ where
  isClosed_le' := by
    simp_rw [le_def, Set.setOf_and]
    refine IsClosed.inter (isClosed_le ?_ ?_) (isClosed_eq ?_ ?_) <;> continuity

lemma monotone_ofReal : Monotone ofReal' := by
  intro x y hxy
  simp only [ofReal_eq_coe, real_le_real, hxy]

end OrderInstance

--


open Nat

/-- A function that is complex differentiable on the closed ball of radius `r` around `c`,
where `c` is real, and all whose iterated derivatives at `c` are real can be give by a real
differentiable function on the real open interval from `c-r` to `c+r`. -/
lemma realValued_of_iteratedDeriv_real_on_ball {f : ℂ → ℂ} ⦃r : NNReal⦄ {c : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) ⦃D : ℕ → ℝ⦄
    (hd : ∀ n, iteratedDeriv n f c = D n) :
    ∃ F : ℝ → ℝ, DifferentiableOn ℝ F (Set.Ioo (c - r) (c + r)) ∧
      Set.EqOn (f ∘ ofReal') (ofReal' ∘ F) (Set.Ioo (c - r) (c + r)) := by
  have Hz : ∀ x ∈ Set.Ioo (c - r) (c + r), (x : ℂ) ∈ Metric.ball (c : ℂ) r
  · intro x hx
    refine Metric.mem_ball.mpr ?_
    rw [dist_eq, ← ofReal_sub, abs_ofReal, abs_sub_lt_iff, sub_lt_iff_lt_add', sub_lt_comm]
    exact and_comm.mpr hx
  have H := taylorSeries_eq_on_ball' hf
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
  have H := taylorSeries_eq_of_entire' hf c
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
  have H := taylorSeries_eq_of_entire' hf 0 z
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
  have hD (n : ℕ) : iteratedDeriv n f 0 = D n
  · refine Complex.ext rfl ?_
    simp only [ofReal_im]
    exact (le_def.mp (h n)).2.symm
  obtain ⟨F, hFd, hF⟩ := realValued_of_iteratedDeriv_real hf hD
  rw [hF]
  refine monotone_ofReal.comp_monotoneOn <| (convex_Ici 0).monotoneOn_of_deriv_nonneg
    hFd.continuous.continuousOn hFd.differentiableOn fun x hx ↦ ?_
  have hD' (n : ℕ) : 0 ≤ iteratedDeriv n (deriv f) 0
  · rw [← iteratedDeriv_succ']
    exact h (n + 1)
  have hf' := (contDiff_succ_iff_deriv.mp <| hf.contDiff (n := 2)).2.differentiable rfl.le
  have hx : (0 : ℂ) ≤ x
  · norm_cast
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
  have h' (n : ℕ) : 0 ≤ iteratedDeriv n (f · - f 0) 0
  · cases n with
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
