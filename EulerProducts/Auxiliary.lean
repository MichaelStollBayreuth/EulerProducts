import Mathlib.Analysis.PSeries
import Mathlib.Topology.CompletelyRegular
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.NumberTheory.LegendreSymbol.MulCharacter
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
### Auxiliary lemmas
-/

namespace Nat

lemma Prime.one_le {p : ℕ} (hp : p.Prime) : 1 ≤ p := hp.one_lt.le

lemma pow_eq_one_iff {m n : ℕ} : m ^ n = 1 ↔ m = 1 ∨ n = 0 := by
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · rcases eq_or_ne n 0 with h | h
    · exact Or.inr h
    · refine Or.inl ?_
      rcases m.eq_zero_or_pos with rfl | hm
      · simp [h] at H
      by_contra! hm'
      exact (H ▸ (one_lt_pow_iff h).mpr <| lt_of_le_of_ne hm hm'.symm).false
  · rcases H with rfl | rfl <;> simp

lemma pow_injective_on_primes {p q m n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p ^ (m + 1) = q ^ (n + 1)) : p = q ∧ m = n := by
  have H := dvd_antisymm (Prime.dvd_of_dvd_pow hp <| h ▸ dvd_pow_self p (succ_ne_zero m))
    (Prime.dvd_of_dvd_pow hq <| h.symm ▸ dvd_pow_self q (succ_ne_zero n))
  exact ⟨H, succ_inj'.mp <| Nat.pow_right_injective hq.two_le (H ▸ h)⟩

end Nat


namespace Real

lemma log_le_rpow {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) :
    log x ≤ ε⁻¹ * x ^ ε := by
  rcases hx.eq_or_lt with rfl | h
  · rw [log_zero, zero_rpow hε.ne', mul_zero]
  suffices : ε * log x ≤ x ^ ε
  · apply_fun (ε⁻¹ * ·) at this using monotone_mul_left_of_nonneg (inv_pos.mpr hε).le
    simp only at this
    rwa [← mul_assoc, inv_mul_cancel hε.ne', one_mul] at this
  exact (log_rpow h ε).symm.trans_le <| (log_le_sub_one_of_pos <| rpow_pos_of_pos h ε).trans
    (sub_one_lt _).le

lemma log_ofNat_le_rpow (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    log n ≤ ε⁻¹ * n ^ ε :=
  log_le_rpow n.cast_nonneg hε

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

@[simp, norm_cast]
lemma ofNat_log {n : ℕ} : Real.log n = log n := ofReal_nat_cast n ▸ ofReal_log n.cast_nonneg

@[simp, norm_cast]
lemma ofNat_arg {n : ℕ} : arg n = 0 :=
  ofReal_nat_cast n ▸ arg_ofReal_of_nonneg n.cast_nonneg

lemma norm_log_ofNat_le_rpow (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ‖log n‖ ≤ ε⁻¹ * n ^ ε := by
  rcases n.eq_zero_or_pos with rfl | h
  · rw [Nat.cast_zero, Nat.cast_zero, log_zero, norm_zero, Real.zero_rpow hε.ne', mul_zero]
  rw [norm_eq_abs, ← ofNat_log, abs_ofReal,
    _root_.abs_of_nonneg <| Real.log_nonneg <| by exact_mod_cast Nat.one_le_of_lt h.lt]
  exact Real.log_ofNat_le_rpow n hε

lemma mul_cpow_ofNat (m n : ℕ) (s : ℂ) : (m * n : ℂ) ^ s = m ^ s * n ^ s :=
  ofReal_nat_cast m ▸ ofReal_nat_cast n ▸ mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg s

lemma ofNat_cpow_mul (n m : ℕ) (z : ℂ) : (n : ℂ) ^ (m * z) = ((n : ℂ) ^ m) ^ z := by
  rw [cpow_mul]
  · rw [cpow_nat_cast]
  all_goals
    rw [← ofNat_log]
    norm_cast
    linarith [Real.pi_pos]

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

lemma norm_ofNat_cpow_le_norm_ofNat_cpow_of_pos {n : ℕ} (hn : 0 < n) {w z : ℂ} (h : w.re ≤ z.re) :
    ‖(n : ℂ) ^ w‖ ≤ ‖(n : ℂ) ^ z‖ := by
  simp_rw [norm_ofNat_cpow_of_pos hn]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) h

lemma indicator_ofReal {f : ℕ → ℝ} {s : Set ℕ} :
    (fun n ↦ ((Set.indicator s f n : ℝ) : ℂ)) = Set.indicator s (fun n ↦ (f n : ℂ)) := by
  ext n
  by_cases h : n ∈ s
  · simp only [h, Set.indicator_of_mem]
  · simp only [h, not_false_eq_true, Set.indicator_of_not_mem, ofReal_zero]

lemma summable_re {α : Type u_1} {f : α → ℂ} (h : Summable f) :
    Summable fun x ↦ (f x).re :=
  HasSum.summable <| Complex.hasSum_re h.hasSum

lemma summable_im {α : Type u_1} {f : α → ℂ} (h : Summable f) :
    Summable fun x ↦ (f x).im :=
  HasSum.summable <| Complex.hasSum_im h.hasSum

end Complex


namespace Equiv.Set

lemma prod_symm_apply {α β : Type*} (s : Set α) (t : Set β) (x : s × t) :
    (Set.prod s t).symm x = (x.1.val, x.2.val) := rfl

/-- The canonical equivalence between `{a} ×ˢ t` and `t`, considered as types. -/
def prod_singleton_left {α β : Type*} (a : α) (t : Set β) : ↑({a} ×ˢ t) ≃ ↑t where
  toFun := fun x ↦ ⟨x.val.snd, (Set.mem_prod.mp x.prop).2⟩
  invFun := fun b ↦ ⟨(a, b.val), Set.mem_prod.mpr ⟨Set.mem_singleton a, Subtype.mem b⟩⟩
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

/-- The canonical equivalence between `s ×ˢ {b}` and `s`, considered as types. -/
def prod_singleton_right {α β : Type*} (s : Set α) (b : β) : ↑(s ×ˢ {b}) ≃ ↑s where
  toFun := fun x ↦ ⟨x.val.fst, (Set.mem_prod.mp x.prop).1⟩
  invFun := fun a ↦ ⟨(a.val, b), Set.mem_prod.mpr ⟨Subtype.mem a, Set.mem_singleton b⟩⟩
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

end Equiv.Set


lemma HasSum.tsum_fibers {β γ : Type*} {f : β → ℂ} (g : β → γ) {a : ℂ} (hf : HasSum f a) :
    HasSum (fun c : γ ↦ ∑' b : g ⁻¹' {c}, f b) a :=
  HasSum.sigma ((Equiv.hasSum_iff <| Equiv.sigmaFiberEquiv g).mpr hf) <|
    fun _ ↦ (Summable.hasSum_iff <| Summable.subtype hf.summable _).mpr rfl

lemma tsum_setProd_eq_tsum_prod {α β : Type*} (s : Set α) (t : Set β) (f : α × β → ℂ) :
    (∑' x : s ×ˢ t, f x) = ∑' x : s × t, f ((Equiv.Set.prod s t).symm x) :=
  ((Equiv.Set.prod s t).symm.tsum_eq <| (s ×ˢ t).restrict f).symm

lemma tsum_setProd_singleton_left {α β : Type*} (a : α) (t : Set β) (f : α × β → ℂ) :
    (∑' x : {a} ×ˢ t, f x) = ∑' b : t, f (a, b) :=
  (Equiv.Set.prod_singleton_left a t |>.symm.tsum_eq <| ({a} ×ˢ t).restrict f).symm

lemma tsum_setProd_singleton_right {α β : Type*} (s : Set α) (b : β) (f : α × β → ℂ) :
    (∑' x : s ×ˢ {b}, f x) = ∑' a : s, f (a, b) :=
  (Equiv.Set.prod_singleton_right s b |>.symm.tsum_eq <| (s ×ˢ {b}).restrict f).symm


namespace MulChar

@[coe]
def toMonoidWithZeroHom  {R R' : Type*} [CommMonoidWithZero R] [CommMonoidWithZero R']
    [Nontrivial R] (χ : MulChar R R') : R →*₀ R' where
      toFun := χ.toFun
      map_zero' := χ.map_zero
      map_one' := χ.map_one'
      map_mul' := χ.map_mul'

lemma one_apply {R : Type*} [CommMonoid R] (R' : Type*) [CommMonoidWithZero R'] {x : R}
    (hx : IsUnit x) : (1 : MulChar R R') x = 1 := by
  rw [show (1 : MulChar R R') = trivial R R' from rfl]
  simp only [trivial_apply, hx, ite_true]

end MulChar

section Topology

namespace Asymptotics

open Filter in
lemma isBigO_mul_iff_isBigO_div {α F : Type*} [NormedField F] {l : Filter α} {f g h : α → F}
    (hf : ∀ᶠ x in l, f x ≠ 0) :
    (fun x ↦ f x * g x) =O[l] h ↔ g =O[l] (fun x ↦ h x / f x) := by
  rw [isBigO_iff', isBigO_iff']
  refine ⟨fun ⟨c, hc, H⟩ ↦ ⟨c, hc, ?_⟩, fun ⟨c, hc, H⟩ ↦ ⟨c, hc, ?_⟩⟩ <;>
  { refine H.congr <| Eventually.mp hf <| eventually_of_forall fun x hx ↦ ?_
    rw [norm_mul, norm_div, ← mul_div_assoc, mul_comm]
    have hx' : ‖f x‖ > 0 := norm_pos_iff.mpr hx
    rw [le_div_iff hx', mul_comm] }

open Topology Filter in
lemma isLittleO_id (s : Set ℝ) : (id : ℝ → ℝ) =o[nhdsWithin 0 s] (fun _ ↦ (1 : ℝ)) :=
  ((isLittleO_one_iff ℝ).mpr tendsto_id).mono nhdsWithin_le_nhds

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
