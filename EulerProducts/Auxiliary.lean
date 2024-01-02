import Mathlib.Data.Real.EReal
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
### Auxiliary lemmas
-/

namespace Real

lemma log_le_rpow {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) :
    log x ≤ ε⁻¹ * x ^ ε := by
  have hε' : 0 < ε⁻¹ := inv_pos.mpr hε
  rcases hx.eq_or_lt with rfl | h
  · rw [log_zero, zero_rpow hε.ne', mul_zero]
  suffices : ε * log x ≤ x ^ ε
  · apply_fun (ε⁻¹ * ·) at this using monotone_mul_left_of_nonneg hε'.le
    simp only at this
    rwa [← mul_assoc, inv_mul_cancel hε.ne', one_mul] at this
  exact (log_rpow h ε).symm.trans_le <| (log_le_sub_one_of_pos <| rpow_pos_of_pos h ε).trans
    (sub_one_lt _).le

lemma log_ofNat_le_rpow (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    log n ≤ ε⁻¹ * n ^ ε :=
  log_le_rpow n.cast_nonneg hε

end Real

namespace EReal

lemma exists_between_ofReal_left {x : EReal} {z : ℝ} (h : x < z) : ∃ y : ℝ, x < y ∧ y < z := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_between h
  induction' a using EReal.rec with a₀
  · simp only [not_lt_bot] at ha₁
  · exact ⟨a₀, by exact_mod_cast ha₁, by exact_mod_cast ha₂⟩
  · simp only [not_top_lt] at ha₂

lemma exists_between_ofReal_right {x : ℝ} {z : EReal} (h : x < z) : ∃ y : ℝ, x < y ∧ y < z := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_between h
  induction' a using EReal.rec with a₀
  · simp only [not_lt_bot] at ha₁
  · exact ⟨a₀, by exact_mod_cast ha₁, by exact_mod_cast ha₂⟩
  · simp only [not_top_lt] at ha₂

lemma Icc_of_Real {x y : ℝ} : Real.toEReal '' Set.Icc x y = Set.Icc ↑x ↑y := by
  refine (Set.image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Icc, WithBot.image_coe_Icc]
  rfl

lemma Ico_of_Real {x y : ℝ} : Real.toEReal '' Set.Ico x y = Set.Ico ↑x ↑y := by
  refine (Set.image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ico, WithBot.image_coe_Ico]
  rfl

lemma Ici_of_Real {x : ℝ} : Real.toEReal '' Set.Ici x = Set.Ico ↑x ⊤ := by
  refine (Set.image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ici, WithBot.image_coe_Ico]
  rfl

lemma Ioc_of_Real {x y : ℝ} : Real.toEReal '' Set.Ioc x y = Set.Ioc ↑x ↑y := by
  refine (Set.image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioc, WithBot.image_coe_Ioc]
  rfl

lemma Ioo_of_Real {x y : ℝ} : Real.toEReal '' Set.Ioo x y = Set.Ioo ↑x ↑y := by
  refine (Set.image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioo, WithBot.image_coe_Ioo]
  rfl

lemma Ioi_ofReal {x : ℝ} : Real.toEReal '' Set.Ioi x = Set.Ioo ↑x ⊤ := by
  refine (Set.image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioi, WithBot.image_coe_Ioo]
  rfl

lemma Iic_ofReal {x : ℝ} : Real.toEReal '' Set.Iic x = Set.Ioc ⊥ ↑x := by
  refine (Set.image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Iic, WithBot.image_coe_Iic]
  rfl

lemma Iio_ofReal {x : ℝ} : Real.toEReal '' Set.Iio x = Set.Ioo ⊥ ↑x := by
  refine (Set.image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Iio, WithBot.image_coe_Iio]
  rfl

end EReal


namespace Complex

@[simp, norm_cast]
lemma ofNat_log {n : ℕ} : Real.log n = log n := ofReal_nat_cast n ▸ ofReal_log n.cast_nonneg

lemma norm_log_ofNat_le_rpow (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ‖log n‖ ≤ ε⁻¹ * n ^ ε := by
  rcases n.eq_zero_or_pos with rfl | h
  · rw [Nat.cast_zero, Nat.cast_zero, log_zero, norm_zero, Real.zero_rpow hε.ne', mul_zero]
  rw [norm_eq_abs, ← ofNat_log, abs_ofReal,
    _root_.abs_of_nonneg <| Real.log_nonneg <| by exact_mod_cast Nat.one_le_of_lt h.lt]
  exact Real.log_ofNat_le_rpow n hε

lemma mul_cpow_ofNat (m n : ℕ) (s : ℂ) : (m * n : ℂ) ^ s = m ^ s * n ^ s :=
  ofReal_nat_cast m ▸ ofReal_nat_cast n ▸ mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg s

lemma norm_ofNat_cpow_of_re_ne_zero (n : ℕ) {s : ℂ} (hs : s.re ≠ 0) :
    ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ (s.re) := by
  rw [norm_eq_abs, ← ofReal_nat_cast, abs_cpow_eq_rpow_re_of_nonneg n.cast_nonneg hs]

lemma norm_ofNat_cpow_of_pos {n : ℕ} (hn : 0 < n) (s : ℂ) :
    ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ (s.re) := by
  rw [norm_eq_abs, ← ofReal_nat_cast, abs_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn) _]

lemma norm_ofNat_cpow_pos_of_pos {n : ℕ} (hn : 0 < n) (s : ℂ) : 0 < ‖(n : ℂ) ^ s‖ :=
  (norm_ofNat_cpow_of_pos hn _).symm ▸ Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

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

lemma tsum_prod_singleton_left {α β : Type*} (a : α) (t : Set β) (f : α × β → ℂ) :
    (∑' x : {a} ×ˢ t, f x) = ∑' b : t, f (a, b) :=
  (Equiv.Set.prod_singleton_left a t |>.symm.tsum_eq <| ({a} ×ˢ t).restrict f).symm

lemma tsum_prod_singleton_right {α β : Type*} (s : Set α) (b : β) (f : α × β → ℂ) :
    (∑' x : s ×ˢ {b}, f x) = ∑' a : s, f (a, b) :=
  (Equiv.Set.prod_singleton_right s b |>.symm.tsum_eq <| (s ×ˢ {b}).restrict f).symm
