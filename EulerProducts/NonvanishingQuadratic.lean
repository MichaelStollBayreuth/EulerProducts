import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet
import EulerProducts.Auxiliary
import EulerProducts.Positivity

/-!
# Non-vanishing of `L(χ, 1)` for nontrivial quadratic characters `χ`
-/

open Complex

/-- The object we're trying to show doesn't exist. -/
structure BadChar (N : ℕ) [NeZero N] where
  χ : DirichletCharacter ℂ N
  χ_ne : χ ≠ 1
  χ_sq : χ ^ 2 = 1
  hχ : χ.LFunction 1 = 0

variable {N : ℕ} [NeZero N]

noncomputable section

/-- The associated character is quadratic. -/
lemma BadChar.χ_apply_eq (B : BadChar N) (x : ZMod N) :
    B.χ x = 0 ∨ B.χ x = 1 ∨ B.χ x = -1 := by
  by_cases hx : IsUnit x
  · have hx' : (B.χ x) ^ 2 = 1 := by
      rw [← B.χ.pow_apply' two_ne_zero, B.χ_sq, MulChar.one_apply hx]
    rw [sq_eq_one_iff] at hx'
    tauto
  · simp only [B.χ.map_nonunit hx, true_or]

/-- The auxiliary function `F: s ↦ ζ s * L B.χ s`. -/
def BadChar.F (B : BadChar N) : ℂ → ℂ :=
  Function.update (fun s : ℂ ↦ riemannZeta s * B.χ.LFunction s) 1 (deriv B.χ.LFunction 1)

lemma BadChar.F_differentiableAt_of_ne (B : BadChar N) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ B.F s := by
  apply DifferentiableAt.congr_of_eventuallyEq
  · exact (differentiableAt_riemannZeta hs).mul <| B.χ.differentiableAt_LFunction s (.inl hs)
  · filter_upwards [eventually_ne_nhds hs] with t ht using Function.update_noteq ht ..

lemma BadChar.F_differentiable (B : BadChar N) : Differentiable ℂ B.F := by
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · exact B.F_differentiableAt_of_ne hs
  · apply AnalyticAt.differentiableAt
    apply analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact B.F_differentiableAt_of_ne ht
    -- now reduced to showing *continuity* at s = 1
    let G := Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1
    let H := Function.update (fun s ↦ B.χ.LFunction s / (s - 1)) 1 (deriv B.χ.LFunction 1)
    have : B.F = G * H := by
      ext t
      rcases eq_or_ne t 1 with rfl | ht
      · simp only [F, G, H, Pi.mul_apply, one_mul, Function.update_same]
      · simp only [F, G, H, Pi.mul_apply, Function.update_noteq ht]
        field_simp [sub_ne_zero.mpr ht]
        ring
    rw [this]
    apply ContinuousAt.mul
    · simpa only [G, continuousAt_update_same] using riemannZeta_residue_one
    · have : HasDerivAt B.χ.LFunction (deriv B.χ.LFunction 1) 1 :=
        (B.χ.differentiableAt_LFunction 1 (.inr B.χ_ne)).hasDerivAt
      rw [hasDerivAt_iff_tendsto_slope] at this
      simp only [funext (slope_def_field B.χ.LFunction 1), B.hχ, sub_zero] at this
      rw [Metric.continuousAt_iff']
      intro ε hε
      simp only [Metric.tendsto_nhds, eventually_nhdsWithin_iff] at this
      filter_upwards [this ε hε] with a ha
      rcases eq_or_ne a 1 with rfl | ha'
      · simp only [dist_self, hε]
      · simpa only [H, Function.update_noteq ha', Function.update_same] using ha ha'

/-- The trivial zero at `s = -2` of the zeta function gives that `F (-2) = 0`.
This is used later to obtain a contradction. -/
lemma BadChar.F_neg_two (B : BadChar N) : B.F (-2) = 0 := by
  simp only [BadChar.F]
  have := riemannZeta_neg_two_mul_nat_add_one 0
  rw [Nat.cast_zero, zero_add, mul_one] at this
  rw [Function.update_noteq (mod_cast (by omega : (-2 : ℤ) ≠ 1)), this, zero_mul]

open ArithmeticFunction

/-- The complex-valued arithmetic function whose L-series is `B.F`. -/
def BadChar.e (B : BadChar N) : ArithmeticFunction ℂ := .zeta * toArithmeticFunction (B.χ ·)

lemma BadChar.e_summable (B : BadChar N) {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (B.e ·) s := by
  refine LSeriesSummable_mul (LSeriesSummable_zeta_iff.mpr hs) ?_
  refine (LSeriesSummable_congr s fun {n} hn ↦ ?_).mp <| B.χ.LSeriesSummable_of_one_lt_re hs
  simp only [toArithmeticFunction, coe_mk, hn, ↓reduceIte]

lemma BadChar.abscissa {N : ℕ} [NeZero N] (B : BadChar N) :
    LSeries.abscissaOfAbsConv B.e < (2 : ℝ) := by
  suffices LSeries.abscissaOfAbsConv B.e ≤ (3 / 2 : ℝ) from this.trans_lt <| by norm_cast; norm_num
  convert LSeriesSummable.abscissaOfAbsConv_le (s := (3 / 2 : ℝ)) ?_
  exact B.e_summable (s := (3 / 2 : ℝ))
    (by simp only [ofReal_div, ofReal_ofNat, div_ofNat_re, re_ofNat]; norm_num)

/-- `B.F` agrees with the L-series of `B.e` on `1 < s.re`. -/
lemma BadChar.F_eq_LSeries (B : BadChar N) {s : ℂ} (hs : 1 < s.re) : B.F s = LSeries B.e s := by
  have (n : ℕ) : B.e n = LSeries.convolution (fun _ ↦ (1 : ℂ)) (B.χ ·) n := by
    simp only [e, mul_apply, natCoe_apply, zeta_apply, Nat.cast_ite, Nat.cast_zero, Nat.cast_one,
      ite_mul, zero_mul, one_mul, LSeries.convolution_def]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp only [(Nat.ne_zero_of_mem_divisorsAntidiagonal hi).1, ↓reduceIte, toArithmeticFunction,
      coe_mk, (Nat.ne_zero_of_mem_divisorsAntidiagonal hi).2]
  rw [show (↑B.e : ℕ → ℂ) = fun n : ℕ ↦ B.e n from rfl]
  simp only [this]
  have h₁ : LSeriesSummable (fun _ ↦ (1 : ℂ)) s := by rwa [← Pi.one_def, LSeriesSummable_one_iff]
  have h₂ : LSeriesSummable (B.χ ·) s := ZMod.LSeriesSummable_of_one_lt_re _ hs
  have hs' : s ≠ 1 := fun h ↦ by simp only [h, one_re, lt_self_iff_false] at hs
  rw [LSeries_convolution' h₁ h₂, BadChar.F, Function.update_noteq hs',← Pi.one_def,
    (LSeriesHasSum_one hs).LSeries_eq, DirichletCharacter.LFunction_eq_LSeries _ hs]

lemma BadChar.mult_e (B : BadChar N) : B.e.IsMultiplicative := by
  refine isMultiplicative_zeta.natCast.mul <| IsMultiplicative.iff_ne_zero.mpr ⟨?_, ?_⟩
  · simp only [toArithmeticFunction, coe_mk, one_ne_zero, ↓reduceIte, Nat.cast_one, map_one]
  · intro m n hm hn _
    simp only [toArithmeticFunction, coe_mk, mul_eq_zero, hm, hn, false_or, Nat.cast_mul, map_mul,
      if_false]

-- We use the ordering on `ℂ` given by comparing real parts for fixed imaginary part
open scoped ComplexOrder

lemma BadChar.e_prime_pow (B : BadChar N) {p : ℕ} (hp : p.Prime) (k : ℕ) : 0 ≤ B.e (p ^ k) := by
  simp only [e, toArithmeticFunction, coe_zeta_mul_apply, coe_mk, Nat.sum_divisors_prime_pow hp,
    pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte, Nat.cast_pow, map_pow]
  rcases B.χ_apply_eq p with h | h | h
  · refine Finset.sum_nonneg fun i _ ↦ ?_
    simp only [h, le_refl, pow_nonneg]
  · refine Finset.sum_nonneg fun i _ ↦ ?_
    simp only [h, one_pow, zero_le_one]
  · simp only [h, neg_one_geom_sum]
    split_ifs
    exacts [le_rfl, zero_le_one]

/-- `B.e` takes nonnegative real values. -/
lemma BadChar.e_nonneg (B : BadChar N) (n : ℕ) : 0 ≤ B.e n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · simpa only [B.mult_e.multiplicative_factorization _ hn] using
      Finset.prod_nonneg fun p hp ↦ B.e_prime_pow (Nat.prime_of_mem_primeFactors hp) _

lemma BadChar.e_one_eq_one (B : BadChar N) : B.e 1 = 1 := by
  simp only [e, toArithmeticFunction, mul_apply, Nat.divisorsAntidiagonal_one, Prod.mk_one_one,
    natCoe_apply, zeta_apply, Nat.cast_ite, Nat.cast_zero, Nat.cast_one, coe_mk, mul_ite, mul_zero,
    ite_mul, zero_mul, one_mul, Finset.sum_singleton, Prod.snd_one, one_ne_zero, ↓reduceIte,
    Prod.fst_one, map_one]

lemma BadChar.F_two_pos (B : BadChar N) : 0 < B.F 2 := by
  rw [B.F_eq_LSeries (by norm_num), LSeries]
  refine tsum_pos (B.e_summable (by norm_num)) (fun n ↦ ?_) 1 ?_ ; swap
  · simp only [LSeries.term_def, one_ne_zero, ↓reduceIte, e_one_eq_one, Nat.cast_one, cpow_ofNat,
      one_pow, ne_eq, not_false_eq_true, div_self, zero_lt_one]
  · simp only [LSeries.term_def, cpow_ofNat]
    split
    · simp only [le_refl]
    · exact mul_nonneg (B.e_nonneg n) <| (RCLike.inv_pos_of_pos (by positivity)).le

/-- The goal: bad characters do not exist. -/
theorem BadChar.elim (B : BadChar N) : False := by
  refine (B.F_two_pos.trans_le <|
    B.F_neg_two ▸
      B.F_differentiable.apply_le_of_differentiable_of_iteratedDeriv_alternating
        (fun n _ ↦ ?_) (by norm_num)).false
  have hs : IsOpen {s : ℂ | 1 < s.re} := by refine isOpen_lt ?_ ?_ <;> fun_prop
  convert B.e.iteratedDeriv_LSeries_alternating B.e_nonneg B.abscissa n using 2
  convert iteratedDeriv_eq_on_open n hs ⟨2, ?_⟩ fun _ ↦ B.F_eq_LSeries
  simp only [Set.mem_setOf_eq, re_ofNat, Nat.one_lt_ofNat]

end

section final

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- If `χ` is a nontrivial quadratic Dirichlet character, then `L(χ, 1) ≠ 0`. -/
theorem LFunction_at_one_ne_zero_of_quadratic {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1) (χ_ne : χ ≠ 1) :
    χ.LFunction 1 ≠ 0 := by
  intro hL
  let B : BadChar N := {χ := χ, χ_sq := hχ, hχ := hL, χ_ne := χ_ne}
  exact B.elim

end DirichletCharacter

end final
