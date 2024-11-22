import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
### Auxiliary stuff
-/

section auxiliary

lemma Summable.prod_of_nonneg_of_summable_tsum {β γ : Type*} {f : β × γ → ℝ} (h₁ : ∀ x, 0 ≤ f x)
    (h₂ : ∀ b, Summable fun c ↦ f (b, c)) (h₃ : Summable fun b ↦ ∑' c, f (b, c)) :
    Summable f := by
  sorry

lemma Real.inv_rpow_eq_rpow_neg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x⁻¹ ^ y = x ^ (-y) := by
  rw [Real.rpow_neg hx]
  exact inv_rpow hx y

end auxiliary

open scoped LSeries.notation

open Complex

/-!
### The L-series of Λ restricted to a residue class
-/

open LSeries DirichletCharacter

namespace ArithmeticFunction.vonMangoldt

variable {q : ℕ} (a : ZMod q)

/-- The von Mangoldt function restricted to the residue class `a` mod `q`. -/
noncomputable abbrev residueClass : ℕ → ℝ :=
  {n : ℕ | (n : ZMod q) = a}.indicator (vonMangoldt ·)

lemma residueClass_nonneg (n : ℕ) : 0 ≤ residueClass a n :=
  Set.indicator_apply_nonneg fun _ ↦ vonMangoldt_nonneg

lemma residueClass_le (n : ℕ) : residueClass a n ≤ vonMangoldt n :=
  Set.indicator_apply_le' (fun _ ↦ le_rfl) (fun _ ↦ vonMangoldt_nonneg)

lemma residueClass_apply_zero : residueClass a 0 = 0 := by
  simp only [Set.indicator_apply_eq_zero, Set.mem_setOf_eq, Nat.cast_zero, map_zero, ofReal_zero,
    implies_true]

lemma abscissaOfAbsConv_residueClass_le_one :
    abscissaOfAbsConv ↗(vonMangoldt.residueClass a) ≤ 1 := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ ?_
  unfold LSeriesSummable
  have := LSeriesSummable_vonMangoldt <| show 1 < (y : ℂ).re by simp only [ofReal_re, hy]
  convert this.indicator {n : ℕ | (n : ZMod q) = a}
  ext1 n
  by_cases hn : (n : ZMod q) = a
  · simp +contextual only [term, Set.indicator, Set.mem_setOf_eq, hn, ↓reduceIte, apply_ite,
      ite_self]
  · simp +contextual only [term, Set.mem_setOf_eq, hn, not_false_eq_true, Set.indicator_of_not_mem,
      ofReal_zero, zero_div, ite_self]

variable [NeZero q] {a}

/-- We can express `ArithmeticFunction.vonMangoldt.residueClass` as a linear combination
of twists of the von Mangoldt function with Dirichlet charaters. -/
lemma residueClass_apply (ha : IsUnit a) (n : ℕ) :
    residueClass a n =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ n * vonMangoldt n := by
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp +contextual only [residueClass, Set.indicator_apply, Set.mem_setOf_eq, apply_ite,
    ofReal_zero, mul_zero, ← Finset.sum_mul, sum_char_inv_mul_char_eq ℂ ha n, eq_comm (a := a),
    ite_mul, zero_mul, ↓reduceIte, ite_self]

/-- We can express `ArithmeticFunction.vonMangoldt.residueClass` as a linear combination
of twists of the von Mangoldt function with Dirichlet charaters. -/
lemma residueClass_eq (ha : IsUnit a) :
    ↗(residueClass a) = (q.totient : ℂ)⁻¹ •
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ • (fun n : ℕ ↦ χ n * vonMangoldt n) := by
  ext1 n
  simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, ← mul_assoc]
    using residueClass_apply ha n

/-- The L-series of the von Mangoldt function restricted to the prime residue class `a` mod `q`
is a linear combination of logarithmic derivatives of L-functions of the Dirichlet characters
mod `q` (on `re s > 1`). -/
lemma LSeries_residueClass_eq (ha : IsUnit a) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(residueClass a) s =
      -(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ *
        (deriv (LFunction χ) s / LFunction χ s) := by
  simp only [deriv_LFunction_eq_deriv_LSeries _ hs, LFunction_eq_LSeries _ hs, neg_mul, ← mul_neg,
    ← Finset.sum_neg_distrib, ← neg_div, ← LSeries_twist_vonMangoldt_eq _ hs]
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp_rw [← LSeries_smul,
    ← LSeries_sum <| fun χ _ ↦ (LSeriesSummable_twist_vonMangoldt χ hs).smul _]
  refine LSeries_congr s fun {n} _ ↦ ?_
  simp only [Pi.smul_apply, residueClass_apply ha, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel_of_invertible, one_mul, Finset.sum_apply, Pi.mul_apply]

-- PR up to here

omit [NeZero q] in
variable (a) in
open Nat.Primes in
lemma summable_vonMangoldt_residueClass_non_primes :
    Summable fun n : ℕ ↦ (if n.Prime then 0 else residueClass a n) / n := by
  have hp₀ (p : Nat.Primes) : 0 < (p : ℝ)⁻¹ := by
    have := p.prop.pos
    positivity
  have hp₁ (p : Nat.Primes) : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one₀ <| mod_cast p.prop.pos]
    exact_mod_cast p.prop.one_lt
  have hp₂ (p : Nat.Primes) : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr (hp₁ p)
  have hp₃ (p : Nat.Primes) : (1 - (p : ℝ)⁻¹)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (hp₂ p) zero_lt_two, le_sub_comm]
    norm_num
    rw [one_div, inv_le_inv₀ (mod_cast p.prop.pos) zero_lt_two]
    exact_mod_cast p.prop.two_le
  let F₀ (n : ℕ) : ℝ := (if n.Prime then 0 else vonMangoldt n) / n
  have hnonneg (n : ℕ) : 0 ≤ (if n.Prime then 0 else residueClass a n) / n := by
    have := residueClass_nonneg a n
    positivity
  have hleF₀ (n : ℕ) : (if n.Prime then 0 else residueClass a n) / n ≤ F₀ n := by
    simp only [F₀]
    refine div_le_div_of_nonneg_right ?_ n.cast_nonneg
    split_ifs with hn
    · exact le_rfl
    · exact residueClass_le a n
  suffices Summable F₀ from this.of_nonneg_of_le hnonneg hleF₀
  have hF₀ (p : Nat.Primes) : F₀ p.val = 0 := by
    simp only [p.prop, ↓reduceIte, zero_div, F₀]
  let F (n : {n : ℕ // IsPrimePow n}) : ℝ := F₀ n.val
  have hFF₀ : F = F₀ ∘ Subtype.val := rfl
  suffices Summable F by
    refine (summable_subtype_iff_indicator.mp (hFF₀ ▸ this)).congr
      fun n ↦ Set.indicator_apply_eq_self.mpr fun (hn : ¬ IsPrimePow n) ↦ ?_
    simp +contextual only [div_eq_zero_iff, ite_eq_left_iff, vonMangoldt_eq_zero_iff, hn,
      not_false_eq_true, implies_true, Nat.cast_eq_zero, true_or, F₀]
  let F' (pk : Nat.Primes × ℕ) : ℝ := F₀ (pk.1 ^ (pk.2 + 1))
  have hFF' : F = F' ∘ ⇑prodNatEquiv.symm := by
    refine (Equiv.eq_comp_symm prodNatEquiv F F').mpr ?_
    ext1 n
    simp only [Function.comp_apply, F, F']
    congr
  suffices Summable F' by
    have := (Nat.Primes.prodNatEquiv.symm.summable_iff (f := F')).mpr this
    rwa [← hFF'] at this
  let F'' (pk : Nat.Primes × ℕ) : ℝ := F₀ (pk.1 ^ (pk.2 + 2))
  have hF'₀ (p : Nat.Primes) : F' (p, 0) = 0 := by
    simp only [zero_add, pow_one, hF₀, F']
  have hF'₁ : F'' = F' ∘ (Prod.map _root_.id (· + 1)) := by
    ext1
    simp only [Function.comp_apply, Prod.map_fst, id_eq, Prod.map_snd, F'', F']
  suffices Summable F'' by
    rw [hF'₁] at this
    refine (Function.Injective.summable_iff ?_ fun u hu ↦ ?_).mp this
    · exact Function.Injective.prodMap (fun ⦃a₁ a₂⦄ a ↦ a) <| add_left_injective 1
    · simp only [Set.range_prod_map, Set.range_id, Set.mem_prod, Set.mem_univ, Set.mem_range,
        Nat.exists_add_one_eq, true_and, not_lt, nonpos_iff_eq_zero] at hu
      rw [← hF'₀ u.1, ← hu]
  have hF'' (p : Nat.Primes) (k : ℕ) : F'' (p, k) ≤ 2 * (p : ℝ)⁻¹ ^ (k + 3 / 2 : ℝ) := by
    calc _
      _ = Real.log p * (p : ℝ)⁻¹ ^ (k + 2) := by
        simp only [div_eq_mul_inv, ite_mul, zero_mul, le_add_iff_nonneg_left, zero_le,
          Nat.Prime.not_prime_pow, ↓reduceIte, Nat.cast_pow, F'', F₀]
        rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime p.prop, inv_pow (p : ℝ) (k + 2)]
      _ ≤ (p: ℝ) ^ (1 / 2 : ℝ) / (1 / 2) * (p : ℝ)⁻¹ ^ (k + 2) := by
        gcongr
        exact Real.log_le_rpow_div (by positivity) one_half_pos
      _ = 2 * (p : ℝ)⁻¹ ^ (-1 / 2 : ℝ) * (p : ℝ)⁻¹ ^ (k + 2) := by
        congr
        rw [← div_mul, div_one, mul_comm, Real.inv_rpow p.val.cast_nonneg,
          ← Real.rpow_neg p.val.cast_nonneg, neg_div, neg_neg]
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_natCast,
          ← Real.rpow_add <| by have := p.prop.pos; positivity, Nat.cast_add, Nat.cast_two,
          add_comm, add_assoc]
        norm_num
  suffices Summable fun (pk : Nat.Primes × ℕ) ↦ 2 * (pk.1 : ℝ)⁻¹ ^ (pk.2 + 3 / 2 : ℝ) by
    refine this.of_nonneg_of_le (fun pk ↦ ?_) (fun pk ↦ hF'' pk.1 pk.2)
    simp only [F'', F₀]
    have := vonMangoldt_nonneg (n := (pk.1 : ℕ) ^ (pk.2 + 2))
    positivity
  refine Summable.mul_left _ ?_
  conv => enter [1, pk]; rw [Real.rpow_add <| hp₀ pk.1, Real.rpow_natCast]
  refine Summable.prod_of_nonneg_of_summable_tsum (fun _ ↦ by positivity) (fun p ↦ ?_) ?_
  · dsimp only
    exact Summable.mul_right _ <| summable_geometric_of_lt_one (hp₀ p).le (hp₁ p)
  · dsimp only
    conv => enter [1, p]; rw [tsum_mul_right, tsum_geometric_of_lt_one (hp₀ p).le (hp₁ p)]
    suffices Summable fun p : Nat.Primes ↦ 2 * (p : ℝ)⁻¹ ^ (3 / 2 : ℝ) by
      refine this.of_nonneg_of_le (fun p ↦ ?_) (fun p ↦ ?_)
      · have := hp₂ p
        positivity
      · gcongr
        exact hp₃ p
    refine Summable.mul_left _ ?_
    conv => enter [1, p]; rw [Real.inv_rpow_eq_rpow_neg p.val.cast_nonneg]
    exact Nat.Primes.summable_rpow.mpr <| by norm_num


end ArithmeticFunction.vonMangoldt


namespace DirichletsThm

open ArithmeticFunction vonMangoldt

variable {q : ℕ} [NeZero q] (a : ZMod q)

open Classical in
/-- The auxiliary function used, e.g., with the Wiener-Ikehara Theorem to prove
Dirichlet's Theorem. On `re s > 1`, it agrees with the L-series of the von Mangoldt
function restricted to the residue class `a : ZMod q` minus the principal part
`(q.totient)⁻¹/(s-1)` of the pole at `s = 1`; see `DirichletsThm.auxFun_prop`. -/
noncomputable
abbrev auxFun (s : ℂ) : ℂ :=
  (q.totient : ℂ)⁻¹ * (-deriv (LFunctionTrivChar₁ q) s / LFunctionTrivChar₁ q s -
    ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)), χ a⁻¹ * deriv (LFunction χ) s / LFunction χ s)

lemma continuousOn_auxFun' :
    ContinuousOn (auxFun a) {s | s = 1 ∨ ∀ χ : DirichletCharacter ℂ q, LFunction χ s ≠ 0} := by
  rw [show auxFun a = fun s ↦ _ from rfl]
  simp only [auxFun, sub_eq_add_neg]
  refine continuousOn_const.mul <| ContinuousOn.add ?_ ?_
  · refine (continuousOn_neg_logDeriv_LFunctionTrivChar₁ q).mono fun s hs ↦ ?_
    have := LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ q) (s := s)
    simp only [ne_eq, Set.mem_setOf_eq] at hs
    tauto
  · simp only [← Finset.sum_neg_distrib, mul_div_assoc, ← mul_neg, ← neg_div]
    refine continuousOn_finset_sum _ fun χ hχ ↦ continuousOn_const.mul ?_
    replace hχ : χ ≠ 1 := by simpa only [ne_eq, Finset.mem_compl, Finset.mem_singleton] using hχ
    refine (continuousOn_neg_logDeriv_LFunction_of_nontriv hχ).mono fun s hs ↦ ?_
    simp only [ne_eq, Set.mem_setOf_eq] at hs
    rcases hs with rfl | hs
    · simp only [ne_eq, Set.mem_setOf_eq, one_re, le_refl,
        LFunction_ne_zero_of_one_le_re χ (.inl hχ), not_false_eq_true]
    · exact hs χ

/-- The L-series of the von Mangoldt function restricted to the prime residue class `a` mod `q`
is continuous on `re s ≥ 1` except for a single pole at `s = 1` with residue `(q.totient)⁻¹`.
The statement as given here in terms auf `DirichletsThm.auxFun` is equivalent. -/
lemma continuousOn_auxFun : ContinuousOn (auxFun a) {s | 1 ≤ s.re} := by
  refine (continuousOn_auxFun' a).mono fun s hs ↦ ?_
  rcases eq_or_ne s 1 with rfl | hs₁
  · simp only [ne_eq, Set.mem_setOf_eq, true_or]
  · simp only [ne_eq, Set.mem_setOf_eq, hs₁, false_or]
    exact fun χ ↦ LFunction_ne_zero_of_one_le_re χ (.inr hs₁) <| Set.mem_setOf.mp hs

--


variable {a}

/-- The auxiliary function agrees on `re s > 1` with the L-series of the von Mangoldt function
restricted to the residue class `a : ZMod q` minus the principal part `(q.totient)⁻¹/(s-1)`
of its pole at `s = 1`. -/
lemma auxFun_prop (ha : IsUnit a) :
    Set.EqOn (auxFun a)
      (fun s ↦ L ↗(vonMangoldt.residueClass a) s - (q.totient : ℂ)⁻¹ / (s - 1))
      {s | 1 < s.re} := by
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  simp only [vonMangoldt.LSeries_residueClass_eq ha hs, auxFun]
  rw [neg_div, ← neg_add', mul_neg, ← neg_mul,  div_eq_mul_one_div (q.totient : ℂ)⁻¹,
    sub_eq_add_neg, ← neg_mul, ← mul_add]
  congrm (_ * ?_)
  -- this should be easier, but `IsUnit.inv ha` does not work here
  have ha' : IsUnit a⁻¹ := isUnit_of_dvd_one ⟨a, (ZMod.inv_mul_of_unit a ha).symm⟩
  classical -- for `Fintype.sum_eq_add_sum_compl`
  rw [Fintype.sum_eq_add_sum_compl 1, MulChar.one_apply ha', one_mul, add_right_comm]
  simp only [mul_div_assoc]
  congrm (?_ + _)
  have hs₁ : s ≠ 1 := fun h ↦ ((h ▸ hs).trans_eq one_re).false
  rw [deriv_LFunctionTrivChar₁_apply_of_ne_one _ hs₁, LFunctionTrivChar₁,
    Function.update_noteq hs₁]
  simp only [LFunctionTrivChar]
  rw [add_div, mul_div_mul_left _ _ (sub_ne_zero_of_ne hs₁)]
  conv_lhs => enter [2, 1]; rw [← mul_one (LFunction ..)]
  rw [mul_comm _ 1, mul_div_mul_right _ _ <| LFunction_ne_zero_of_one_le_re 1 (.inr hs₁) hs.le]

lemma auxFun_real (ha : IsUnit a) {x : ℝ} (hx : 1 < x) : auxFun a x = (auxFun a x).re := by
  replace hx : (x : ℂ) ∈ {s | 1 < s.re} := by
    simp only [Set.mem_setOf_eq, ofReal_re, hx]
  rw [auxFun_prop ha hx]
  simp only [sub_re, ofReal_sub]
  congr 1
  · rw [LSeries, re_tsum ?_]
    · push_cast
      refine tsum_congr fun n ↦ ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [term_zero, zero_re, ofReal_zero]
      · simp only [ne_eq, hn, not_false_eq_true, term_of_ne_zero, ← ofReal_natCast n,
          ← ofReal_cpow n.cast_nonneg]
        norm_cast
    · refine LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
      refine (vonMangoldt.abscissaOfAbsConv_residueClass_le_one a).trans_lt ?_
      simp only [Set.mem_setOf_eq, ofReal_re] at hx ⊢
      norm_cast
  · rw [show (q.totient : ℂ) = (q.totient : ℝ) from rfl]
    norm_cast


open Topology Filter in
lemma LSeries_vonMangoldt_residueClass_tendsto_atTop (ha : IsUnit a) :
    Tendsto (fun x : ℝ ↦ ∑' n, vonMangoldt.residueClass a n / (n : ℝ) ^ x)
      (𝓝[>] 1) atTop := by
  have H {x : ℝ} (hx : 1 < x) :
      ∑' n, vonMangoldt.residueClass a n / (n : ℝ) ^ x =
        (auxFun a x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
    apply_fun ((↑) : ℝ → ℂ) using ofReal_injective
    push_cast
    simp_rw [ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast]
    convert_to L ↗(vonMangoldt.residueClass a) x = _
    · simp only [div_eq_mul_inv, LSeries, term]
      refine tsum_congr fun n ↦ ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [vonMangoldt.residueClass_apply_zero, ofReal_zero, Nat.cast_zero, zero_mul,
          ↓reduceIte]
      · simp only [hn, ↓reduceIte]
    · rw [← auxFun_real ha hx, auxFun_prop ha <| Set.mem_setOf.mpr (ofReal_re x ▸ hx)]
      simp only [sub_add_cancel]
  refine Tendsto.congr' (eventuallyEq_nhdsWithin_of_eqOn fun ⦃x⦄ hx ↦ H hx).symm ?_
  clear H
  have : ContinuousWithinAt (fun x : ℝ ↦ (auxFun a x).re) {x | 1 < x} 1 := by
    refine continuous_re.continuousWithinAt.comp (t := (Set.univ : Set ℂ)) ?_ fun ⦃_⦄ _ ↦ trivial
    change ContinuousWithinAt ((auxFun a) ∘ ofReal) ..
    refine ContinuousWithinAt.comp (t := {s | 1 < s.re}) ?_ continuous_ofReal.continuousWithinAt
      fun ⦃_⦄ a ↦ a
    refine ContinuousWithinAt.mono (t := {s | 1 ≤ s.re}) ?_
       fun s hs ↦ Set.mem_setOf.mpr <| (Set.mem_setOf.mp hs).le
    exact ContinuousOn.continuousWithinAt (continuousOn_auxFun a) <| by
      simp only [ofReal_one, Set.mem_setOf_eq, one_re, le_refl]
  refine tendsto_atTop_add_left_of_le' (𝓝[>] 1) ((auxFun a 1).re - 1) ?_ ?_
  · exact Tendsto.eventually_const_le (ofReal_one ▸ sub_one_lt _) this.tendsto
  · conv => enter [1, x]; rw [div_eq_mul_inv]
    refine Tendsto.comp (y := atTop) ?_ ?_
    · refine tendsto_atTop_atTop.mpr fun x ↦ ⟨q.totient * x, fun y hy ↦ ?_⟩
      exact (le_inv_mul_iff₀' <| mod_cast q.totient.pos_of_neZero).mpr hy
    · refine tendsto_inv_zero_atTop.comp (y := 𝓝[>] 0) ?_
      convert ContinuousWithinAt.tendsto_nhdsWithin_image ?_
      · exact (sub_self _).symm
      · simp only [Set.image_sub_const_Ioi, sub_self]
      · exact (continuous_add_right (-1)).continuousWithinAt

open vonMangoldt Filter Topology in
lemma not_summable_vonMangoldt_residueClass_prime_div (ha : IsUnit a) :
    ¬ Summable fun n : ℕ ↦ (if n.Prime then residueClass a n else 0) / n := by
  intro H
  have key : Summable fun n : ℕ ↦ residueClass a n / n := by
    convert (summable_vonMangoldt_residueClass_non_primes a).add H using 2 with n
    simp only [← add_div, ite_add_ite, zero_add, add_zero, ite_self]
  let C := ∑' n, residueClass a n / n
  have H₁ {x : ℝ} (hx : 1 < x) : ∑' n, residueClass a n / (n : ℝ) ^ x ≤ C := by
    refine tsum_le_tsum (fun n ↦ ?_) ?_ key
    · rcases n.eq_zero_or_pos with rfl | hn
      · simp only [Nat.cast_zero, Real.zero_rpow (by linarith), div_zero, le_refl]
      · refine div_le_div_of_nonneg_left (residueClass_nonneg a _) (mod_cast hn) ?_
        conv_lhs => rw [← Real.rpow_one n]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_cast) hx.le
    · exact summable_real_of_abscissaOfAbsConv_lt <|
        (vonMangoldt.abscissaOfAbsConv_residueClass_le_one a).trans_lt <| mod_cast hx
  have H₂ := tendsto_atTop.mp (LSeries_vonMangoldt_residueClass_tendsto_atTop ha) (C + 1)
  rcases (H₂.and self_mem_nhdsWithin).exists with ⟨x, hx, h'x⟩
  exact (lt_add_one C).not_le (hx.trans <| H₁ h'x)

end DirichletsThm

/-!
### Derivation of Dirichlet's Theorem (without Wiener-Ikehara)
-/

section DirichletsTheorem

open ArithmeticFunction DirichletsThm in
/-- **Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positive
integer and `a : ZMod q` is a unit, then there are infintely many prime numbers `p`
such that `(p : ZMod q) = a`. -/
theorem dirchlet_primes_in_arith_progression {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ∀ n : ℕ, ∃ p > n, p.Prime ∧ (p : ZMod q) = a := by
  by_contra! H
  obtain ⟨N, hN⟩ := H
  refine not_summable_vonMangoldt_residueClass_prime_div ha <| summable_of_finite_support ?_
  refine Set.Finite.subset (Set.finite_le_nat N) fun n hn ↦ ?_
  simp only [Function.support_div, Set.mem_inter_iff, Function.mem_support, ne_eq, ite_eq_right_iff,
    Set.indicator_apply_eq_zero, Set.mem_setOf_eq, Classical.not_imp, Nat.cast_eq_zero] at hn
  simp only [Set.mem_setOf_eq]
  contrapose! hn
  exact fun H ↦ (hN n hn.gt H.1 H.2.1).elim

end DirichletsTheorem

/-!
### Statement of a version of the Wiener-Ikehara Theorem
-/

open Filter Topology Nat ArithmeticFunction in
/-- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/
def WienerIkeharaTheorem : Prop :=
  ∀ {f : ℕ → ℝ} {A : ℝ} {F : ℂ → ℂ}, (∀ n, 0 ≤ f n) →
    Set.EqOn F (fun s ↦ L ↗f s - A / (s - 1)) {s | 1 < s.re} →
    ContinuousOn F {s | 1 ≤ s.re} →
    Tendsto (fun N : ℕ ↦ ((Finset.range N).sum f) / N) atTop (𝓝 A)

/-!
### Derivation of the Prime Number Theorem and Dirichlet's Theorem from the Wiener-Ikehara Theorem
-/

open Filter ArithmeticFunction Topology DirichletsThm

/--  The *Wiener-Ikehara Theorem* implies *Dirichlet's Theorem* in the form that
`ψ x ∼ q.totient⁻¹ * x`, where `ψ x = ∑ n < x ∧ n ≡ a mod q, Λ n`
and `Λ` is the von Mangoldt function.

This is Theorem 2 in Section 2 of PNT+ (but using the `WIT` stub defined here). -/
theorem Dirichlet_vonMangoldt (WIT : WienerIkeharaTheorem) {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) :
    Tendsto (fun N : ℕ ↦ (((Finset.range N).filter (fun n : ℕ ↦ (n : ZMod q) = a)).sum Λ) / N)
      atTop (𝓝 <| (q.totient : ℝ)⁻¹) := by
  classical
  have H N : ((Finset.range N).filter (fun n : ℕ ↦ (n : ZMod q) = a)).sum Λ =
      (Finset.range N).sum ({n : ℕ | (n : ZMod q) = a}.indicator Λ) :=
    (Finset.sum_indicator_eq_sum_filter _ _ (fun _ ↦ {n : ℕ | n = a}) _).symm
  simp only [H]
  refine WIT (F := auxFun a) (fun n ↦ ?_) ?_ ?_
  · exact Set.indicator_apply_nonneg fun _ ↦ vonMangoldt_nonneg
  · convert auxFun_prop ha with s
    push_cast
    rfl
  · exact continuousOn_auxFun a

/-- The *Wiener-Ikehara Theorem* implies the *Prime Number Theorem* in the form that
`ψ x ∼ x`, where `ψ x = ∑ n < x, Λ n` and `Λ` is the von Mangoldt function. -/
theorem PNT_vonMangoldt (WIT : WienerIkeharaTheorem) :
    Tendsto (fun N : ℕ ↦ ((Finset.range N).sum Λ) / N) atTop (𝓝 1) := by
  convert Dirichlet_vonMangoldt WIT (q := 1) (a := 1) isUnit_one with n
  · exact (Finset.filter_true_of_mem fun _ _ ↦ Subsingleton.eq_one _).symm
  · simp only [Nat.totient_one, Nat.cast_one, inv_one]
