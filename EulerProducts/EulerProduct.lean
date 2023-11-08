import EulerProducts.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Field.InfiniteSum

namespace EulerProduct

open scoped Topology

open BigOperators

-- We work with series indexed by the natural numbers
-- and with terms in a complete normed field `F`.
variable {F : Type*} [NormedField F] [CompleteSpace F] {f : ℕ → F}

-- We assume that `f` is *multiplicative* in the sense of arithmetic functions,
-- i.e., multiplicative on coprime elements. For convenience, we also assume that `f 0 = 0`.
-- The condition `f 1 = 1` is then equivalent to `f 1 ≠ 0`, but more convenient to use.
variable (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)

lemma map_prime_pow_mul {p : ℕ} (hp : p.Prime) (e : ℕ) {m : p.smoothNumbers} :
    f (p ^ e * m) = f (p ^ e) * f m :=
  hmul <| Nat.Coprime.pow_left _ <| hp.smoothNumbers_coprime <| Subtype.mem m

open Nat in
/-- This relates a finite product over primes to an infinite sum over smooth numbers. -/
lemma summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ ↦ ‖f (p ^ n)‖)) (N : ℕ) :
    Summable (fun m : N.smoothNumbers ↦ ‖f m‖) ∧
      HasSum (fun m : N.smoothNumbers ↦ f m) (∏ p in N.primesBelow, ∑' (n : ℕ), f (p ^ n)) := by
  induction' N with N ih
  · rw [smoothNumbers_zero, primesBelow_zero, Finset.prod_empty]
    exact ⟨Set.Finite.summable (Set.finite_singleton 1) (‖f ·‖), hf₁ ▸ hasSum_singleton 1 f⟩
  · rw [primesBelow_succ]
    split_ifs with hN
    · constructor
      · simp_rw [← (equivProdNatSmoothNumbers hN).summable_iff, Function.comp_def,
                 equivProdNatSmoothNumbers_apply', map_prime_pow_mul hmul hN, norm_mul]
        apply summable_mul_of_summable_norm (f := fun (x : ℕ) ↦ ‖f (N ^ x)‖)
          (g := fun (x : N.smoothNumbers) ↦ ‖f x.val‖) <;>
          simp_rw [norm_norm]
        exacts [hsum hN, ih.1]
      · simp_rw [Finset.prod_insert (not_mem_primesBelow N),
                 ← (equivProdNatSmoothNumbers hN).hasSum_iff, Function.comp_def,
                 equivProdNatSmoothNumbers_apply', map_prime_pow_mul hmul hN]
        -- below, `(α := F)` seems to be necessary to avoid a time-out
        apply HasSum.mul (α := F) (Summable.hasSum <| summable_of_summable_norm <| hsum hN) ih.2
        -- `exact summable_mul_of_summable_norm (hsum hN) ih.1` gives a time-out
        have := summable_mul_of_summable_norm (hsum hN) ih.1
        exact this
    · rwa [smoothNumbers_succ hN]

open Nat in
/-- Given a (completely) multiplicative function `f : ℕ → F`, where `F` is a normed field,
such that `‖f p‖ < 1` for all primes `p`, we can express the sum of `f n` over all `N`-smooth
positive integers `n` as a product of `(1 - f p)⁻¹` over the primes `p < N`. At the same time,
we show that the sum involved converges absolutely. -/
lemma summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric {f : ℕ →* F}
    (h : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1) (N : ℕ) :
    Summable (fun m : N.smoothNumbers ↦ ‖f m‖) ∧
      HasSum (fun m : N.smoothNumbers ↦ f m) (∏ p in N.primesBelow, (1 - f p)⁻¹) := by
  have hf₁ : f 1 = 1 := f.map_one
  have hmul {m n} (_ : Nat.Coprime m n) := f.map_mul m n
  convert summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hf₁ hmul ?_ N with M hM <;>
    simp_rw [map_pow]
  · exact (tsum_geometric_of_norm_lt_1 <| h <| prime_of_mem_primesBelow hM).symm
  · intro p hp
    simp_rw [norm_pow]
    exact summable_geometric_iff_norm_lt_1.mpr <| (norm_norm (f p)).symm ▸ h hp

-- We now assume in addition that `f` is norm-summable.
variable (hsum : Summable (‖f ·‖))

/-- A version of `summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum` in terms of the
value of the series. -/
lemma prod_primesBelow_tsum_eq_tsum_smoothNumbers (N : ℕ) :
    ∏ p in N.primesBelow, ∑' (n : ℕ), f (p ^ n) = ∑' m : N.smoothNumbers, f m :=
  (summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hf₁ hmul
    (fun hp ↦ hsum.comp_injective <| Nat.pow_right_injective hp.one_lt) _).2.tsum_eq.symm

/-- A version of `summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric` in terms of
the value of the series. -/
lemma prod_primesBelow_geometric_eq_tsum_smoothNumbers {f : ℕ →* F}
    (h : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1) (N : ℕ) :
    ∏ p in N.primesBelow, (1 - f p)⁻¹ = ∑' m : N.smoothNumbers, f m :=
  (summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric h N).2.tsum_eq.symm

-- Can simplify when #8194 is merged (also below where it is used: `ε/2 → ε`)
lemma tail_estimate' {ε : ℝ} (εpos : 0 < ε) :
     ∃ N : ℕ, ∀ s ⊆ {n | N ≤ n}, ‖∑' m : s, f m‖ ≤ ε := by
  obtain ⟨t, ht⟩ := summable_iff_vanishing.mp hsum _ (Metric.closedBall_mem_nhds 0 εpos)
  use if emp : t.Nonempty then t.max' emp + 1 else 0
  refine fun s hs ↦ (norm_tsum_le_tsum_norm <| hsum.subtype _).trans ?_
  refine tsum_le_of_sum_le (hsum.subtype _) fun s' ↦ (le_abs_self _).trans ?_
  rw [← Finset.sum_subtype_map_embedding (g := fun i ↦ ‖f i‖) fun _ _ ↦ rfl]
  simp_rw [mem_closedBall_zero_iff, Real.norm_eq_abs, Finset.disjoint_left] at ht
  refine ht _ fun n hns' hnt ↦ ?_
  obtain ⟨⟨m, hms⟩, -, rfl⟩ := Finset.mem_map.mp hns'
  have := hs hms
  split_ifs at this with h
  · exact (t.le_max' _ hnt).not_lt ((Nat.lt_succ_self _).trans_le this)
  · exact h ⟨m, hnt⟩

lemma norm_tsum_smoothNumbers_sub_tsum_lt {ε : ℝ} (εpos : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ‖(∑' m : N.smoothNumbers, f m) - (∑' m : ℕ, f m)‖ < ε := by
  conv =>
    enter [1, N₀, N]
    rw [← tsum_subtype_add_tsum_subtype_compl (summable_of_summable_norm hsum) N.smoothNumbers,
        ← sub_sub, sub_self, zero_sub, norm_neg,
        tsum_eq_tsum_diff_singleton (N.smoothNumbers)ᶜ 0 hf₀]
  obtain ⟨N₀, hN₀⟩ := tail_estimate' hsum <| half_pos εpos
  refine ⟨N₀, fun N hN₁ ↦ (hN₀ _ ?_).trans_lt <| half_lt_self εpos⟩
  exact (Nat.smoothNumbers_compl _).trans fun n ↦ hN₁.le.trans

open Filter Nat in
/-- The *Euler Product* for multiplicative (on coprime arguments) functions.
If `f : ℕ → F`, where `F` is a complete normed field, `f 0 = 0`,
`f 1 = 1`, `f` is multiplicative on coprime arguments,
and `‖f ·‖` is summable, then `∏' p : {p : ℕ | p.Prime}, ∑' e, f (p ^ e) = ∑' n, f n`.
Since there are no infinite products yet in Mathlib, we state it in the form of
convergence of finite partial products. -/
-- TODO: Change to use `∏'` once infinite products are in Mathlib
theorem euler_product :
    Tendsto (fun n : ℕ ↦ ∏ p in primesBelow n, ∑' e, f (p ^ e)) atTop (𝓝 (∑' n, f n)) := by
  rw [Metric.tendsto_nhds]
  intro ε εpos
  simp only [Finset.mem_range, eventually_atTop, ge_iff_le]
  obtain ⟨N₀, hN₀⟩ := norm_tsum_smoothNumbers_sub_tsum_lt hf₀ hsum εpos
  use N₀
  convert hN₀ using 3 with m
  rw [dist_eq_norm]
  congr 2
  exact prod_primesBelow_tsum_eq_tsum_smoothNumbers hf₁ hmul hsum m

open Filter Nat in
/-- The *Euler Product* for completely multiplicative functions.
If `f : ℕ →*₀ F`, where `F` is a complete normed field
and `‖f ·‖` is summable, then `∏' p : {p : ℕ | p.Prime}, (1 - f p)⁻¹ = ∑' n, f n`.
Since there are no infinite products yet in Mathlib, we state it in the form of
convergence of finite partial products. -/
-- TODO: Change to use `∏'` once infinite products are in Mathlib
theorem euler_product_multiplicative {f : ℕ →*₀ F} (hsum : Summable fun x => ‖f x‖) :
    Tendsto (fun n : ℕ ↦ ∏ p in primesBelow n, (1 - f p)⁻¹) atTop (𝓝 (∑' n, f n)) := by
  convert euler_product f.map_zero f.map_one (fun {m n} _ ↦ f.map_mul m n) hsum with N p hN
  simp_rw [map_pow]
  refine (tsum_geometric_of_norm_lt_1 <| summable_geometric_iff_norm_lt_1.mp ?_).symm
  refine summable_of_summable_norm ?_
  convert hsum.comp_injective <| Nat.pow_right_injective (prime_of_mem_primesBelow hN).one_lt
  simp only [norm_pow, Function.comp_apply, map_pow]

end EulerProduct
