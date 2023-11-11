import EulerProducts.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Field.InfiniteSum

set_option autoImplicit false

namespace EulerProduct

open scoped Topology

open BigOperators

-- We work with series indexed by the natural numbers
-- and with terms in a complete normed field `F`.
variable {F : Type*} [NormedField F] [CompleteSpace F] {f : ℕ → F}

-- We assume that `f` is *multiplicative* in the sense of arithmetic functions,
-- i.e., multiplicative on coprime elements.
-- The condition `f 1 = 1` is then equivalent to `f 1 ≠ 0`, but more convenient to use.
variable (hf₁ : f 1 = 1) (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)

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
        convert summable_mul_of_summable_norm (hsum hN) ih.1
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
  have hmul {m n} (_ : Nat.Coprime m n) := f.map_mul m n
  convert summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum f.map_one hmul ?_ N with M hM <;>
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

lemma _root_.Summable.norm_lt_one {f : ℕ →* F} (hsum : Summable f) {p : ℕ} (hp : 1 < p) :
    ‖f p‖ < 1 := by
  refine summable_geometric_iff_norm_lt_1.mp ?_
  simp_rw [← map_pow]
  exact hsum.comp_injective <| Nat.pow_right_injective hp

/-- A version of `summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric` in terms of
the value of the series. -/
lemma prod_primesBelow_geometric_eq_tsum_smoothNumbers {f : ℕ →* F} (hsum : Summable f) (N : ℕ) :
    ∏ p in N.primesBelow, (1 - f p)⁻¹ = ∑' m : N.smoothNumbers, f m := by
  refine (summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric ?_ N).2.tsum_eq.symm
  exact fun {_} hp ↦ hsum.norm_lt_one hp.one_lt

/-- We need the following statement that says that summing over `N`-smooth numbers
for large enough `N` gets us arbitrarily close to the sum over all natural numbers
(assuming `f` is norm-summable and `f 0 = 0`; the latter since `0` is not smooth). -/
lemma norm_tsum_smoothNumbers_sub_tsum_lt (hsum : Summable f) (hf₀ : f 0 = 0) {ε : ℝ} (εpos : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ‖(∑' m : ℕ, f m) - (∑' m : N.smoothNumbers, f m)‖ < ε := by
  obtain ⟨N₀, hN₀⟩ :=
    summable_iff_nat_tsum_vanishing.mp hsum (Metric.ball 0 ε) <| Metric.ball_mem_nhds 0 εpos
  simp_rw [mem_ball_zero_iff] at hN₀
  refine ⟨N₀, fun N hN₁ ↦ ?_⟩
  convert hN₀ _ <| (Nat.smoothNumbers_compl N).trans <| fun m hm ↦ hN₁.le.trans hm
  simp_rw [← tsum_subtype_add_tsum_subtype_compl hsum N.smoothNumbers,
    add_sub_cancel', tsum_eq_tsum_diff_singleton (N.smoothNumbers)ᶜ hf₀]

open Filter Nat in
/-- The *Euler Product* for multiplicative (on coprime arguments) functions.
If `f : ℕ → F`, where `F` is a complete normed field, `f 0 = 0`,
`f 1 = 1`, `f` is multiplicative on coprime arguments,
and `‖f ·‖` is summable, then `∏' p : {p : ℕ | p.Prime}, ∑' e, f (p ^ e) = ∑' n, f n`.
Since there are no infinite products yet in Mathlib, we state it in the form of
convergence of finite partial products. -/
-- TODO: Change to use `∏'` once infinite products are in Mathlib
theorem euler_product (hf₀ : f 0 = 0) :
    Tendsto (fun n : ℕ ↦ ∏ p in primesBelow n, ∑' e, f (p ^ e)) atTop (𝓝 (∑' n, f n)) := by
  rw [Metric.tendsto_nhds]
  intro ε εpos
  simp only [Finset.mem_range, eventually_atTop, ge_iff_le]
  have hsum' := summable_of_summable_norm hsum
  obtain ⟨N₀, hN₀⟩ := norm_tsum_smoothNumbers_sub_tsum_lt hsum' hf₀ εpos
  use N₀
  convert hN₀ using 3 with m
  rw [dist_eq_norm, norm_sub_rev]
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
  convert euler_product f.map_one (fun {m n} _ ↦ f.map_mul m n) hsum f.map_zero with N p hN
  simp_rw [map_pow]
  refine (tsum_geometric_of_norm_lt_1 <| summable_geometric_iff_norm_lt_1.mp ?_).symm
  refine summable_of_summable_norm ?_
  convert hsum.comp_injective <| Nat.pow_right_injective (prime_of_mem_primesBelow hN).one_lt
  simp only [norm_pow, Function.comp_apply, map_pow]

end EulerProduct
