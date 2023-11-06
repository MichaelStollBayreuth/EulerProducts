import EulerProducts.Basic

namespace EulerProduct

open scoped Topology

open BigOperators

variable {F : Type*} [NormedField F] [CompleteSpace F] {f : ℕ → F}
variable (hsum : Summable (‖f ·‖))
variable (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)

-- Can simplify when #8194 is merged
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

lemma norm_tsum_factorsBelow_sub_tsum_lt {ε : ℝ} (εpos : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ‖(∑' m : N.factorsBelow, f m) - (∑' m : ℕ, f m)‖ < ε := by
  conv =>
    enter [1, N₀, N]
    rw [← tsum_subtype_add_tsum_subtype_compl (summable_of_summable_norm hsum) N.factorsBelow,
        ← sub_sub, sub_self, zero_sub, norm_neg, tsum_nat_eq_tsum_diff_zero (N.factorsBelow)ᶜ hf₀]
  obtain ⟨N₀, hN₀⟩ := tail_estimate' hsum <| half_pos εpos
  refine ⟨N₀, fun N hN₁ ↦ (hN₀ _ ?_).trans_lt <| half_lt_self εpos⟩
  exact (Nat.factorsBelow_compl _).trans fun n ↦ hN₁.le.trans

open Nat in
/-- This is the key lemma that relates a finite product over primes to a partial
infinite sum. -/
lemma prod_of_tsum_geometric (N : ℕ) :
    ∏ p in N.primesBelow, ∑' (n : ℕ), f (p ^ n) = ∑' m : N.factorsBelow, f m := by
  induction' N with N ih
  · rw [factorsBelow_zero, primesBelow_zero]
    simp [hf₁]
  · rw [primesBelow_succ]
    split_ifs with hN
    · rw [Finset.prod_insert (not_mem_primesBelow N), ih, tsum_mul_tsum_of_summable_norm]
      · convert Equiv.tsum_eq (equivProdNatFactorsBelow hN) ?_ with em
        · rw [equivProdNatFactorsBelow_apply]
          exact (hmul <| Coprime.pow_left em.1 <| hN.factorsBelow_coprime
            <| Subtype.mem em.2).symm
        · infer_instance
      · exact hsum.comp_injective <| Nat.pow_right_injective hN.one_lt
      · exact Summable.subtype hsum N.factorsBelow
    · rw [ih]
      exact tsum_congr_subtype f (factorsBelow_succ hN).symm

open Filter Nat in
/-- The *Euler Product* for multiplicative (on coprime arguments) functions.
If `f : ℕ → F`, where `F` is a complete normed field, `f 0 = 0`,
`f 1 = 1`, `f` is multiplicative on coprime arguments,
and `‖f ·‖` is summable, then `∏' p : {p : ℕ | p.Prime}, ∑' e, f (p ^ e) = ∑' n, f n`.
Since there are no infinite products yet in Mathlib, we state it in the form of
convergence of finite partial products. -/
theorem euler_product :
    Tendsto (fun n : ℕ ↦ ∏ p in primesBelow n, ∑' e, f (p ^ e)) atTop (𝓝 (∑' n, f n)) := by
  rw [Metric.tendsto_nhds]
  intro ε εpos
  simp only [Finset.mem_range, eventually_atTop, ge_iff_le]
  obtain ⟨N₀, hN₀⟩ := norm_tsum_factorsBelow_sub_tsum_lt hsum hf₀ εpos
  use N₀
  convert hN₀ using 3 with m
  rw [dist_eq_norm]
  congr 2
  exact prod_of_tsum_geometric hsum hf₁ hmul m

open Filter Nat in
/-- The *Euler Product* for completely multiplicative functions.
If `f : ℕ →*₀ F`, where `F` is a complete normed field
and `‖f ·‖` is summable, then `∏' p : {p : ℕ | p.Prime}, (1 - f p)⁻¹ = ∑' n, f n`.
Since there are no infinite products yet in Mathlib, we state it in the form of
convergence of finite partial products. -/
theorem euler_product_multiplicative {f : ℕ →*₀ F} (hsum : Summable fun x => ‖f x‖) :
    Tendsto (fun n : ℕ ↦ ∏ p in primesBelow n, (1 - f p)⁻¹) atTop (𝓝 (∑' n, f n)) := by
  have hf₀ : f 0 = 0 := MonoidWithZeroHom.map_zero f
  have hf₁ : f 1 = 1 := MonoidWithZeroHom.map_one f
  have hmul {m n} (_ : Nat.Coprime m n) : f (m * n) = f m * f n := MonoidWithZeroHom.map_mul f m n
  convert euler_product hsum hf₀ hf₁ hmul with N p hN
  simp_rw [map_pow]
  refine (tsum_geometric_of_norm_lt_1 <| summable_geometric_iff_norm_lt_1.mp ?_).symm
  refine summable_of_summable_norm ?_
  convert hsum.comp_injective <| Nat.pow_right_injective (prime_of_mem_primesBelow hN).one_lt
  simp

end EulerProduct
