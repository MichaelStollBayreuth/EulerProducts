import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Nat.Squarefree
-- import Mathlib.Data.IsROrC.Basic -- transitive import
import Mathlib.Analysis.PSeries

/-!
# The sum of the reciprocals of the primes diverges

We show that the sum of `1/p`, where `p` runs through the prime numbers, diverges.
We follow the elementary proof by Erdős that is reproduced in the "BOOK of proofs".
There are two versions of the main result: `not_summable_one_div_on_primes`, which
expresses the sum as a sub-sum of the harmonic series, and `Nat.Primes.not_summable_one_div`,
which writes it as a sum over `Nat.Primes`. We also show that the sum of `p^r` for `r : ℝ`
converges if and only if `r < -1`; see `Nat.Primes.summable_rpow`.
-/

namespace Nat

/-- There are exactly `⌊N/n⌋` positive multiples of `n` that are `≤ N`.
Compare `Nat.card_multiples` for a "shifted-by-one" version. -/
--  Data/Nat/Factorization/Basic.lean
lemma card_multiples' (N n : ℕ) :
    ((Finset.range N.succ).filter (fun k ↦ k ≠ 0 ∧ n ∣ k)).card = N / n := by
  induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.range_succ, Finset.filter_insert]
        by_cases h : n ∣ N.succ
        · simp [h, succ_div_of_dvd, ih]
        · simp [h, succ_div_of_not_dvd, ih]

-- The following should go into NumberTheory/SmoothNumbers.lean
lemma mem_primesBelow {k n : ℕ} :
    n ∈ primesBelow k ↔ n < k ∧ n.Prime := by simp [primesBelow]

instance (k : ℕ) : DecidablePred (· ∈ smoothNumbers k) :=
  inferInstanceAs <| DecidablePred fun x ↦ x ∈ {m | m ≠ 0 ∧ ∀ p ∈ factors m, p < k}

lemma mem_smoothNumbers_of_dvd {n m k : ℕ} (h : m ∈ smoothNumbers n) (h' : k ∣ m) (hk : k ≠ 0) :
    k ∈ smoothNumbers n := by
  rw [mem_smoothNumbers] at h ⊢
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨hk, fun p hp ↦ h₂ p ?_⟩
  rw [mem_factors <| by assumption] at hp ⊢
  exact ⟨hp.1, hp.2.trans h'⟩

lemma mem_smoothNumbers_iff_forall_le {n m : ℕ} :
    m ∈ smoothNumbers n ↔ m ≠ 0 ∧ ∀ p ≤ m, p.Prime → p ∣ m → p < n := by
  rw [mem_smoothNumbers']
  refine ⟨fun H ↦ ⟨fun h ↦ ?_, fun p _ ↦ H p⟩,
          fun ⟨H₀, H₁⟩ ↦ fun p hp₁ hp₂ ↦ H₁ p (Nat.le_of_dvd (Nat.pos_of_ne_zero H₀) hp₂) hp₁ hp₂⟩
  subst h
  obtain ⟨p, hp₁, hp₂⟩ := exists_infinite_primes n
  exact not_le_of_lt (H p hp₂ p.dvd_zero) hp₁

lemma ne_zero_of_mem_smoothNumbers {n m : ℕ} (h : m ∈ smoothNumbers n) : m ≠ 0 :=
  (mem_smoothNumbers_iff_forall_le.mp h).1

/-- The `k`-smooth numbers up to and including `N` as a `Finset` -/
abbrev smoothNumbersUpTo (N k : ℕ) : Finset ℕ :=
    (Finset.range N.succ).filter (· ∈ smoothNumbers k)

lemma mem_smoothNumbersUpTo {N k n : ℕ} :
    n ∈ smoothNumbersUpTo N k ↔ n ≤ N ∧ n ∈ smoothNumbers k := by
  simp [smoothNumbersUpTo, lt_succ]

/-- The positive non-`k`-smooth numbers up to and including `N` as a `Finset` -/
abbrev roughNumbersUpTo (N k : ℕ) : Finset ℕ :=
    (Finset.range N.succ).filter (fun n ↦ n ≠ 0 ∧ n ∉ smoothNumbers k)

lemma smoothNumbersUpTo_card_add_roughNumbersUpTo_card (N k : ℕ) :
    (smoothNumbersUpTo N k).card + (roughNumbersUpTo N k).card = N := by
  rw [← Finset.card_union_eq <| Finset.disjoint_filter.mpr fun n _ hn₂ h ↦ h.2 hn₂,
    Finset.filter_union_right]
  suffices : Finset.card (Finset.filter (fun x ↦ x ≠ 0) (Finset.range (succ N))) = N
  · convert this with n
    have hn : n ∈ smoothNumbers k → n ≠ 0 := fun h ↦ (mem_smoothNumbers.mp h).1
    tauto
  · rw [Finset.filter_ne', Finset.card_erase_of_mem <| Finset.mem_range_succ_iff.mpr <| zero_le N]
    simp

/-- A `k`-smooth number can be written as a square times a product of distinct primes `< k`. -/
-- This needs Mathlib.Data.Nat.Squarefree
lemma eq_prod_primes_mul_sq_of_mem_smoothNumbers {n k : ℕ} (h : n ∈ smoothNumbers k) :
    ∃ s ∈ k.primesBelow.powerset, ∃ m, n = m ^ 2 * (s.prod id) := by
  obtain ⟨l, m, H₁, H₂⟩ := sq_mul_squarefree n
  have hl : l ∈ smoothNumbers k :=
    mem_smoothNumbers_of_dvd h (Dvd.intro_left (m ^ 2) H₁) <| Squarefree.ne_zero H₂
  have := List.toFinset_eq H₂.nodup_factors
  refine ⟨l.factors.toFinset, ?_,  m, ?_⟩
  · simp only [toFinset_factors, Finset.mem_powerset]
    refine fun p hp ↦ mem_primesBelow.mpr ⟨?_, (mem_primeFactors.mp hp).1⟩
    rw [mem_primeFactors] at hp
    exact mem_smoothNumbers'.mp hl p hp.1 hp.2.1
  rw [← H₁]
  congr
  simp only [toFinset_factors]
  exact (prod_primeFactors_of_squarefree H₂).symm

/-- The set of `k`-smooth numbers `≤ N` is contained in the set of numbers of the form `m^2 * P`,
where `m ≤ √N` and `P` is a product of distinct primes `< k`. -/
lemma smoothNumbersUpTo_subset_image (N k : ℕ) :
    smoothNumbersUpTo N k ⊆ Finset.image (fun (s, m) ↦ m ^ 2 * (s.prod id))
      (k.primesBelow.powerset ×ˢ (Finset.range N.sqrt.succ).erase 0) := by
  intro n hn
  obtain ⟨hn₁, hn₂⟩ := mem_smoothNumbersUpTo.mp hn
  obtain ⟨s, hs, m, hm⟩ := eq_prod_primes_mul_sq_of_mem_smoothNumbers hn₂
  simp only [id_eq, Finset.mem_range, zero_lt_succ, not_true_eq_false, Finset.mem_image,
    Finset.mem_product, Finset.mem_powerset, Finset.mem_erase, Prod.exists]
  refine ⟨s, m, ⟨Finset.mem_powerset.mp hs, ?_, ?_⟩, hm.symm⟩
  · have := hm ▸ ne_zero_of_mem_smoothNumbers hn₂
    simp only [ne_eq, _root_.mul_eq_zero, zero_lt_two, pow_eq_zero_iff, not_or] at this
    exact this.1
  · rw [lt_succ, le_sqrt']
    refine LE.le.trans ?_ (hm ▸ hn₁)
    nth_rw 1 [← mul_one (m ^ 2)]
    exact mul_le_mul_left' (Finset.one_le_prod' fun p hp ↦
      (prime_of_mem_primesBelow <| Finset.mem_powerset.mp hs hp).one_lt.le) _

/-- The cardinality of the set of `k`-smooth numbers `≤ N` is bounded by `2^π(k-1) * √N`. -/
lemma smoothNumbersUpTo_card_le (N k : ℕ) :
    (smoothNumbersUpTo N k).card ≤ 2 ^ k.primesBelow.card * N.sqrt := by
  convert (Finset.card_le_of_subset <| smoothNumbersUpTo_subset_image N k).trans <|
     Finset.card_image_le
  simp

/-- The set of `k`-rough numbers `≤ N` can be written as the union of the sets of multiples `≤ N`
of primes `k ≤ p ≤ N`. -/
lemma roughNumbersUpTo_eq_biUnion (N k) :
    roughNumbersUpTo N k =
      (N.succ.primesBelow \ k.primesBelow).biUnion
        fun p ↦ (Finset.range N.succ).filter (fun m ↦ m ≠ 0 ∧ p ∣ m) := by
  ext
  simp only [roughNumbersUpTo, mem_smoothNumbers_iff_forall_le, not_and, not_forall,
    not_lt, exists_prop, exists_and_left, Finset.mem_range, not_exists, not_le, Finset.mem_filter,
    Finset.filter_congr_decidable, Finset.mem_biUnion, Finset.mem_sdiff, mem_primesBelow]
  refine ⟨fun ⟨H₁, H₂, H₃⟩ ↦ ?_,
          fun ⟨p, ⟨⟨_, hp₂⟩, hp₃⟩, hp₄, hp₅, hp₆⟩ ↦
              ⟨hp₄, hp₅, fun _ ↦ ⟨p, Nat.le_of_dvd (Nat.pos_of_ne_zero hp₅) hp₆, hp₂, hp₆, ?_⟩⟩⟩
  · obtain ⟨p, hp₁, hp₂, hp₃, hp₄⟩ := H₃ H₂
    exact ⟨p, ⟨⟨hp₁.trans_lt H₁, hp₂⟩, fun h₁ _ ↦ (h₁.trans_le hp₄).false.elim⟩, H₁, H₂, hp₃⟩
  · exact Nat.not_lt.mp <| hp₃.mt <| not_not.mpr hp₂

/-- The cardinality of the set of `k`-rough numbers `≤ N` is bounded by the sum of `⌊N/p⌋`
over the primes `k ≤ p ≤ N`. -/
lemma roughNumbersUpTo_card_le (N k : ℕ) :
    (roughNumbersUpTo N k).card ≤ (N.succ.primesBelow \ k.primesBelow).sum (fun p ↦ N / p) := by
  rw [roughNumbersUpTo_eq_biUnion]
  exact Finset.card_biUnion_le.trans <| Finset.sum_le_sum fun p _ ↦ (card_multiples' N p).le

/-- The cardinality of the set of `k`-rough numbers `≤ N` is bounded by `N` times the sum
of `1/p` over the primes `k ≤ p ≤ N`. -/
-- This needs Mathlib.Data.IsROrC.Basic
lemma roughNumbersUpTo_card_le' (N k : ℕ) :
    (roughNumbersUpTo N k).card ≤
      N * (N.succ.primesBelow \ k.primesBelow).sum (fun p ↦ (1 : ℝ) / p) := by
  simp_rw [Finset.mul_sum, mul_one_div]
  refine (Nat.cast_le.mpr <| roughNumbersUpTo_card_le N k).trans ?_
  push_cast
  exact Finset.sum_le_sum fun n _ ↦ cast_div_le

end Nat

open Set Nat

/-- The sum over primes `k ≤ p ≤ 4^(π(k-1)+1)` over `1/p` (as a real number) is at least `1/2`. -/
lemma sum_one_div_primes_ge (k : ℕ) :
    ((4 ^ (k.primesBelow.card + 1)).succ.primesBelow \ k.primesBelow).sum
      (fun p ↦ (1 / p : ℝ)) ≥ 1 / 2 := by
  set m : ℕ := 2 ^ k.primesBelow.card
  set N₀ : ℕ := 2 * m ^ 2 with hN₀
  let S : ℝ := ((2 * N₀).succ.primesBelow \ k.primesBelow).sum (fun p ↦ (1 / p : ℝ))
  suffices : 2 * N₀ ≤ m * (2 * N₀).sqrt + 2 * N₀ * S
  · rw [ge_iff_le]
    rw [hN₀, ← mul_assoc, ← pow_two 2, ← mul_pow, sqrt_eq', ← sub_le_iff_le_add'] at this
    push_cast at this
    ring_nf at this
    simp_rw [← one_div] at this
    conv at this in (_ * 2 ≤ _) => enter [1, 2]; rw [show (2 : ℝ) = 4 * (1 / 2) by norm_num]
    rw [← mul_assoc, mul_comm _ (1 / 2 : ℝ), mul_assoc (Finset.sum ..),
      _root_.mul_le_mul_right <| by positivity] at this
    convert this using 5
    rw [show 4 = 2 ^ 2 by norm_num, Nat.pow_right_comm]
    ring
  calc (2 * N₀ : ℝ)
    _ = ((2 * N₀).smoothNumbersUpTo k).card + ((2 * N₀).roughNumbersUpTo k).card := by
        exact_mod_cast ((2 * N₀).smoothNumbersUpTo_card_add_roughNumbersUpTo_card k).symm
    _ ≤ m * (2 * N₀).sqrt + ((2 * N₀).roughNumbersUpTo k).card := by
        exact_mod_cast Nat.add_le_add_right ((2 * N₀).smoothNumbersUpTo_card_le k) _
    _ ≤ m * (2 * N₀).sqrt + 2 * N₀ * S := add_le_add_left ?_ _
  exact_mod_cast roughNumbersUpTo_card_le' (2 * N₀) k

/-- The sum over the reciprocals of the primes diverges. -/
theorem not_summable_one_div_on_primes :
    ¬ Summable (indicator {p | p.Prime} (fun n : ℕ ↦ (1 : ℝ) / n)) := by
  intro h
  obtain ⟨k, hk⟩ := h.nat_tsum_vanishing (Iio_mem_nhds one_half_pos : Iio (1 / 2 : ℝ) ∈ nhds 0)
  replace hk := hk {p | Nat.Prime p ∧ k ≤ p} <| by simp
  rw [tsum_subtype, indicator_indicator, inter_eq_left.mpr <| fun n hn ↦ hn.1, mem_Iio] at hk
  have h' : Summable (indicator {p | Nat.Prime p ∧ k ≤ p} fun n ↦ (1 : ℝ) / n)
  · convert h.indicator {n : ℕ | k ≤ n} using 1
    simp only [indicator_indicator, inter_comm]
    rfl
  refine ((sum_one_div_primes_ge k).le.trans_lt <| LE.le.trans_lt ?_ hk).false
  convert sum_le_tsum (primesBelow ((4 ^ (k.primesBelow.card + 1)).succ) \ primesBelow k)
    (fun n _ ↦ indicator_nonneg (fun p _ ↦ by positivity) _) h' using 1
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have H : n ∈ {p | Nat.Prime p ∧ k ≤ p}
  · simp only [Finset.mem_sdiff, mem_setOf_eq] at hn ⊢
    obtain ⟨hn₁, hn₂⟩ := hn
    refine ⟨prime_of_mem_primesBelow hn₁, ?_⟩
    rw [mem_primesBelow, not_and_or, not_lt] at hn₂
    exact hn₂.resolve_right <| not_not.mpr <| prime_of_mem_primesBelow hn₁
  simp only [indicator_of_mem H]

/-- The sum over the reciprocals of the primes diverges. -/
theorem Nat.Primes.not_summable_one_div : ¬ Summable (fun p : Nat.Primes ↦ (1 / p : ℝ)) := by
  convert summable_subtype_iff_indicator.mp.mt not_summable_one_div_on_primes

-- The following needs Mathlib.Analysis.PSeries

/-- The series over `p^r` for primes `p` converges if and only if `r < -1`. -/
theorem Nat.Primes.summable_rpow {r : ℝ} :
    Summable (fun p : Nat.Primes ↦ (p : ℝ) ^ r) ↔ r < -1 := by
  by_cases h : r < -1
  · -- case `r < -1`
    simp only [h, iff_true]
    exact (Real.summable_nat_rpow.mpr h).subtype _
  · -- case `-1 ≤ r`
    simp only [h, iff_false]
    refine fun H ↦ Nat.Primes.not_summable_one_div <| H.of_nonneg_of_le (fun _ ↦ by positivity) ?_
    intro p
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.prop.one_lt.le) <| not_lt.mp h
