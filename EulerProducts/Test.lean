import Mathlib.NumberTheory.ZetaFunction

noncomputable section

open MeasureTheory Set Filter Asymptotics TopologicalSpace Real Asymptotics Topology
open Complex

/-- The residue of `Λ(s)` at `s = 1` is equal to 1. -/
lemma riemannCompletedZeta_residue_one :
    Tendsto (fun s ↦ (s - 1) * riemannCompletedZeta s) (𝓝[≠] 1) (𝓝 1) := by
  unfold riemannCompletedZeta
  simp_rw [mul_add, mul_sub, (by simp : 𝓝 (1 : ℂ) = 𝓝 (0 - 0 + 1))]
  refine ((Tendsto.sub ?_ ?_).mono_left nhdsWithin_le_nhds).add ?_
  · rw [(by simp : 𝓝 (0 : ℂ) = 𝓝 ((1 - 1) * riemannCompletedZeta₀ 1))]
    apply ((continuous_sub_right _).mul differentiable_completed_zeta₀.continuous).tendsto
  · rw [(by simp : 𝓝 (0 : ℂ) = 𝓝 ((1 - 1) * (1 / 1)))]
    exact (((continuous_sub_right _).continuousAt).mul <|
      continuousAt_const.div continuousAt_id one_ne_zero)
  · refine (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).congr' ?_
    refine eventually_nhdsWithin_of_forall (fun s hs ↦ ?_)
    simpa using (div_self <| sub_ne_zero_of_ne <| Set.mem_compl_singleton_iff.mpr hs).symm

/-- The residue of `ζ(s)` at `s = 1` is equal to 1. -/
lemma riemannZeta_residue_one : Tendsto (fun s ↦ (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) := by
  suffices : Tendsto (fun s => (s - 1) *
      (π ^ (s / 2) * riemannCompletedZeta s / Gamma (s / 2))) (𝓝[≠] 1) (𝓝 1)
  · refine this.congr' <| (eventually_ne_nhdsWithin one_ne_zero).mp (eventually_of_forall ?_)
    intro x hx
    simp [riemannZeta_def, Function.update_noteq hx]
  have h0 : Tendsto (fun s ↦ π ^ (s / 2) : ℂ → ℂ) (𝓝[≠] 1) (𝓝 (π ^ (1 / 2 : ℂ)))
  · refine ((continuousAt_id.div_const _).const_cpow ?_).tendsto.mono_left nhdsWithin_le_nhds
    exact Or.inl <| ofReal_ne_zero.mpr pi_ne_zero
  have h1 : Tendsto (fun s : ℂ ↦ 1 / Gamma (s / 2)) (𝓝[≠] 1) (𝓝 (1 / π ^ (1 / 2 : ℂ)))
  · rw [← Complex.Gamma_one_half_eq]
    refine (Continuous.tendsto ?_ _).mono_left nhdsWithin_le_nhds
    simpa using differentiable_one_div_Gamma.continuous.comp (continuous_id.div_const _)
  convert (riemannCompletedZeta_residue_one.mul h0).mul h1 using 2 with s
  · ring
  · have := fun h ↦ ofReal_ne_zero.mpr pi_ne_zero ((cpow_eq_zero_iff _ (1 / 2)).mp h).1
    field_simp

/-
private lemma dist_one (m : ℕ) : dist (m : ℂ) 1 < 1 ↔ m = 1 := by
  refine ⟨fun H ↦ ?_, fun H ↦ by simp [H]⟩
  rwa [dist_eq, ← Int.cast_one, ← Int.cast_Nat_cast, ← Int.cast_sub, ← int_cast_abs, ← Int.cast_abs,
      ← Int.cast_one (R := ℝ), Int.cast_lt, Int.abs_lt_one_iff, sub_eq_zero, ← Nat.cast_one,
      Int.ofNat_inj] at H

private abbrev S : Set ℂ := {z | ∃ n : ℕ, z = n}ᶜ

open Filter Topology Metric in
private lemma nhdsWithinS_eq_nhdsNe : 𝓝[≠] 1 = 𝓝[S] 1 := by
  refine nhdsWithin_eq_nhdsWithin (mem_ball_self zero_lt_one) (isOpen_ball (x := (1 : ℂ))) ?_
  ext z
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff, mem_ball,
    Set.mem_setOf_eq, not_exists, and_congr_left_iff]
  intro hz
  rw [← not_exists, not_iff_not]
  refine ⟨fun H ↦ ⟨1, by simp [H]⟩, fun ⟨n, hn⟩ ↦ ?_⟩
  simp only [hn, dist_one] at hz
  simp [hn, hz]

lemma riemannZeta_functionalEquation :
    ∀ s ∈ S, ζ s = 2 ^ s * π ^ (s - 1) * Γ (1 - s) * sin (π * s / 2) * ζ (1 - s) := by
  intro s hs
  convert riemannZeta_one_sub (s := 1 - s) ?_ ?_ using 5 <;> try simp only [sub_sub_self 1 s]
  · simp only [neg_sub]
  · intro n hn
    have hs₁ : s = 1 + n := by linear_combination -hn
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists] at hs
    exact hs (1 + n) <| by exact_mod_cast hs₁
  · simp only [ne_eq, sub_eq_self]
    rintro rfl
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists] at hs
    exact hs 0 <| by exact_mod_cast rfl

open Topology Filter Metric in
lemma tendsto_sub_one_mul_Gamma_one_sub_nhds_one :
    Tendsto (fun x ↦ (x - 1) * Γ (1 - x)) (𝓝[S] 1) (𝓝 (-1)) := by
  rw [← nhdsWithinS_eq_nhdsNe]
  conv =>
    enter [1, x]
    rw [show (x - 1) * Γ (1 - x) = - ((1 - x) * Γ (1 - x)) by ring]
  refine (tendsto_self_mul_Gamma_nhds_zero.comp ?_).neg
  convert tendsto_map
  sorry
  -- simpa using (Homeomorph.addLeft (1 : ℂ)).embedding.map_nhdsWithin_eq ({0}ᶜ) 0
    -- rw [show (0 : ℂ) = 1 - 1 by ring]

private lemma continuousAtProduct :
    ContinuousAt (fun x ↦ 2 ^ x * ↑π ^ (x - 1) * sin (↑π * x / 2) * ζ (1 - x)) 1 := by
  -- ideally, this would just be `continuity`
  refine (((Continuous.const_cpow (by continuity) <| Or.inl two_ne_zero).mul <|
      Continuous.const_cpow (by continuity) <| Or.inl <| by exact_mod_cast Real.pi_ne_zero).mul <|
      by continuity).continuousAt.mul <|
    ContinuousAt.comp ?_ <| Continuous.continuousAt <| by continuity
  simp only [sub_self]
  exact DifferentiableAt.continuousAt <| differentiableAt_riemannZeta zero_ne_one

open Topology Filter Metric in
lemma zeta_residue_at_one : Tendsto (fun s ↦ (s - 1) * ζ s) (𝓝[≠] 1) (𝓝 1) := by
  rw [nhdsWithinS_eq_nhdsNe]
  have : ∀ s ∈ S, (s - 1) * Γ (1 - s) * (2 ^ s * π ^ (s - 1) * sin (π * s / 2) * ζ (1 - s)) =
            (s - 1) * ζ s
  · intro s hs
    rw [riemannZeta_functionalEquation s hs]
    ring
  refine tendsto_nhdsWithin_congr this ?_
  rw [show (𝓝 (1 : ℂ)) = (𝓝 ((-1) * (-1))) by simp]
  convert tendsto_sub_one_mul_Gamma_one_sub_nhds_one.mul <|
    tendsto_nhdsWithin_of_tendsto_nhds continuousAtProduct.tendsto using 1
  simp [riemannZeta_zero, mul_div_cancel' (-1 : ℂ) two_ne_zero]

-/
