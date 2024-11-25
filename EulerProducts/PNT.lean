import Mathlib.NumberTheory.LSeries.PrimesInAP


open Complex ArithmeticFunction Filter Topology

/-!
### Statement of a version of the Wiener-Ikehara Theorem
-/

open scoped LSeries.notation

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
  refine WIT (F := vonMangoldt.LfunctionResidueClassAux a) (fun n ↦ ?_) ?_ ?_
  · exact Set.indicator_apply_nonneg fun _ ↦ vonMangoldt_nonneg
  · convert vonMangoldt.eqOn_LfunctionResidueClassAux ha with s
    push_cast
    rfl
  · exact vonMangoldt.continuousOn_LfunctionResidueClassAux a

/-- The *Wiener-Ikehara Theorem* implies the *Prime Number Theorem* in the form that
`ψ x ∼ x`, where `ψ x = ∑ n < x, Λ n` and `Λ` is the von Mangoldt function. -/
theorem PNT_vonMangoldt (WIT : WienerIkeharaTheorem) :
    Tendsto (fun N : ℕ ↦ ((Finset.range N).sum Λ) / N) atTop (𝓝 1) := by
  convert Dirichlet_vonMangoldt WIT (q := 1) (a := 1) isUnit_one with n
  · exact (Finset.filter_true_of_mem fun _ _ ↦ Subsingleton.eq_one _).symm
  · simp only [Nat.totient_one, Nat.cast_one, inv_one]
