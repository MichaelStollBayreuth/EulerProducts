import Mathlib.Topology.Algebra.InfiniteSum.Basic

section tsum

open BigOperators

variable {α β : Type*} [AddCommMonoid α] [TopologicalSpace α]

-- these should go into `Mathlib.Topology.Algebra.InfiniteSum.Basic`
open Set in
lemma tsum_eq_tsum_diff [T2Space α] {f : β → α} (s t : Set β) (hf₀ : ∀ b ∈ t, f b = 0) :
    ∑' a : s, f a = ∑' a : (s \ t : Set β), f a := by
  simp_rw [tsum_subtype]
  refine tsum_congr fun b' ↦ ?_
  by_cases hs : b' ∈ s \ t
  · rw [indicator_of_mem hs f, indicator_of_mem (mem_of_mem_diff hs) f]
  · rw [indicator_of_not_mem hs f]
    rw [mem_diff, not_and, not_not_mem] at hs
    by_cases h₁ : b' ∈ s
    · simpa [indicator_of_mem h₁] using hf₀ b' <| hs h₁
    · exact indicator_of_not_mem h₁ f

open Set in
/-- If `f b = 0`, then the sum over all `f a` is the same as the sum over `f a` for `a ≠ b`. -/
lemma tsum_eq_tsum_diff_singleton [T2Space α] {f : β → α} (s : Set β) {b : β} (hf₀ : f b = 0) :
    ∑' a : s, f a = ∑' a : (s \ {b} : Set β), f a :=
  tsum_eq_tsum_diff s {b} fun _ ha ↦ ha ▸ hf₀

lemma hasSum_singleton (m : β) (f : β → α) : HasSum (({m} : Set β).restrict f) (f m) := by
  convert_to HasSum (fun x : ({m} : Set β) ↦ f x) (f (⟨m, rfl⟩ : ({m} : Set β)))
  exact hasSum_single (α := α) _ <| fun m' h ↦ False.elim <| h <| Subtype.ext m'.2

end tsum
