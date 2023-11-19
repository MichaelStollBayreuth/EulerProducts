import Mathlib

example : ContinuousOn (fun t : ℝ ↦ t) (Set.Icc 0 1) := by
  continuity
  sorry
