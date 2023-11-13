import Mathlib.Tactic
-- import Mathlib.Analysis.PSeries

variable (x : ℝ)

#check x ^ 2 -- hover over the `2` in the infoview
             -- with `import Mathlib.Analysis.PSeries`, it is `2 : ℝ`, else `2 : ℕ`. 

-- example (a b c d x y : ℝ) (h₁ : x ∈ Set.Ioc a b) (h₂ : y ∈ Set.Ioc c d) :
--     x + y ∈ Set.Ioc (a + c) (b + d) := by
--   refine Set.mem_Ioc.mpr ?_
--   rw [Set.mem_Ioc] at h₁ h₂
--   constructor <;> linarith (config := {splitHypotheses := true})
