import Mathlib


example {C E : Type*} [IsROrC C] [NormedAddCommGroup E] [NormedSpace ℂ E] :
    NormedSpace ℝ E := inferInstance
