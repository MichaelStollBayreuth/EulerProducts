import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Euler products for L-series
-/

open Complex

open scoped LSeries.notation

namespace LSeries

-- Use this to golf `LSeries.term_convolution`
lemma term_mul_aux (a b : ℂ) (m n : ℕ) (s : ℂ) :
    (a / m ^ s) * (b / n ^ s) = a * b / (m * n) ^ s := by
  rw [mul_comm_div, div_div, ← mul_div_assoc, mul_comm (m : ℂ), natCast_mul_natCast_cpow]

lemma term_mul {f₁ f₂ f : ℕ → ℂ} {m n : ℕ} (h : f (m * n) = f₁ m * f₂ n) (s : ℂ) :
    term f s (m * n) = term f₁ s m * term f₂ s n := by
  rcases eq_or_ne (m * n) 0 with H | H
  · rcases mul_eq_zero.mp H with rfl | rfl <;> simp only [term_zero, mul_zero, zero_mul]
  · obtain ⟨hm, hn⟩ := mul_ne_zero_iff.mp H
    simp only [ne_eq, H, not_false_eq_true, term_of_ne_zero, Nat.cast_mul, hm, hn, h, term_mul_aux]

/-- Weak multiplicativity of `f : ℕ → ℂ` is inherited by the terms of its L-series. -/
lemma term_multiplicative {f : ℕ → ℂ} (hf : ∀ {m n}, m.Coprime n → f (m * n) = f m * f n) (s : ℂ)
    {m n : ℕ} (hcop : m.Coprime n) :
    term f s (m * n) = term f s m * term f s n :=
  term_mul (hf hcop) s

/-- Complete multiplicativity of `f : ℕ → ℂ` is inherited by the terms of its L-series. -/
lemma term_completelyMultiplicative {f : ℕ → ℂ} (hf : ∀ m n, f (m * n) = f m * f n) (s : ℂ)
    (m n : ℕ) :
    term f s (m * n) = term f s m * term f s n :=
  term_mul (hf m n) s

lemma term_at_one {f : ℕ → ℂ} (h₁ : f 1 = 1) (s : ℂ) : term f s 1 = 1 := by
  rw [term_of_ne_zero one_ne_zero, h₁, Nat.cast_one, one_cpow, div_one]

end LSeries

section eulerProduct

open Nat BigOperators Filter Topology EulerProduct

namespace LSeries

/-- The Euler product for the L-series of a weakly multiplicative sequence `f` -/
lemma eulerProduct_of_multiplicative {f : ℕ → ℂ} (h₁ : f 1 = 1)
    (hf : ∀ {m n}, m.Coprime n → f (m * n) = f m * f n) {s : ℂ} (hs : LSeriesSummable f s) :
    Tendsto (fun n : ℕ ↦ ∏ p in primesBelow n, ∑' e, term f s (p ^ e)) atTop (𝓝 (L f s)) :=
  eulerProduct (term_at_one h₁ s) (term_multiplicative hf s) hs.norm (term_zero ..)

/-- The Euler product for the L-series of a completely multiplicative sequence `f` -/
lemma eulerProduct_of_completelyMultiplicative {f : ℕ → ℂ} (h₁ : f 1 = 1)
    (hf : ∀ m n, f (m * n) = f m * f n) {s : ℂ} (hs : LSeriesSummable f s) :
    Tendsto (fun n : ℕ ↦ ∏ p in primesBelow n, (1 - term f s p)⁻¹) atTop (𝓝 (L f s)) :=
  eulerProduct_completely_multiplicative
    (f := { toFun := term f s,
            map_zero' := term_zero ..,
            map_one' := term_at_one h₁ s,
            map_mul' := term_completelyMultiplicative hf s })
    hs.norm

end LSeries

end eulerProduct
