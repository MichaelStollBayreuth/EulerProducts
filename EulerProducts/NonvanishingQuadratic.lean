import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Positivity

/-!
# Non-vanishing of `L(χ, 1)` for nontrivial quadratic characters `χ`

The main result of this file is the statement
`DirichletCharacter.LFunction_at_one_ne_zero_of_quadratic`, which says that if `χ` is
a nontrivial (`χ ≠ 1`) quadratic (`χ^2 = 1`) Dirichlet character, then the value of
its L-function at `s = 1` is nonzero.

This is an important step in the proof of
*Dirichlet's Theorem on Primes in Arithmetic Progression*.
-/

/-!
### Auxiliary lemmas
-/

-- Mathlib.Analysis.Calculus.Deriv.Slope or Mathlib.LinearAlgebra.AffineSpace.Slope
lemma HasDerivAt.continuousAt_div {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜]
    {f : 𝕜 → 𝕜} {c a : 𝕜} (hf : HasDerivAt f a c) :
    ContinuousAt (Function.update (fun x ↦ (f x - f c) / (x - c)) c a) c := by
  rw [← slope_fun_def_field]
  exact continuousAt_update_same.mpr <| hasDerivAt_iff_tendsto_slope.mp hf

-- Mathlib.NumberTheory.MulChar.Basic
/-- A multiplicative character `χ` into an integral domain is quadratic
if and only if `χ^2 = 1`. -/
lemma MulChar.isQuadratic_iff_sq_eq_one {M R : Type*} [CommMonoid M] [CommRing R]
    [NoZeroDivisors R] [Nontrivial R] {χ : MulChar M R} :
    IsQuadratic χ ↔ χ ^ 2 = 1:= by
  refine ⟨fun h ↦ ext (fun x ↦ ?_), fun h x ↦ ?_⟩
  · rw [one_apply_coe, χ.pow_apply_coe]
    rcases h x with H | H | H
    · exact (not_isUnit_zero <| H ▸ IsUnit.map χ <| x.isUnit).elim
    · simp only [H, one_pow]
    · simp only [H, even_two, Even.neg_pow, one_pow]
  · by_cases hx : IsUnit x
    · refine .inr <| sq_eq_one_iff.mp ?_
      rw [← χ.pow_apply' two_ne_zero, h, MulChar.one_apply hx]
    · exact .inl <| map_nonunit χ hx

namespace DirichletCharacter

-- Mathlib.NumberTheory.DirichletCharacter.LSeries
open ArithmeticFunction in
/-- The arihmetic function associated to a Dirichlet character is multiplicative. -/
lemma isMultiplicative_toArithmeticFunction {N : ℕ} {R : Type*} [CommMonoidWithZero R]
    (χ : DirichletCharacter R N) :
    (toArithmeticFunction (χ .)).IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m} {n} hm hn _ ↦ ?_⟩
  · simp only [toArithmeticFunction, coe_mk, one_ne_zero, ↓reduceIte, Nat.cast_one, map_one]
  · simp only [toArithmeticFunction, coe_mk, mul_eq_zero, hm, hn, false_or, Nat.cast_mul, map_mul,
      if_false]

lemma apply_eq_toArithmeticFunction_apply {N : ℕ} {R : Type*} [CommMonoidWithZero R]
    (χ : DirichletCharacter R N) {n : ℕ} (hn : n ≠ 0) :
    χ n = toArithmeticFunction (χ ·) n := by
  simp only [toArithmeticFunction, ArithmeticFunction.coe_mk, hn, ↓reduceIte]

/-!
### Convolution of a Dirichlet character with ζ

We define `DirichletCharacter.zetaMul χ` to be the arithmetic function obtained by
taking the product (as arithmetic functions = Dirichlet convolution) of the
arithmetic function `ζ` with `χ`.

We then show that for a quadratic character `χ`, this arithmetic function is multiplicative
and takes nonnegative real values.
-/

open Complex ArithmeticFunction

variable {N : ℕ}

/-- The complex-valued arithmetic function that is the convolution of the constant
function `1` with `χ`. -/
def zetaMul (χ : DirichletCharacter ℂ N) : ArithmeticFunction ℂ :=
  .zeta * toArithmeticFunction (χ ·)

/-- The arithmetic function `zetaMul χ` is multiplicative. -/
lemma isMultiplicative_zetaMul (χ : DirichletCharacter ℂ N) : χ.zetaMul.IsMultiplicative :=
  isMultiplicative_zeta.natCast.mul <| isMultiplicative_toArithmeticFunction χ

lemma LSeriesSummable_zetaMul (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable χ.zetaMul s := by
  refine ArithmeticFunction.LSeriesSummable_mul (LSeriesSummable_zeta_iff.mpr hs) <|
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n hn ↦ ?_) hs
  simpa only [toArithmeticFunction, coe_mk, hn, ↓reduceIte, ← Complex.norm_eq_abs]
  using norm_le_one χ _

-- We use the ordering on `ℂ` given by comparing real parts for fixed imaginary part
open scoped ComplexOrder

lemma zetaMul_prime_pow_nonneg {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    0 ≤ zetaMul χ (p ^ k) := by
  simp only [zetaMul, toArithmeticFunction, coe_zeta_mul_apply, coe_mk,
    Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
    Nat.cast_pow, map_pow]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h
  · refine Finset.sum_nonneg fun i _ ↦ ?_
    simp only [h, le_refl, pow_nonneg]
  · refine Finset.sum_nonneg fun i _ ↦ ?_
    simp only [h, one_pow, zero_le_one]
  · simp only [h, neg_one_geom_sum]
    split_ifs
    exacts [le_rfl, zero_le_one]

/-- `zetaMul χ` takes nonnegative real values when `χ` is a quadratic character. -/
lemma zetaMul_nonneg {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ zetaMul χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · simpa only [χ.isMultiplicative_zetaMul.multiplicative_factorization _ hn] using
      Finset.prod_nonneg
        fun p hp ↦ zetaMul_prime_pow_nonneg hχ (Nat.prime_of_mem_primeFactors hp) _


/-!
### "Bad" Dirichlet characters

Our goal is to show that `L χ 1 ≠ 0` when `χ` is a (nontrivial) quadratic Dirichlet character.
To do that, we package the contradictory properties in a structure `DirichletCharacter.BadChar`
and derive further statements eventually leading to a contradiction.
-/

/-- The object we're trying to show doesn't exist: A nontrivial quadratic Dirichlet character
whose L-function vanishes at `s =1`. -/
structure BadChar (N : ℕ) [NeZero N] where
  χ : DirichletCharacter ℂ N
  χ_ne : χ ≠ 1
  χ_sq : χ ^ 2 = 1
  hχ : χ.LFunction 1 = 0

variable {N : ℕ} [NeZero N]

open Complex DirichletCharacter

namespace BadChar

/-- The product of the Riemann zeta function with the L-function of `B.χ`.
We will show that `B.F (-2) = 0` but also that `B.F (-2)` must be positive,
giving the desired contradiction. -/
noncomputable
def F (B : BadChar N) : ℂ → ℂ :=
  Function.update (fun s : ℂ ↦ riemannZeta s * LFunction B.χ s) 1 (deriv (LFunction B.χ) 1)

lemma F_differentiableAt_of_ne (B : BadChar N) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ B.F s := by
  apply DifferentiableAt.congr_of_eventuallyEq
  · exact (differentiableAt_riemannZeta hs).mul <| differentiableAt_LFunction B.χ s (.inl hs)
  · filter_upwards [eventually_ne_nhds hs] with t ht using Function.update_noteq ht ..

open ArithmeticFunction in
/-- `B.F` agrees with the L-series of `zetaMul χ` on `1 < s.re`. -/
lemma F_eq_LSeries (B : BadChar N) {s : ℂ} (hs : 1 < s.re) :
    B.F s = LSeries B.χ.zetaMul s := by
  rw [F, zetaMul, ← coe_mul, LSeries_convolution']
  · have hs' : s ≠ 1 := fun h ↦ by simp only [h, one_re, lt_self_iff_false] at hs
    simp only [ne_eq, hs', not_false_eq_true, Function.update_noteq, B.χ.LFunction_eq_LSeries hs]
    congr 1
    · rw [← LSeries_zeta_eq_riemannZeta hs]
      rfl
    · exact LSeries_congr s B.χ.apply_eq_toArithmeticFunction_apply
  -- summability side goals from `LSeries_convolution'`
  · exact LSeriesSummable_zeta_iff.mpr hs
  · exact (LSeriesSummable_congr _ fun h ↦ (B.χ.apply_eq_toArithmeticFunction_apply h).symm).mpr <|
      ZMod.LSeriesSummable_of_one_lt_re B.χ hs

/-- If `χ` is a bad character, then `F` is an entire function. -/
lemma F_differentiable (B : BadChar N) : Differentiable ℂ B.F := by
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · exact B.F_differentiableAt_of_ne hs
  -- now need to deal with `s = 1`
  refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact B.F_differentiableAt_of_ne ht
  -- now reduced to showing *continuity* at s = 1
  let G := Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1
  let H := Function.update (fun s ↦ (B.χ.LFunction s - B.χ.LFunction 1) / (s - 1)) 1
    (deriv B.χ.LFunction 1)
  have : B.F = G * H := by
    ext1 t
    rcases eq_or_ne t 1 with rfl | ht
    · simp only [F, G, H, Pi.mul_apply, one_mul, Function.update_same]
    · simp only [F, G, H, Function.update_noteq ht, mul_comm _ (riemannZeta _), B.hχ, sub_zero,
      Pi.mul_apply, mul_assoc, mul_div_cancel₀ _ (sub_ne_zero.mpr ht)]
  rw [this]
  apply ContinuousAt.mul
  · simpa only [G, continuousAt_update_same] using riemannZeta_residue_one
  · exact (B.χ.differentiableAt_LFunction 1 (.inr B.χ_ne)).hasDerivAt.continuousAt_div

/-- The trivial zero at `s = -2` of the zeta function gives that `F (-2) = 0`.
This is used later to obtain a contradction. -/
lemma F_neg_two (B : BadChar N) : B.F (-2 : ℝ) = 0 := by
  have := riemannZeta_neg_two_mul_nat_add_one 0
  rw [Nat.cast_zero, zero_add, mul_one] at this
  rw [F, ofReal_neg, ofReal_ofNat, Function.update_noteq (mod_cast (by omega : (-2 : ℤ) ≠ 1)),
    this, zero_mul]

end BadChar

/-!
### The main result
-/

open scoped ComplexOrder in
/-- If `χ` is a nontrivial quadratic Dirichlet character, then `L(χ, 1) ≠ 0`. -/
theorem LFunction_at_one_ne_zero_of_quadratic {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ^ 2 = 1) (χ_ne : χ ≠ 1) :
    χ.LFunction 1 ≠ 0 := by
  intro hL
  -- construct a "bad character" and put together a contradiction.
  let B : BadChar N := {χ := χ, χ_sq := hχ, hχ := hL, χ_ne := χ_ne}
  refine (B.F_neg_two ▸ (?_ : 0 < B.F (-2 : ℝ))).false
  refine ArithmeticFunction.LSeries_positive_of_differentiable_of_eqOn (zetaMul_nonneg hχ)
    (χ.isMultiplicative_zetaMul.map_one ▸ zero_lt_one) B.F_differentiable ?_
    (fun _ ↦ B.F_eq_LSeries) _
  exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    fun _ a ↦ χ.LSeriesSummable_zetaMul a

end DirichletCharacter
