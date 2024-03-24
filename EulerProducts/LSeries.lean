import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.Normed.Field.InfiniteSum

/-!
# Dirichlet convolution of sequences and products of L-series

We define the *Dirichlet convolution* `f ⍟ g` of two sequences `f g : ℕ → R` with values in a
semiring `R` by `(f ⍟ g) n = ∑ (k * m = n), f k * g m` when `n ≠ 0` and `(f ⍟ g) 0 = 0`.
Technically, this is done by transporting the existing definition for `ArithmeticFunction R`;
see `LSeries.convolution`. We show that these definitions agree (`LSeries.convolution_def`).

We then consider the case `R = ℂ` and show that `L (f ⍟ g) = L f * L g` on the common domain
of convergence of the L-series `L f`  and `L g` of `f` and `g`; see `LSeries_convolution`
and `LSeries_convolution'`.
-/

open scoped LSeries.notation

open Complex LSeries

/-!
### Dirichlet convolution of two functions
-/

open BigOperators

/-- We turn any function `ℕ → R` into an `ArithmeticFunction R` by setting its value at `0`
to be zero. -/
def toArithmeticFunction {R : Type*} [Zero R] (f : ℕ → R) : ArithmeticFunction R where
  toFun n := if n = 0 then 0 else f n
  map_zero' := rfl

/-- If we consider an arithmetic function just as a function and turn it back into an
arithmetic function, it is the same as before. -/
@[simp]
lemma ArithmeticFunction.toArithmeticFunction_eq_self {R : Type*} [Zero R]
    (f : ArithmeticFunction R) :
    toArithmeticFunction f = f := by
  ext n
  simp (config := {contextual := true}) [toArithmeticFunction, ArithmeticFunction.map_zero]

/-- Dirichlet convolution of two sequences.

We define this in terms of the already existing definition for arithmetic functions. -/
noncomputable def LSeries.convolution {R : Type*} [Semiring R] (f g : ℕ → R) : ℕ → R :=
  (toArithmeticFunction f * toArithmeticFunction g :)

@[inherit_doc]
scoped[LSeries.notation] infixl:70 " ⍟ " => LSeries.convolution

open scoped LSeries.notation

/-- The product of two arithmetic functions defines the same function as the Dirichlet convolution
of the functions defined by them. -/
lemma ArithmeticFunction.mul_to_convolution {R : Type*} [Semiring R] (f g : ArithmeticFunction R) :
    f ⍟ g = (f * g :) := by
  simp only [convolution, ArithmeticFunction.toArithmeticFunction_eq_self]

namespace LSeries

lemma convolution_def {R : Type*} [Semiring R] (f g : ℕ → R) :
    f ⍟ g = fun n ↦ ∑ p in n.divisorsAntidiagonal, f p.1 * g p.2 := by
  ext n
  simp only [convolution, toArithmeticFunction, ArithmeticFunction.mul_apply,
    ArithmeticFunction.coe_mk, mul_ite, mul_zero, ite_mul, zero_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  obtain ⟨hp₁, hp₂⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  obtain ⟨h₁, h₂⟩ := mul_ne_zero_iff.mp (hp₁.symm ▸ hp₂)
  simp only [h₂, ↓reduceIte, h₁]

@[simp]
lemma convolution_map_zero {R : Type*} [Semiring R] (f g : ℕ → R) : (f ⍟ g) 0 = 0 := by
  simp only [convolution_def, Nat.divisorsAntidiagonal_zero, Finset.sum_empty]


/-!
### Multiplication of L-series
-/

open Set Nat in
/-- We give an expression of the `LSeries.term` of the convolution of two functions. -/
lemma term_convolution (f g : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    term (f ⍟ g) s n =
      ∑' (b : (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {n}),
        term f s b.val.1 * term g s b.val.2 := by
  let m : ℕ × ℕ → ℕ := fun p ↦ p.1 * p.2
  let h : ℕ × ℕ → ℂ := fun x ↦ term f s x.1 * term g s x.2
  rcases n.eq_zero_or_pos with rfl | hn
  · trans 0 -- show that both sides vanish when `n = 0`
    · -- by definition, the left hand sum is over the empty set
      exact term_zero ..
    · -- the right hand sum is over the union below, but in each term, one factor is always zero
      have hS : m ⁻¹' {0} = {0} ×ˢ univ ∪ (univ \ {0}) ×ˢ {0} := by
        ext
        simp only [m, mem_preimage, mem_singleton_iff, _root_.mul_eq_zero, mem_union, mem_prod,
          mem_univ, mem_diff]
        tauto
      rw [tsum_congr_set_coe h hS,
        tsum_union_disjoint (Disjoint.set_prod_left disjoint_sdiff_right ..) ?_ ?_,
          -- (hsum.subtype _) (hsum.subtype _),
        tsum_setProd_singleton_left 0 _ h, tsum_setProd_singleton_right _ 0 h]
      · simp only [h, term_zero, zero_mul, tsum_zero, mul_zero, add_zero]
      · simp only [h, Function.comp_def]
        convert summable_zero with p
        rw [Set.mem_singleton_iff.mp p.prop.1, term_zero, zero_mul]
      · simp only [h, Function.comp_def]
        convert summable_zero with p
        rw [Set.mem_singleton_iff.mp p.prop.2, term_zero, mul_zero]
  -- now `n > 0`
  have H : n.divisorsAntidiagonal = m ⁻¹' {n} := by
    ext x
    replace hn := hn.ne' -- for `tauto` below
    simp only [Finset.mem_coe, mem_divisorsAntidiagonal, m, mem_preimage, mem_singleton_iff]
    tauto
  rw [← H, Finset.tsum_subtype' n.divisorsAntidiagonal h, term_of_ne_zero hn.ne',
    convolution_def, Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  simp only [h]
  obtain ⟨hp, hn₀⟩ := mem_divisorsAntidiagonal.mp hp
  have ⟨hp₁, hp₂⟩ := mul_ne_zero_iff.mp <| hp.symm ▸ hn₀
  rw [term_of_ne_zero hp₁ f s, term_of_ne_zero hp₂ g s, mul_comm_div, div_div,
    ← mul_div_assoc, ← natCast_mul_natCast_cpow, ← Nat.cast_mul, mul_comm p.2, hp]

end LSeries

open Set in
/-- The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
equals the product of their L-series, assuming both L-series converge. -/
lemma LSeriesHasSum.convolution {f g : ℕ → ℂ} {s a b : ℂ} (hf : LSeriesHasSum f s a)
    (hg : LSeriesHasSum g s b) :
    LSeriesHasSum (f ⍟ g) s (a * b) := by
  simp only [LSeriesHasSum]
  have hsum := summable_mul_of_summable_norm hf.summable.norm hg.summable.norm
  let m : ℕ × ℕ → ℕ := fun p ↦ p.1 * p.2
  convert (HasSum.mul hf hg hsum).tsum_fiberwise m with n
  exact term_convolution ..

/-- The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
equals the product of their L-series, assuming both L-series converge. -/
lemma LSeries_convolution {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeries (f ⍟ g) s = LSeries f s * LSeries g s :=
  (LSeriesHasSum.convolution hf.LSeriesHasSum hg.LSeriesHasSum).LSeries_eq

/-- The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
equals the product of their L-series in their common half-plane of absolute convergence. -/
lemma LSeries_convolution' {f g : ℕ → ℂ} {s : ℂ}
    (hf : abscissaOfAbsConv f < s.re) (hg : abscissaOfAbsConv g < s.re) :
    LSeries (f ⍟ g) s = LSeries f s * LSeries g s :=
  LSeries_convolution (LSeriesSummable_of_abscissaOfAbsConv_lt_re hf)
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re hg)

/-- The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
is summable when both L-series are summable. -/
lemma LSeriesSummable.convolution {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeriesSummable (f ⍟ g) s :=
  (LSeriesHasSum.convolution hf.LSeriesHasSum hg.LSeriesHasSum).LSeriesSummable

namespace ArithmeticFunction

/-!
### Versions for arithmetic functions
-/

/-- The L-series of the (convolution) product of two `ℂ`-valued arithmetic functions `f` and `g`
equals the product of their L-series, assuming both L-series converge. -/
lemma LSeriesHasSum_mul {f g : ArithmeticFunction ℂ} {s a b : ℂ} (hf : LSeriesHasSum ↗f s a)
    (hg : LSeriesHasSum ↗g s b) :
    LSeriesHasSum ↗(f * g) s (a * b) :=
  mul_to_convolution f g ▸ hf.convolution hg

/-- The L-series of the (convolution) product of two `ℂ`-valued arithmetic functions `f` and `g`
equals the product of their L-series, assuming both L-series converge. -/
lemma LSeries_mul {f g : ArithmeticFunction ℂ} {s : ℂ} (hf : LSeriesSummable ↗f s)
    (hg : LSeriesSummable ↗g s) :
    LSeries ↗(f * g) s = LSeries ↗f s * LSeries ↗g s :=
  mul_to_convolution f g ▸ LSeries_convolution hf hg

/-- The L-series of the (convolution) product of two `ℂ`-valued arithmetic functions `f` and `g`
equals the product of their L-series in their common half-plane of absolute convergence. -/
lemma LSeries_mul' {f g : ArithmeticFunction ℂ} {s : ℂ}
    (hf : abscissaOfAbsConv ↗f < s.re) (hg : abscissaOfAbsConv ↗g < s.re) :
    LSeries ↗(f * g) s = LSeries ↗f s * LSeries ↗g s :=
  mul_to_convolution f g ▸ LSeries_convolution' hf hg

/-- The L-series of the (convolution) product of two `ℂ`-valued arithmetic functions `f` and `g`
is summable when both L-series are summable. -/
lemma LSeriesSummable_mul {f g : ArithmeticFunction ℂ} {s : ℂ} (hf : LSeriesSummable ↗f s)
    (hg : LSeriesSummable ↗g s) :
    LSeriesSummable ↗(f * g) s :=
  mul_to_convolution f g ▸ hf.convolution hg

end ArithmeticFunction
