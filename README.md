# EulerProducts

An attempt at formalizing facts on Euler products and L-series more generally in Lean

Most of the results developed here have by now made it into Mathlib, most notably a proof of
**Drichlet's Theorem on Primes in Residue Classes**.

Apart from the uniqueness result for L-series, what is currently left in this repository
are some bits and pieces that were not needed for the big result, but may still be useful.

Contents:
* [__EulerProducts/Auxiliary.lean__](EulerProducts/Auxiliary.lean):
  auxiliary lemmas
* [__EulerProducts/EulerProduct.lean__](EulerProducts/EulerProduct.lean):
  Euler products formulas for L-series of weakly or completely multiplicative sequences
* [__EulerProducts/LSeriesUnique.lean__](EulerProducts/LSeriesUnique.lean):
  a converging L-series determines its coefficients
* [__EulerProducts/DirichletLSeries.lean__](EulerProducts/DirichletLSeries.lean):
  results on L-series of Dirichlet characters and specific arithmetic functions (like the Möbius and
  von Mangoldt functions)
* [__EulerProducts/PNT.lean__](EulerProducts/PNT.lean):
  a reduction of an asymptotic version of __Dirichlet's Theorem__ to a version of the
  __Wiener-Ikehara Tauberian Theorem__. Note that the Wiener-Ikehara Theorem is proved
  in [__PNT+__](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd?tab=readme-ov-file).
