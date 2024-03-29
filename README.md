# EulerProducts

An attempt at formalizing facts on Euler products and L-series more generally in Lean

Some results have by now made it into Mathlib.

Current projects:
* [__EulerProducts/Auxiliary.lean__](EulerProducts/blob/main/EulerProducts/Auxiliary.lean):
  auxiliary lemmas
* [__EulerProducts/Logarithm.lean__](EulerProducts/blob/main/EulerProducts/Logarithm.lean):
  proves a logarithmic version of the Euler product formula for completely multiplicative 
  arithmetic functions
* [__EulerProducts/EulerProduct.lean__](EulerProducts/blob/main/EulerProducts/EulerProduct.lean):
  Euler products formulas for L-series of weakly or completely multiplicative sequences
* [__EulerProducts/LSeriesUnique.lean__](EulerProducts/blob/main/EulerProducts/LSeriesUnique.lean):
  a converging L-series determines its coefficients
* [__EulerProducts/DirichletLSeries.lean__](EulerProducts/blob/main/EulerProducts/DirichletLSeries.lean):
  results on L-series of Dirichlet characters and specific arithmetic functions (like the Möbius and
  von Mangoldt functions)
* [__EulerProducts/PNT.lean__](EulerProducts/blob/main/EulerProducts/PNT.lean):
  a reduction of the __Prime Number Theorem__ (in the version $\psi(x) \sim x$) to a version of the
  __Wiener-Ikehara Tauberian Theorem__.
