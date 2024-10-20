# EulerProducts

An attempt at formalizing facts on Euler products and L-series more generally in Lean

Some results have by now made it into Mathlib.

Current projects:
* [__EulerProducts/Auxiliary.lean__](EulerProducts/Auxiliary.lean):
  auxiliary lemmas
* [__EulerProducts/Logarithm.lean__](EulerProducts/Logarithm.lean):
  proves a logarithmic version of the Euler product formula for completely multiplicative 
  arithmetic functions
* [__EulerProducts/EulerProduct.lean__](EulerProducts/EulerProduct.lean):
  Euler products formulas for L-series of weakly or completely multiplicative sequences
* [__EulerProducts/LSeriesUnique.lean__](EulerProducts/LSeriesUnique.lean):
  a converging L-series determines its coefficients
* [__EulerProducts/DirichletLSeries.lean__](EulerProducts/DirichletLSeries.lean):
  results on L-series of Dirichlet characters and specific arithmetic functions (like the Möbius and
  von Mangoldt functions)
* [__EulerProducts/NonvanishingQuadratic.lean__](EulerProducts/NonvanishingQuadratic.lean):
  This contains a proof of the non-vanishing of the L-function of a nontrivial quadratic
  Dirichlet character at 1.
* [__EulerProducts/Orthogonality.lean__](EulerProducts/Orthogonality.lean):
  A proof of the orthogonality relation of Dirichlet characters of given modulus.
* [__EulerProducts/PNT.lean__](EulerProducts/PNT.lean):
  a reduction of the __Prime Number Theorem__ (in the version $\psi(x) \sim x$) to a version of the
  __Wiener-Ikehara Tauberian Theorem__. This also contains a proof of the non-vanishing
  of Dirichlet L-functions of nontrivial characters along the line `Re s = 1`. This is material
  that was created in the framework of the [__DirichletNonvanishing__](https://github.com/CBirkbeck/DirichletNonvanishing) project. The non-vanishing is then used to give a proof (the reduction) of 
  *Dirichlet's Theorem* (to the Wiener-Ikehara Theorem), in a PNT-like version.
