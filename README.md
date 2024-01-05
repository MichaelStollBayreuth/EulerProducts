# EulerProducts

An attempt at formalizing facts on Euler products in Lean

Some results have by now made it into Mathlib.

Current projects:
* [__EulerProducts/ComplexLog.lean__](EulerProducts/ComplexLog.lean): estimates for the complex
  logarithm (see [#9270](https://github.com/leanprover-community/mathlib4/pull/9270))
* [__EulerProducts/Auxiliary.lean__](EulerProducts/Auxiliary.lean): auxiliary lemmas
  (see [#9404](https://github.com/leanprover-community/mathlib4/pull/9404) for the `EReal` part)
* [__EulerProducts/Logarithm.lean__](EulerProducts/Logarithm.lean): proves a logarithmic version
  of the Euler product formula for completely multiplicative arithmetic functions
* [__EulerProducts/LSeries.lean__](EulerProducts/LSeries.lean): convergence, derivatives, products
  of L-series
* [__EulerProducts/PNT.lean__](EulerProducts/PNT.lean): a reduction of the __Prime Number Theorem__
  (in the version $\psi(x) \sim x$) to a version of the __Wiener-Ikehara Tauberian Theorem__.
