# Actual zero-diamond kernel determinant (verified)

This module transfers the existing generic-field transitive-kernel determinant
through the actual diagonal sign switch and ordinary vertex enumeration of a
zero-diamond tournament. It does not duplicate the principal-minor expansion:
the existing stronger switching representation already gives the complete
finite determinant directly.

Proved endpoint, over any characteristic-zero field (including C):

    det(I - (z/n) S) = ((1+z/n)^n + (1-z/n)^n)/2.

Here S is the real/integer skew sign matrix, and D=0 is its actual unordered
four-vertex diamond count. No spectral or principal-minor hypothesis is supplied.
The same polynomial at z replaced by i z has the alternating even coefficients.
Thus the displayed expression tends to cosh(z), not cos(z); the imaginary
parameter version is the one tending to cos(z).

This finite identity alone does not prove locally uniform limits, zero-free
regions, a branch of log/sqrt, source-resolvent numerators, or Condition R.
It must not be called a Gaussian limit theorem. A focused Lean 4.35.0 check
passed with only propext, Classical.choice and Quot.sound for both exported
endpoints. All 117 delivered modules subsequently passed verify.py (2026-11-08
22:54:52 UTC); all recorded source hashes match. The aggregate lake build
also passed (9164 jobs). These finite checks do not establish analytic R.

The normalized finite identity includes n=0 under Lean division conventions;
the empty determinant and right-hand side are both 1. Any asymptotic or
analytic interpretation separately requires positive n and then n tending to
infinity. Independent read-only mathematical review found no extra hidden
spectral or structural premise.
