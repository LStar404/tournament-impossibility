# Fixed-order Cauchy error transfer

Focused Lean compilation passed and generated the library .olean. The two
exported axiom reports contain only propext, Classical.choice, Quot.sound.
The proof uses Mathlib's full iterated-derivative Cauchy estimate, not an
unproved derivative assumption.

For |z|<=r<R and a complex function bounded by C/n:

* Differentiability on the outer open disk gives the bound
  j! C / [n ((R-r)/2)^j] for every fixed derivative order j.
* Differentiability on that disk plus continuity on its closure, with the
  bound on the closed disk, gives the sharper j! C / [n (R-r)^j].
* The derivative-difference endpoint explicitly identifies iterated derivatives
  of f-g with the difference of derivatives of f and g, using analyticity
  inferred from complex differentiability locally.

The constants are uniform in the point z in the smaller disk and in n.
No uniformity in derivative order j is claimed. The statements permit n=0
under Lean's totalized real division, but intended asymptotic applications
use positive orders n; the value-bound hypothesis then has its ordinary meaning.

The actual functions' differentiability and their C/n value error are explicit
premises. This module does not assert that the complete Gaussian/source error
has already satisfied those premises, nor does it prove full Condition R.
See cauchy_derivative_formal_plan.md for the remaining application interfaces.
Aggregate integration and publication are separate parent-owned steps.
