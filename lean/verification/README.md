# Verification evidence, 2026-11-08

`result.json` was regenerated at 2026-11-08T15:10:46.649740+00:00 by `python verify.py`.
All 22 delivered proof modules passed. Each result is bound to the source SHA-256.
The 41 printed theorem-axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
No external mathematical input is declared as a new axiom.

The complete A.5 theorem is now checked in `QRegularRationalLimit.lean`:
for every q≥2 and natural k, a rational-valued sequence with finite-dimensional
complex q-kernel and a_n/n^k→L has L∈ℚ. No graph asymptotic or transcendence
hypothesis is assumed in this general theorem. The descent preserves a linear
relation with nonzero denominator; it does not merely prove algebraicity.

The actual a/m applications retain explicit `ExtremalAsymptotic` and
`FourExponentialIndependence` assumptions. The P digit-model exclusion uses
only `ExtremalAsymptotic`. R, natural boundary, non-D-finiteness, and the upstream
extremal graph theorem remain outside this certification. The general equivalence
of finite q-kernels with the separate continuous-linear digit representation
interface is not formalized.

A second build, `lake build`, completed successfully (3173 jobs).
Independent `lake env lean EndpointCheck.lean` passed with exit code 0. It locks
the exact theorem types, including full A.5 directly with the q-kernel span
assumption, and prints eleven axiom audits containing only the standard three.
This separate endpoint test is not counted among the 22 proof modules.
