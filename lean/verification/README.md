# Verification evidence, 2026-11-08

`result.json` was regenerated at 2026-11-08T14:48:15.732408+00:00 by `python verify.py`.
All 18 delivered proof modules passed. The record binds each result to its SHA-256 source hash.
The 35 printed theorem-axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
No external mathematical input was declared as a new axiom.

The new endpoints are in `QRegularApplications.lean` and `PathCountGrowth.lean`.
They retain explicit `ExtremalAsymptotic` and, for the transcendence-based a/m
obstructions, `FourExponentialIndependence` assumptions.
The full rational-limit strengthening of paper Theorem A.5 is not formalized:
the checked obstruction excludes transcendental limits, which suffices for a/m.
The raw-count endpoint concerns actual continuous-linear digit representations;
the general equivalence with the finite q-kernel definition is not formalized.

R, natural boundary, non-D-finiteness, and the upstream extremal graph theorem
are not certified by these logs. See the paper's separate source/assumption audit.

A second build, `lake build`, completed successfully (3168 jobs).
Independent `lake env lean EndpointCheck.lean` passed with exit code 0. It locks
the exact theorem types and the standard q-kernel definition and prints nine
additional axiom audits, again only the three standard axioms. It is a separate
endpoint test, not counted among the 18 proof modules in `result.json`.
