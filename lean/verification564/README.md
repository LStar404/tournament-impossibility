# Verified 564-module A.5 correction (0.4.1)

PASS: QRegularGeometricLimit and EndpointCheck were freshly compiled; 562 unchanged
project objects were copied only after source/object hash verification. The
combined 564-module environment passed one full-kernel inventory scan, actual
builtin #check/#print axioms for all 7,979 declarations, stored/inferred type
checks, and complete raw Lean Expr type exports. This is two fresh project
compilations plus a full 564-module audit, not a full 564-source rebuild.

The complete raw types, names, universe parameters, kinds and axiom sets match
exactly, by globally unique kernel name, all 7,970 baseline declarations plus the
9 independently verified declarations of the new module. There were
0 owner-attribution changes and 0 pretty-type display differences;
summary.json identifies them. Owner changes never count as missing declarations.
Only Classical.choice, Quot.sound and propext occur; no sorryAx or new axiom.
All 79,506 recorded external dependency files were rehashed before and after,
and all reused objects, project sources and package/configuration pins checked.

## Corrected statement and retained limits

NonAlgebraicity.qRegular_geometric_limit_rational proves the exact geometric
assertion of paper Theorem A.5: for q>=2, rational-valued a and natural d,
complex q-kernel regularity and convergence of q^(-d*e)a(q^e) imply that the
limit is rational. It needs neither a full-sequence limit nor an LW premise.
The new full-sequence corollary has the same proposition as the old endpoint.
Version 0.4.0 checked the latter full-sequence proposition; its text overstated
coverage of the general geometric-only assertion. The old theorem, its
mathematical proof, and its existing applications remain unchanged.

Actual A.5 applications, degree zero, q^e positivity and the n=0 conventions
were checked, together with the exact E/M/m_n instantiations. Existing
nonalgebraicity/non-q-regularity applications retain FourExponentialIndependence.
This patch does not establish full Condition R, actual F/J, extremizer
classification, natural-boundary or non-D-finite conclusions. No other new
research module is included.

## Reproduction and historical evidence

Use Python 3.11+, Lean 4.35.0 and the unchanged locked dependencies. From lean/:

```sh
lake exe cache get
(cd .lake/packages/Cli && lake build Cli)
cd ..
python3 tools/verify564.py --check-sources-only
LEAN_BIN="$(cd lean && elan which lean)" python3 tools/verify564.py --output /tmp/tournament564-fresh
```

The output directory must not exist. The Cli build is essential because plain
Mathlib cache get does not include Cli, while the portable runner requires every
locked package library directory. Do not run lake update or change the manifest.
LEAN_BIN and MATHLIB_PACKAGES support non-default installations.

sources.json pins the 564 sources, configuration, helper/application/runner bytes
and declarations.json. The latter stores exact names/universes/kinds/axioms and
SHA256 fingerprints of each full raw Expr UTF-8 string. The fresh runner rebuilds
all 564 sources, exports every complete raw type and compares those fingerprints.
Its source-only/syntax checks pass; a full fresh 564 run has not been performed.
The completed integration above compares the complete raw strings directly.

verification563/ and tools/verify563.py are historical 0.4.0 certificates/runner.
Their mathematical bytes are unchanged; only the historical README gains the
Cli prerequisite and an explicit original-snapshot scope note. Run the old
verifier only in the original 0.4.0 ZIP or exact ca4633 snapshot, not against the
changed 564 EndpointCheck/lakefile. Older verification557/ and verification/
remain byte-identical historical evidence. The original 0.4.0 ZIP is not replaced.
See the root SOURCE_REPRODUCTION_README.md for installation and package scope.
