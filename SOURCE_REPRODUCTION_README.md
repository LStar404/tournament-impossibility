# Source reproduction 0.4.1: narrow Theorem A.5 coverage correction

This source release adds QRegularGeometricLimit and imports it from EndpointCheck.
Theorem A.5's geometric-subsequence assertion now has a direct endpoint:
NonAlgebraicity.qRegular_geometric_limit_rational. It assumes complex q-kernel
regularity and convergence of q^(-d*e) a(q^e), not convergence of the full sequence.
The full-sequence corollary has a type definitionally equal to the previous
qRegular_scaled_limit_rational endpoint. Neither assertion has a
Lindemann–Weierstrass or FourExponentialIndependence premise.

The earlier full-sequence theorem remains unchanged. This correction does not
establish full Condition R, actual F/J, structural classification, a natural
boundary, or non-D-finiteness. Existing transcendence/nonalgebraicity applications
retain their stated conditional premises. No Condition R research module is
included in this release.

## Evidence scope

The verification564 directory records the separate incremental integration:
QRegularGeometricLimit and EndpointCheck are the two fresh source compilations;
562 other module objects are reused after verification. It passed a
complete 564-module kernel audit of 7,979 declarations, with exact direct
comparison of all complete raw types to the prior 7,970 plus new 9 baseline.
Consult summary.json for measured results, exact hashes and audit facts. This is not
a fresh compilation of all 564 sources. Do not infer that a full fresh 564 build
has passed from the incremental audit or from source-hash checks.

The original 0.4.0 source ZIP and original full-563 reproduction run are not
modified. That separate full-563 rebuild is still in progress as of preparation
of this correction; its completion must be reported from its own result, not
inferred from the newer integration. Historical verification563 mathematical
certificates are unchanged. The historical README adds the
locked Cli build prerequisite missed by cache-get-only instructions and clarifies
that verify563 applies only to the original 0.4.0 snapshot.

## Fresh-source reproduction

Use Python 3.11 or newer and Lean leanprover/lean4:v4.35.0. Obtain the locked
package sources and Mathlib cache without changing lean/lake-manifest.json:

```sh
elan toolchain install leanprover/lean4:v4.35.0
cd lean
lake exe cache get
(cd .lake/packages/Cli && lake build Cli)
cd ..
python3 tools/verify564.py --check-sources-only
LEAN_BIN="$(cd lean && elan which lean)" python3 tools/verify564.py --output /tmp/tournament564-fresh
```

The output directory must not exist. Do not run lake update. Cli is locked to
c24fe6078c630e89b489bffe59b3e20ac30d12c8. Plain Mathlib cache get follows the
Mathlib import closure and does not include Cli; the explicit build is a
reproduction prerequisite, not a change to any mathematical certificate.

The verifier requires and verifies a library directory for every locked package,
including Cli; it does not rebuild those packages or update their revisions.
It verifies package revisions and tracked source cleanliness, fingerprints their
library artifacts, and creates a new project-object directory. LEAN_BIN selects
the pinned compiler; MATHLIB_PACKAGES optionally selects the directory containing
all locked package checkouts. The default is lean/.lake/packages.

All 564 project sources are freshly compiled, without project-object reuse.
A full kernel inventory is checked against module-data inventory. Every kernel
declaration receives real builtin #check/#print axioms commands and a complete
raw Lean Expr type export. Globally unique names, SHA256 fingerprints of the complete UTF-8 raw Expr
strings, ordered universes, declaration kinds and axiom sets must match the
pinned integrated declarations.json, not merely their counts. The fresh run
exports complete raw types locally; the compact published manifest stores their
cryptographic fingerprints rather than the full raw strings. Module attribution is not used as
a declaration identity because import order can relocate generated constants.

The two existing SharpApplication checks and GeometricApplicationChecks run as
standalone tools, never exported project roots. They include direct exact-type
A.5 application, degree-zero normalization, positivity of q^e, and definitional
equality of the new full-sequence corollary to the old endpoint.

A successful fresh run writes result.json only after all checks finish. A
source-only PASS establishes file hashes and manifest consistency, not proof
compilation or a kernel audit. The historical verify563.py remains unchanged.

## Package scope and attribution

The source-reproduction ZIP contains all 564 project sources, pinned configuration,
current and historical verification summaries, portable verification tools, both
complete paper TeX/Markdown/PDF versions, CITATION.cff and the unchanged LICENSE.
It is not an offline dependency bundle: Lean, Mathlib, package caches and compiled
objects must be obtained separately. Internet access is needed for initial setup.
The paper author is Xingchen Liu, School of Mathematics, Sichuan University.
The repository LICENSE retains Xingchen Liu and Xiangyu Ye, CC BY4.0.

Version 0.4.0 remains available at https://zenodo.org/records/24104925. That record
is historical and is not the DOI of this 0.4.1 correction. No new Zenodo version
is asserted by this source package. ARCHIVE_MANIFEST.json and SHA256SUMS in the
ZIP identify its exact included bytes; its own SHA256 is supplied alongside it.
The complete local audit logs, object files and raw Expr exports are separate
from this portable source package. The compact declaration fingerprints permit
a fresh run to compare every full exported type without bundling those objects.

## Paper reproduction

The included 0.4.1 PDFs were rebuilt locally in two XeLaTeX passes per language,
using XeTeX 3.141592653-2.6-0.999996 (TeX Live 2025/dev/Debian), and visually
checked. The GitHub paper workflow instead targets Tectonic 0.17.0. These are
distinct builds; engine/font differences or PDF metadata can change PDF bytes.
The archive manifests identify the exact reviewed local PDFs, not an asserted
future CI output. Complete bilingual TeX and synchronized Markdown are included.
Paper-build helpers and the locked Tectonic fallback installer are in tools/.
Reproduction needs the chosen TeX engine and required fonts/TeX resources, which
are not bundled in the source ZIP.
