# Portable 564 verification inputs

`tools/verify564.py` consumes `lean/verification564/sources.json`:

- `module_count`: 564.
- `modules`: unique records with `module`, repository-relative `path`, `sha256`,
  and `imports` (module-name list). The complete root set must equal the roots
  in `lean/lakefile.toml`.
- `configuration`: filename-to-SHA256 mapping relative to `lean/`; must include
  `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`.
- `tooling`: repository-relative filename-to-SHA256 mapping. Required entries:
  `tools/verify564.py`, `tools/FullTreeAuditSupportFast.lean`,
  `tools/ExactKernelTypes.lean`, `tools/SharpApplicationInstantiations.lean`,
  `tools/SharpApplicationFullyApplied.lean`, `tools/GeometricApplicationChecks.lean`.
- `expected_declarations`: object with `path` equal to the repository-relative
  declarations file and `sha256` equal to that file's SHA256.

`lean/verification564/declarations.json` contains `schema_version: 1`,
`module_count: 564`, `declaration_count: 7979`, and `records`. Each record has:

- `name`: globally unique full kernel name (including private/generated names).
- `kind`: declaration kind as exported by FullTreeAuditSupportFast.
- `universes`: ordered list of universe-parameter names.
- `axioms`: unique axiom names; comparison is order-independent.
- `type_expr_sha256`: lowercase SHA256 of the complete `type_expr_repr` string
  encoded as UTF-8, without an added newline, from ExactKernelTypes. This hashes
  Lean's derived Repr Expr output, including proof terms, universes, binder
  information and metadata. It is not a hash of the JSON encoding or pretty type.

Optional record fields (including module attribution) are ignored. The pinned
manifest must be generated from the completed integrated audit, not populated
from a portable run's new outputs. A fresh run independently exports full raw
Expr files and compares their hashes to the published integrated fingerprints.
The integration's own baseline comparison can use complete raw strings. These
are distinct evidence claims.

There is no circular self-hash: sources.json pins tooling and declarations.json,
but does not contain its own digest. A release-level manifest may pin
sources.json. The portable run records the source manifest's initial digest and
checks it again at completion. No measured audit result belongs in these inputs
until the integrated audit has actually completed.

Outputs are written only to the new `--output` directory: fresh project objects,
fresh helper objects, logs, complete kernel inventory, per-module builtin audit
records, full raw Expr exports, dependency-library hashes, and final result.json.
A result.json with passed=true is written only at the end of a successful full
run. Source-only mode never writes that certificate and never invokes Lean.
