# Verified 557-module snapshot

This directory describes the isolated fresh direct-Lean run completed on 2026-11-10 at 08:20 UTC: 557 modules, 7,907 declarations, full-kernel inventory equality and real builtin type/axiom checks. Only propext, Classical.choice and Quot.sound occurred. No historical project objects were reused. This was not a new Lake build.

`sources.json` records every exact source and configuration hash. `summary.json` is a portable, path-redacted summary of that completed run, including original artifact hashes for provenance. Large raw logs and object caches are intentionally not committed. Historical `../verification/` evidence remains historical.

## Verified comment correction

After the original fresh 557-module run, 30 obsolete compilation-status comments were corrected without changing any non-comment bytes. Those 30 modules were freshly compiled. The 527 unchanged modules reused individually hash-verified original objects. All 557 modules and all 7,907 declarations were then newly audited, with full-kernel inventory equality, real builtin type/axiom checks, and exact equality of original declaration records and full unabridged kernel Expr types. This was not a second compilation of all 557 modules. The independent final checker verified 2,377 evidence-file hashes.

`sources.json` identifies the current corrected sources. `summary.json` distinguishes the original fresh run from this correction run; `comment_correction.json` records the changed source hashes and compact evidence. Historical Candidate module/namespace names do not indicate an unverified current status. Mathematical assumptions and limitations remain unchanged.

## Reproduction

Install the pinned Lean 4.35.0 toolchain. From `lean/`, run `lake exe cache get` to obtain the pinned mathlib dependencies. From the repository root:

```sh
python3 tools/verify557.py --check-sources-only
python3 tools/verify557.py --output /tmp/tournament-audit-new
```

The output directory must not exist. The runner checks exact source/configuration hashes and dependency revisions, compiles every project module in topological order into fresh output, and audits imported declarations against a full-kernel inventory. Set `LEAN_BIN` and/or `MATHLIB_PACKAGES` only if using a non-default installation. No local or historical project `.olean` directory is on its search path.

The portable runner is an adaptation of the completed isolated audit. Its source-hash mode has been tested; the full portable rerun has not yet been executed. The completed result reported above belongs to the original isolated audit, not an asserted rerun of this adapter.

## Mathematical scope

Actual two-constant MainBound, with L=cosh(1)/cos(1) and packing upper U, and actual-maximizer tau <= 2 log(U/L)+D/n. This does not establish sharp-L, tau=O(1/n), structural classification, actual F/J, or full Condition R. Existing downstream nonalgebraicity applications retain their explicit external hypotheses.
