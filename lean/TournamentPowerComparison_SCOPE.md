# TournamentPowerComparison scope

Actual Lean 4.35 compilation passed.
- The iterated action of a fixed actual tournament is identified with Matrix powers (not pointwise powers of its entry function).
- Absolute sorting of a coordinate basis vector does not depend on its position.
- Every column of B^r is bounded by the same explicit K basis orbit.
- frobenius_power_bound proves the expanded squared Frobenius bound against n times that orbit, for all natural r.

The reference orbit is not replaced with T in this module. Logs: verification/TournamentPowerComparison.log. Standard three axioms only, no sorryAx/new axioms.

Included in full `verify.py`, `lakefile.toml`, and the raw-matrix independent
`ReferenceMomentEndpoint.lean`/`EndpointCheck.lean` audits.
