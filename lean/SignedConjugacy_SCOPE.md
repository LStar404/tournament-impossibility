# SignedConjugacy scope

Actual Lean 4.35 compilation passed.
This is an explicitly generic transport lemma: given a genuine permutation, signs with square 1, two normal real matrices, and a proved signed conjugacy of their Gram matrices, it proves equality of the corresponding column squared norms for every natural power. It also proves multiplication and power preservation of the signed-entry relation.

The concrete Gram relation is a HYPOTHESIS here; this module alone must not be advertised as establishing K/T conjugacy. The later concrete reference assembly must discharge that hypothesis. Log: verification/SignedConjugacy.log; standard three axioms only.

Included in full `verify.py`, `lakefile.toml`, and the raw-matrix independent
`ReferenceMomentEndpoint.lean`/`EndpointCheck.lean` audits.
