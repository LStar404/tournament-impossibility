# Complex skew source identity: independent 141st candidate

Focused verification: actual Lean invocation exit 0, generated `.lake/build/lib/lean/ComplexSkewSourceIdentity.olean`.
Source: `impossibility_revision/lean/ComplexSkewSourceIdentity.lean`.
SHA256: `7f79ef56b9a486b8e7eab71329473fa735f61fabb82e2b9d4f427891ba9d92b4`.
Log: `/workspace/shared/r_upstream_audit/complex_skew_source_identity.log`.
Both printed endpoints depend only on propext, Classical.choice, Quot.sound.

The theorem holds for any finite-dimensional complex skew matrix S, any complex t, and a supplied genuine two-sided inverse R of I+t S². It proves the resolvent commutes with S and then

`e^T(R-I)e = t (S e)^T R(S e)`

for arbitrary e. For the actual all-ones vector it proves

`1^T R 1 = card(ι) + t (S1)^T R(S1)`.

No real-parameter, energy, series-convergence, or norm assumption is used. The source is explicitly bilinear, not Hermitian. Two minus signs cancel as required.

This candidate is NOT included in the frozen 140-module verify/lake results, aggregate configuration, endpoint audit, or current publication manifest. None of the 140 verified files or their configurations were edited. The old shared `next_lean_drafts` copy remains only an uncompiled historical draft.

Remaining integration: instantiate with the actual graph matrix and disk resolvent, then prove block Q Schur/source elimination and identify the raw Lambda. This is not a proof of a Gaussian integral, Wick expansion, permanent recovery, or Condition R.
