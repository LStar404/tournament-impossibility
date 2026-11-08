# OrdinalTransitiveReference: actual ordered reference-block normalization

The module constructs `blockEquiv m k`, the natural block-order bijection from the recursively nested carrier `OrdinalBlockMatrix.Carrier m k` to `Fin (total m k)`, and proves that `total m k` is exactly the sum of the first k block sizes.

## Exact kernel-checked results

- `entry`: the actual ordered matrix joining the transitive reference blocks T(m_i) has entries exactly those of T(total), after the constructed bijection. No reindexing identity is postulated.
- `power_entry` and `power_frobenius_relabel`: generic finite bijective relabeling preserves matrix powers and expanded Frobenius sums.
- `power_frobenius_eq`: for every natural-number exponent r, the actual ordered transitive-block join has the same squared Frobenius norm of its rth power as the single transitive matrix T(sum m_i).
- `sixth_eq`: the exact `TwoBlockSixthMoment.third` API equality for the actual join and T(sum m_i).

The exponent is `r : ℕ`, not an arbitrary signed integer. Empty blocks, k=0, and zero total dimension are included without positivity assumptions.

Lean 4.35 compilation passed. Main log: verification/ordinal_transitive_reference.log. The independent endpoint verification/OrdinalTransitiveReferenceEndpoint.lean states the expanded actual-matrix Frobenius identity without a hypothetical relabeling premise; see verification/ordinal_transitive_reference_endpoint.log. Principal endpoints use only propext, Classical.choice and Quot.sound, with no sorryAx or added axioms.

This removes the representation difference between a reference ordered join and the global transitive matrix. It does not itself prove any unformalized asymptotic/classification clauses of Assumption R.
