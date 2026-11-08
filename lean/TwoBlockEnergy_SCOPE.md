# TwoBlockEnergy verified scope

`TwoBlockEnergy.lean` proves first and second all-one orbit energy recurrences for the actual ordered block matrix `fromBlocks A 1 (-1) B`. The blocks may have any finite index types, including empty types, and any real skew-symmetric entries; no tournament unit-entry condition is needed.

Definitions: `first A = sum (A 1)^2`; `second A = sum (A (A 1))^2`. The latter is definitionally the squared norm of the two-step orbit, equivalent to `(A^2).mulVec 1` by matrix multiplication.

With cardinalities a,b, the proved endpoints are:

- first(join A B) = first A + first B + ab(a+b).
- second(join A B) = second A + second B + (b²+2ab)first A + (a²+2ab)first B + a²b²(a+b).

Intermediate skew-pair, zero self-quadratic, sum of first/second actions and mixed-action identities are proved from entrywise skew symmetry. No moment identities are assumed.

This file does not prove sixth Frobenius moment recursion, finite arbitrary-block induction, graph triangle counts, or full Assumption R.

Actual serial Lean compilation passed; see `verification/two_block_energy.log`. Both endpoint axiom prints contain only propext, Classical.choice, Quot.sound. No sorryAx.
