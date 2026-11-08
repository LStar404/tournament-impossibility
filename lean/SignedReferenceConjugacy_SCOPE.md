# SignedReferenceConjugacy scope

Source combines explicit K/T square formulas and integer zigzag arithmetic to prove a concrete signed-permutation entry relation. Q is explicitly defined by its unique signed nonzero entry in each row, Q_orthogonal proves QQᵀ=I, and the final theorem states K²=Q(−T²)Qᵀ.

STATUS: actual Lean 4.35 serial compilation passed. See verification/SignedReferenceConjugacy.log. concrete_entry, concrete_square_conjugacy and Q_orthogonal all print only propext, Classical.choice and Quot.sound. No sorry/admit/new axioms are used.

This is a finite reference identity, not an asymptotic theorem or Assumption R.

Scope boundary: this concrete square identity is an input to nonnegative-integer power comparisons, not a statement about negative powers. The separate all-ones reference-orbit identity is not proved in this module or by Q_orthogonal alone. No claim of a complete proof of Assumption R is made.

Included in full `verify.py`, `lakefile.toml`, and the raw-matrix independent
`ReferenceMomentEndpoint.lean`/`EndpointCheck.lean` audits.
