# RawBlockSourceIdentity: checked scope

rawSource B is defined from the genuine 2n-dimensional ordinary bilinear
quadratic form ones^T ((B-I) B^{-1}) ones / 2. It is not defined as the
reduced scalar. Assuming B B^{-1}=I, source_eq_reduced proves
rawSource B = n - e^T u / 2, where u is the sum of the two blocks of
B^{-1} ones. The proof explicitly computes ones^T ones=2n.

This is generic finite block linear algebra. Invertibility for the actual
Gaussian block matrix, its Schur complement, and further source contraction
are separate obligations. No integral or permanent-recovery claim is made.

Focused Lean compile produced an olean. The endpoint axiom report contains
only propext, Classical.choice, Quot.sound, with no sorryAx.
