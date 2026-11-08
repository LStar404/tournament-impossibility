# TwoBlockCubeGeneric scope

This is the arbitrary-finite-type version of the exact four-block cube expansion. For real skew A on ι and B on κ, joined A B has blocks A, all-ones, negative all-ones, B. `joined_cube` explicitly computes all four blocks using finite skew-total cancellation. The raw algebraic expansion also supports arbitrary rectangular off-diagonal blocks.

Actual Lean 4.35 serial compilation passed and generated the matching olean. See verification/two_block_cube_generic.log. Main theorem axiom prints have only propext, Classical.choice, Quot.sound.

No norm or asymptotic comparison is asserted by this module alone. Its generic sum-type carrier permits actual nested ordinal-block constructions without a hypothetical moment sequence.
