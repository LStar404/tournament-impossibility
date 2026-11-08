# Actual strongly connected component reconstruction

`TournamentOrdinalReconstruction` constructs the finite linearly ordered family
of actual strongly connected components of any finite real sign tournament.
The component order is the actual intercomponent edge direction. Its recursive
ordinal-block carrier is proved bijective with the original vertices, and its
matrix entries agree exactly under that bijection. In particular, no block
representation hypothesis, missing-vertex assumption, or moment equality is
supplied as an input.

The module proves that every included block is strongly connected, the block
sizes sum to the original dimension, and all natural-number-power Frobenius
moments (including the sixth moment) are preserved. Its auxiliary block-size
bound requires a positive global directed-cycle count.

This is a finite matrix/graph reconstruction theorem. It does not establish
Condition R, asymptotic recovery, or complex analytic estimates. Compilation
and axiom audit must be reported separately from this scope description.
