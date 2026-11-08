# TwoBlockSixthMoment scope

## Actual matrix result

For arbitrary finite types ι,κ and actual real skew matrices A,B, `third_join` proves the exact sixth Frobenius moment recurrence for their all-ones ordinal join S:

    g(S) = g(A)+g(B)+6 b f(A)+6 a f(B)+6 e(A)e(B)
           +6 a b² e(A)+6 a² b e(B)+2 a³ b³,

where a=card(ι), b=card(κ), e(A)=||A1||², f(A)=||A²1||², and g(A)=||A³||F². The definitions are TwoBlockEnergy.first/second and TwoBlockSixthMoment.third. Empty carriers are allowed.

The proof establishes the mixed inner products from actual skew symmetry, rather than assuming their target energy values. `diagonal_cube_norm` gives g(A)+4 b f(A)+2 a b² e(A). `cross_cube_norm` gives b f(A)+a f(B)+3 e(A)e(B)+a³b³+2ab²e(A)+2a²be(B). The lower-left norm equals the upper-right norm by actual cube skew symmetry. All four blocks are summed.

## Verification and limits

Actual Lean 4.35 serial compilation succeeded, including regenerated Matrix-typed RectangularFrobenius dependencies. The three theorem axiom prints contain only propext, Classical.choice, Quot.sound; no sorryAx or added axiom. See verification/two_block_sixth_moment.log.

This is an exact finite two-block identity, not by itself the arbitrary-block iteration, an asymptotic small-defect estimate, the all-ones K/T orbit identity, or Assumption R. Subsequent modules must explicitly connect these separate interfaces.
