# Actual ordered-block sixth-moment bridge

The theorem `actual_sixth_coefficient` identifies the finite polynomial
(★) with an ACTUAL Frobenius sixth moment for a finite family of arbitrary real
skew-symmetric square blocks. See verification logs for the compiled state.

## Construction and quantifiers

- Block dimensions m : Nat → Nat, matrices A_i of size m_i.
- Sole matrix hypothesis: A_i(x,y) = −A_i(y,x). Unit off-diagonal entries are
  unnecessary, so actual tournament sign matrices are included.
- Carrier 0 = Fin 0, Carrier (k+1) = Carrier k ⊕ Fin(m_k).
- The actual matrix joins the previous blocks to A_k using an all-ones upper
  off-diagonal block and an all-minus-ones lower block.
- All finite k, including zero and empty blocks, are allowed.
- e_i = ||A_i 1||², f_i = ||A_i² 1||², g_i = ||A_i³||F².

## Proof route

No determinant-series identity is assumed. The actual cube is expanded into
four blocks; rank-one inner products, skew-symmetry, and finite sums establish
all three real two-block moment recurrences. Three additive polynomial
invariants then identify their cumulative sixth moment with (★).

`OrdinalMomentRecurrence` alone remains an algebraic layer. The actual matrix
realization is supplied only by `OrdinalSixthMatrixBridge` and its dependencies.

## Exclusions

This bridge does not itself identify cyclic triangle counts with
(e_i^0−e_i)/8, prove the transitive closed-form e_i^0, establish the small-diamond
counting estimates, prove the final small-deficit spectral bound, or prove R.
It also does not construct a general formal log-determinant API.
