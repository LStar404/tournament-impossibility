# Finite Wick pairing / permanent bridge

Finite pairing modules (validation evidence is recorded separately in verification/result.json):

1. BipartitePairingPermanent: independent left/right partner maps with both
inverse laws, equivalent to permutations; their edge-weight sum is permanent.
The induced 2n-vertex partner map is involutive and fixed-point free.
2. WickPairingZero: ALL fixed-point-free involutive permutations on Fin n ⊕
Fin n, including monochromatic edges. Edges are counted once by selecting
the smaller endpoint under an injective key placing left vertices first.
A same-colour edge makes its entire weight zero for zero monochromatic
covariance, and the full sum equals its bipartite filter.
3. WickBipartiteEquiv: constructs the actual equivalence from this bipartite
subtype of full pairings to independent left/right partner maps, with both
inverse proofs. Thus no permanent identity is smuggled into the definition.
4. WickPairingPermanent: proves unique representative selection, identifies
the surviving weight, and combines the equivalence and zero elimination to
obtain, over any commutative semiring,

  sum over ALL pairings of edge-product(fromBlocks 0 A A.transpose 0)
    = Matrix.permanent A.

The permanent index direction is explicitly handled using transpose. The
empty n=0 pairing sum is 1; no positivity, n>0, or invertibility is assumed.

Scope exclusions: this is a finite pairing-sum identity only, not a Wick
expectation or Gaussian integral theorem. There is no positive-measure
interpretation of general complex zQ. Products containing (1+X_i) require
partial pairings/subset expansion not supplied here. Analytic continuation,
exponential re-summation, activity estimates, truncation and permanent
recovery remainder estimates remain separate obligations. Full Condition R
is not proved.
