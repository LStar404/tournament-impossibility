# DiamondGap: universal positive diamond gap for actual tournaments

## Proven scope

`DiamondGap.Tournament V` is an integer matrix `S : V → V → ℤ` satisfying
`S a b = -S b a` and `S a b ∈ {1,-1}` for distinct vertices. The diagonal is proved zero.
This is the usual signed adjacency-matrix representation of an arbitrary tournament;
there is no regularity, parity, color-word, separation-graph, or recovery hypothesis.

The Pfaffian polynomial in edge order `ab,ac,ad,bc,bd,cd` is `af-be+cd`.
`quad_iff_pattern` proves that its square is 9 exactly when the four vertices form
an ordinary diamond: a source or sink joined to a directed cyclic triangle.
The explicit four disjuncts in `diamondPattern` correspond to the possible
source/sink vertex. This equivalence is proved for all six distinct-vertex edges,
not assumed as a bridge.

`IsDiamond T s` requires `s.card=4` and a four-vertex enumeration with Pfaffian
square 9. `diamonds T` is the finite set of such **unordered vertex sets**.
It does not count ordered tuples, sources, or orientations multiple times.

Main exported endpoints:

* `DiamondGap.Tournament.diamond_covers`: if a diamond exists, every vertex lies
  in some diamond.
* `DiamondGap.Tournament.positive_gap`: if `0 < T.diamonds.card`, then
  `Fintype.card V ≤ 4 * T.diamonds.card`.
* `DiamondGap.Tournament.zero_or_gap`: the corresponding unconditional dichotomy.

## Proof method and audit

Instead of formalizing switching and transitive-tournament classification, the
proof uses the equivalent five-vertex local fact. On the six edges of a diamond
and the four edges to a fifth vertex, at least one of the four triples joined
to that fifth vertex gives another diamond. `local_bool` checks all 2^10 edge
assignments using Lean `decide`, with proof checked by kernel reduction.
`pattern_bool` likewise checks all 2^6 assignments for the pattern equivalence.
Neither uses `native_decide`, external scripts, an oracle, or a new axiom.
The local fact is lifted to arbitrary matrices via their ±1 edge hypotheses.
`quad_distinct` establishes all six inequalities whenever the Pfaffian square
is 9. The final finite-set argument bounds the cardinality of the union by the
sum of cardinalities; each diamond contributes exactly four.

Verified with Lean 4.35.0 and the repository-pinned mathlib.
`local_bool` and `quad_iff_pattern` require only `propext`.
`diamond_covers`, `positive_gap`, and `zero_or_gap` use only
`propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, `sorryAx`, user axioms, or unverified numeric computation.

## Not claimed

This proves the universal gap, not a sharp minimum number of diamonds.
It does not prove the spectral weak-feedback inequality, the even-order
nonregular exclusion, asymptotic permanent comparison, the recovery theorem R,
or any full extremal ranking. Those analytic bridges remain separate obligations.
No switching theorem or source-normalization algorithm is asserted by this file.

## Repository integration

Included in `lakefile.toml`, the full `verify.py` module list, and
`EndpointCheck.lean`. Machine-check output is retained in
`verification/DiamondGap.log` and the complete manifest in
`verification/result.json`.
