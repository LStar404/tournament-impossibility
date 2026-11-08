# DiamondFreeRepresentation: finite ordinary diamond-free color-word representation

## Final machine-checked statement

`diamondFree_color_representation` takes an actual finite
`DiamondGap.Tournament V` with no ordinary four-vertex diamond and returns:

* an actual `List Bool` color word w of length `Fintype.card V`;
* an ordinary enumeration `e : Fin (Fintype.card V) ≃ V`;
* equality of every ORIGINAL tournament matrix entry, after that enumeration,
  with `ColorTransport.colorGraph w`.

`zero_diamonds_color_representation` gives the same conclusion directly from
`T.diamonds.card = 0`, where diamonds are the existing unordered four-vertex
sets from DiamondGap. This is not a new abstract notion of a forbidden object.
The empty vertex type is included.

## Proof, with the switching distinction kept explicit

1. Define an explicit sign-switched matrix `d(a) * T.S(a,b) * d(b)` and prove
   it is a tournament. This operation is NOT called an ordinary isomorphism.
2. Prove its four-vertex Pfaffian is multiplied by the product of the four
   switching signs, so its square is unchanged. Consequently ordinary diamond
   absence is preserved, using the verified DiamondGap criterion.
3. Choose a pivot p. Set d(p)=1 and d(x)=T.S(p,x) for x≠p, and prove the pivot
   becomes a source in the switched tournament.
4. Prove source + diamond-free implies transitivity: any failure of
   transitivity would be a cyclic triangle joined to that source, and its
   Pfaffian square would be 9. The proof handles coincident vertices explicitly.
5. `TournamentColorEnumeration` constructs a genuine strict total order from
   the resulting transitive tournament and a finite ordered enumeration.
6. Encode the switching signs as an actual Bool list. Reconstruct the ORIGINAL
   matrix by multiplying those signs back into the transitive order matrix.
   This final identity is the color-word representation under an ordinary
   vertex enumeration; no assertion that T itself is ordinarily isomorphic
   to its transitive switched matrix is used.

No source, transitivity, representation, switching-invariance or enumeration
lemma is introduced as a new axiom. Each relevant premise of the generic
finite enumeration bridge is discharged here.

## Connections and remaining scope

The final word and exact matrix identity can be used with the already verified
ColorCutNormalization, ColorGraphRepair, and ColorTargetModels chain: those
modules handle arbitrary color words, their ordinary cut normalization,
energy and finite differing-edge counts, and the named carousel/doubling
models. The theorem here supplies the previously missing representation input
for the ZERO-diamond case.

It does not assert that arbitrary tournaments have color-word representations.
It does not repair tournaments with positive diamond count, prove upstream
analytic stability/feedback bounds, or prove the full condition R. Nor does
it make a new claim that general sign switching preserves ordinary graph
isomorphism. The result is restricted to diamond-free tournaments exactly as
stated in the hypothesis.

## Verification

Files: `lean/DiamondFreeRepresentation.lean` and its dependency
`lean/TournamentColorEnumeration.lean`.
Command: `lake env lean DiamondFreeRepresentation.lean`.
Log: `verification/DiamondFreeRepresentation.log`.
Final module compilation on 2026-11-08 completed with exit code 0, no warnings.
Seven printed core theorem audits contain only standard logical axioms
propext, Classical.choice and Quot.sound; the enumeration dependency has two
additional audited endpoints with the same standard axiom set.
No sorry/admit, new mathematical axiom, unsafe proof or external oracle.
Integrated into full `verify.py`, `lakefile.toml`, and `EndpointCheck.lean`.

## Subsequent combined endpoint

`ZeroDiamondRepair.lean`, using `FiniteGraphEditTransport.lean`, now combines
this representation with all verified repair and target bridges. Its endpoints
start directly from the original finite tournament and D=0, and give actual
finite differing-edge bounds to the independent carousel/doubling targets in
terms of the original squared row-sum energy. No color-word, normalization,
or target-identification premise remains in those endpoints. Positive-D repair
and the complete condition R remain outside the result.
