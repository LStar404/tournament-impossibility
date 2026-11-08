# TournamentColorEnumeration: finite ordered enumeration and switched representation

This module imports DiamondGap and ColorGraphRepair. It supplies a reusable
conditional bridge; its switching/transitivity premises must be proved by the
caller, and are not asserted for arbitrary tournaments.

## Transitive tournament enumeration

For an actual `DiamondGap.Tournament V` on a finite decidable vertex type,
`transitive_tournament_enumeration` assumes explicitly

    U.S a b = 1 → U.S b c = 1 → U.S a c = 1.

It proves that `U.S a b = 1` is a strict total order: irreflexivity follows
from the zero diagonal, strict totality from tournament unit entries and skew
symmetry, and transitivity from the stated premise. Mathlib's finite ordered
enumeration then gives an actual equivalence

    e : Fin (Fintype.card V) ≃ V

whose matrix entries satisfy `(U.S (e i) (e j) : ℝ) = orderSign i j`.
The empty vertex type is included; no inhabitant or positive-cardinality
assumption is used.

## Representation after a proved transitive switch

`representation_of_transitive_switch` takes actual tournaments T and U, a sign
function `d : V → ℤ`, and the explicit hypotheses:

* `∀ x, (d x)^2 = 1`;
* `∀ a b, U.S a b = d a * T.S a b * d b`;
* the transitivity implication above for U.

It constructs a genuine `List Bool` w of length `Fintype.card V`, together
with an ordinary enumeration e, and proves for all finite indices i,j:

    (T.S (e i) (e j) : ℝ) = ColorTransport.colorGraph w i j.

The word is constructed by `List.ofFn` from whether `d (e i) = 1`.
The ±1 fact follows from the square-one hypothesis, not an unproved sign
selection axiom. The list getter/color equality and the inverse switching
identity are proved explicitly.

The theorem does not regard switching as ordinary graph isomorphism. The
switch signs remain in the concrete word; e is only the ordinary vertex
enumeration. The final equality represents the ORIGINAL tournament T, not
merely the switched tournament U.

## Scope exclusions

The existence of a transitive switch, the diamond-free structural argument,
and any application to graph repair must come from separately verified
premises. This file does not prove every tournament is a color-word graph,
and does not prove R, Hamiltonian asymptotics, or analytic stability.

## Verification

Command: `lake env lean TournamentColorEnumeration.lean`.
Log: `verification/TournamentColorEnumeration.log`.
Both public endpoints compiled on 2026-11-08 with exit code 0 and no warnings.
`#print axioms` contains only propext, Classical.choice and Quot.sound.
No sorry/admit, new mathematical axiom, unsafe declaration or external oracle.
Integrated into full `verify.py`, `lakefile.toml`, and `EndpointCheck.lean`.
