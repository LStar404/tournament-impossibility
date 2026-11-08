# Local ordered cancellation: formalized scope

`OrderedCancellation.lean` is an independent local lemma, not a proof of Condition R.

## Formal statements

For any unital ring (multiplication need not commute), an explicitly supplied descending multiplicative additive filtration F, and a−1,b−1 in F₁, define

P₀⁺=a, P₀⁻=b,
Pₙ₊₁⁺=Pₙ⁺Pₙ⁻, Pₙ₊₁⁻=Pₙ⁻Pₙ⁺.

`difference_order` proves Pₙ⁺−Pₙ⁻ ∈ Fₙ₊₁. The proof uses the exact identity

AB−BA=(A−B)(B−1)−(B−1)(A−B).

`observable_equal` proves equality after applying an additive observable explicitly assumed to vanish on Fₙ₊₁. A coefficient functional is not silently assumed to have this property.

The extension includes:

- `words_length`: both recursively defined complementary dyadic words have length 2ⁿ.
- `evaluate_words`: their ordered products are exactly Pₙ⁺ and Pₙ⁻.
- `blocks_add`: first forming q levels and then n packet levels equals q+n original levels, without commuting any factors.
- `list_product_residual`: a finite product of factors equal to one modulo F₁ remains so.
- `expandPackets_prod`: expanding each high-bit sign into its full positive/negative packet preserves the ordered product.
- `packet_length`: packets of length 2^q expanded along r−q high levels have total length 2^r, provided q≤r.
- `packet_difference_order`: such packets, with every factor equal to one modulo F₁, have sign-odd difference in F_(r−q+1).

The finite packet interface models a low-position period cost q. It neither assumes nor proves that any particular tournament kernel admits that interface.

## Not formalized

This module does not yet provide:

- a concrete noncommutative formal-power-series degree filtration and coefficient observable;
- the identification with a `popcount`-indexed Thue–Morse sequence;
- polynomial-weight auxiliary insertions or weak-order/collision decompositions;
- the kernel-specific degree/period bound a+q≤h+b;
- extremal structure, permanent recovery, uniform remainder estimates, or Condition R.

Thus the accurate statement is: **the abstract noncommutative filtered recursion and finite low-position packet interface are formalized**. It is not accurate to say that the whole weighted cancellation argument or R has been formalized.

## Verification

The module is included in `lakefile.toml`, the direct compiler check `verify.py`, and the public endpoint audit `EndpointCheck.lean`. All hypotheses are explicit parameters, not additional axioms. The principal cancellation and packet theorem depend only on `propext` and `Quot.sound`; the generic observable corollary also uses `Classical.choice`.
