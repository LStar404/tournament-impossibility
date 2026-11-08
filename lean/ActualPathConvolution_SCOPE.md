# Exact actual-path convolution (S1): scope and provenance

## Proven endpoints

- `TournamentHamiltonian.actual_path_convolution_even_subsets` proves, for every actual tournament of positive order `n+1`,
  `2^n H = Σ_{U even} det(S[U]) permanent((J+S)[Uᶜ])`.
- `NonAlgebraicity.hamiltonianPathCount_convolution` is the identical theorem for this repository's existing `hamiltonianPathCount` and `Orientation` encoding. The conversion `asPathTournament` preserves the count definitionally (`rfl`).
- `weighted_path_sum` proves the exact factor `2^n`, using actual adjacent directed-edge products; no path-count identity is assumed.
- `odd_sign_principal_det_zero` proves the parity restriction by transpose invariance and determinant negation.

No asymptotic input, diamond-free hypothesis, analytic input, convolution hypothesis, `sorry`, or custom mathematical axiom is used. Positive order is written `n+1`; there is no silently truncated exponent at order zero.

## Reused finite proofs

Eight modules in `TournamentHamiltonian/` are copied unchanged from the author's public repository `LStar404/tournament-hamiltonian-paths`, commit `6144fe396da98debdf31baa10fd7388312189d9f`:

`Packing`, `Definitions`, `PositiveDeterminant`, `Hadamard`, `Orientation`, `PathConvolution`, `PathConvolutionCoefficients`, `PathConvolutionGenerating`.

In particular the generic arbitrary-real-matrix endpoint `complement_det_per_convolution_bool_eq_cycles`, together with `sum_path_products_eq_marked_cycles`, supplies the combinatorial cycle cancellation proof. Taking `A=J+S` makes `J−A=−S=Sᵀ`. Thus this is not a redefinition of the desired path count, nor an assumption of the paper's generating-function argument.

The older positive adjacency convolution is a different normalization; the new file explicitly bridges to the supplement's `J+S` normalization rather than conflating them.

## Not yet covered

The zero-diamond *two-permanent average* is NOT an endpoint of this batch. It still requires formal proof that every even principal sign minor of a diamond-free tournament has determinant one, plus the diagonal-permanent subset expansion/parity average. The general S1 theorem does not remove these obligations. Nor does this batch prove R, asymptotic recovery, or global classification.

## Build

All eight upstream modules were actually recompiled sequentially on the current Lean 4.35.0 / pinned mathlib environment (not trusted as pre-existing binaries). The new bridge was compiled separately. Integration into the repository manifest and whole-project build is the integrator's next step; this file does not claim that integration has already happened.

The fresh independent `#print axioms` check reported for both S1 endpoints and the reused positive-convolution endpoint exactly `[propext, Classical.choice, Quot.sound]`; the final compile/check process exited with status 0.
