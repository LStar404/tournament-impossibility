# TransitiveFirstEnergy: exact first source-energy formula

For the actual finite transitive sign matrix `TransitiveOrbit.T n`, the module proves

    TwoBlockEnergy.first (T n) = (n : ℝ) * ((n : ℝ)^2 - 1) / 3.

The expanded `action_sum_sq` states the same identity as the sum of squares of T applied to the actual all-one vector. Every natural dimension is covered, including n=0 and n=1.

The proof computes the actual matrix action when the last vertex is adjoined: each old coordinate increases by 1 and the new coordinate is −n. The skew-matrix sum-action identity gives zero total old action, so the energy recurrence is E(n+1)=E(n)+n+n². The polynomial formula then follows by induction. No reference-energy formula is assumed.

Lean 4.35 compilation passed. Main log: verification/transitive_first_energy.log. The independent endpoint verification/TransitiveFirstEnergyEndpoint.lean expands the matrix entries to the literal +1/−1/0 comparison formula; its log is verification/transitive_first_energy_endpoint.log. Printed dependencies are only propext, Classical.choice and Quot.sound, with no sorryAx or added axioms.

This is a finite reference-energy identity, not the remaining asymptotic or stability parts of Assumption R.
