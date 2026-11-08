# TournamentSourceEnergy scope

This file defines cycleCount as the cardinality of the actual set of ordered triples (i,j,k) with B_ij=B_jk=B_ki=1, for a genuine finite tournament sign matrix B. It does not define a triangle count by the desired energy deficit. These conditions automatically exclude repeated vertices.

The proof uses the pointwise polynomial indicator identity
4*(cyc(i,j,k)+cyc(i,k,j)) = 1 - 1_{i=j=k} + B_ij*B_jk + B_jk*B_ki + B_ki*B_ij.
Summing over all triples gives the division-free identity
8*cycleCount = n^3 - n - 3*sum_i (sum_j B_ij)^2.
The source-vector interface first_eq_reference_sub uses the same actual matrix as TournamentPowerComparison and TwoBlockEnergy.

The counting convention is ordered: mathematically a cyclic unordered three-set has three forward cyclic orderings. The exported statement uses cycleCount/3 as a real number and does not require or claim a separate Lean theorem about divisibility by three or an independently defined unordered-triangle cardinality.

No claim about infinite sequences, Assumption R, or classification of near-extremizers follows from this module alone.

Verification completed: Lean 4.35.0 main compilation and independent expanded endpoint both exit 0. Logs are verification/tournament_source_energy.log and verification/source_energy_endpoint.log; endpoint source is verification/SourceEnergyEndpoint.lean. All audited axioms are only propext, Classical.choice, Quot.sound; no sorry/admit/new axiom.
