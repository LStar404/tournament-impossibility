# SelectedWeight scope

For any finite strictly increasing enumeration f of k indices in [0,n), selected_index_le proves f(j) ≤ n−k+j. Therefore a descending vector's selected coordinates dominate its last k coordinates termwise. selected_weight_ge proves the required comparison with weights 1,1,3,3,... . The increasing enumeration and index bounds are explicit input hypotheses, not arbitrary selected values postulated to satisfy the target inequality.

This module does not construct an enumeration from a Finset or identify the k largest |Bx| coordinates. It is the selected-coordinate optimization component, not the complete tournament selected-row inequality or Assumption R.

Integrated into `lakefile.toml`, full `verify.py`, and `EndpointCheck.lean`;
compiler/axiom output is retained in `verification/SelectedWeight.log`.

## Subsequent complete finite vector-majorization bridge

TournamentEnvelope, TournamentSwitching, TopAbsoluteSelection and
SelectedTournamentMajorization now construct the actual matrix selected-row
envelope, selected subsets/signs, sorting and signed-permutation bridges, proving
sortedPad(Bx) weakly majorized by K(sortedPad(x)) for every actual finite tournament
and real input. `VectorMajorizationEndpoint.lean` checks the expanded inequality
from raw matrix entries. Earlier exclusions about these particular bridges
above are superseded. Reference K-orbit identities, moment comparisons and R
remain separate, unproved obligations.
