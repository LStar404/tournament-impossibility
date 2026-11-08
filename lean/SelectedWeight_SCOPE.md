# SelectedWeight scope

For any finite strictly increasing enumeration f of k indices in [0,n), selected_index_le proves f(j) ≤ n−k+j. Therefore a descending vector's selected coordinates dominate its last k coordinates termwise. selected_weight_ge proves the required comparison with weights 1,1,3,3,... . The increasing enumeration and index bounds are explicit input hypotheses, not arbitrary selected values postulated to satisfy the target inequality.

This module does not construct an enumeration from a Finset or identify the k largest |Bx| coordinates. It is the selected-coordinate optimization component, not the complete tournament selected-row inequality or Assumption R.

Integrated into `lakefile.toml`, full `verify.py`, and `EndpointCheck.lean`;
compiler/axiom output is retained in `verification/SelectedWeight.log`.
