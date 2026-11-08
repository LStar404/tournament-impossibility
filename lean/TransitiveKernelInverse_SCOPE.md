# Exact transitive-kernel inverse

Focused Lean compilation passed. No aggregate verification or publication is
asserted by this scope note; integration is owned by the parent task.

For every m>=0 (matrix order m+1) and a in any characteristic-zero field,
`kernel_mul_numerator` proves A B=H_(m+1)(a) I, where A=I+aT with the existing
positive-above-diagonal transitive tournament matrix. B is the explicit
polynomial matrix:

* diagonal: H_m(a);
* i<j: -a (1-a)^(j-i-1) (1+a)^(n-j+i-1);
* i>j:  a (1+a)^(i-j-1) (1-a)^(n-i+j-1).

The polynomial identity needs no nonzero assumptions and includes a=0,1,-1.
`inverse_formula` assumes only H_(m+1)(a)!=0 and identifies the actual matrix
inverse with H_(m+1)(a)^(-1) times B. No determinant-inverse or adjugate formula
is supplied as a hypothesis. The proof uses sparse adjacent-row differences
and a sparse first-plus-last boundary equation, avoiding divisions by a or
1±a and avoiding finite geometric summation.

The two exported axiom reports contain only propext, Classical.choice,
Quot.sound. Log: /workspace/shared/r_upstream_audit/transitive_inverse_focused.log.

This module alone does not prove entry norm bounds, Euclidean inverse operator
bounds, transfer to arbitrary zero-diamond graphs, source estimates, or R.
Those are the next interfaces described in transitive_inverse_route.md.

Aggregate verification: all 130 delivered modules freshly recompiled PASS
at 2026-11-08T23:50:27.188634Z (zero retained records), all source hashes
match, and the aggregate lake build passed with 9177 jobs.
