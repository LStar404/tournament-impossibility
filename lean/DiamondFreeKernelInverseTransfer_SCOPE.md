# Actual zero-diamond inverse-entry transfer

Actual zero-diamond structure yields a diagonal +/-1 switch and ordinary
vertex enumeration to a transitive skew matrix. This module proves the
corresponding exact conjugation identity for full kernel inverses and an
explicit signed representation of every entry. No spectral hypothesis or
compatible choice across graph orders is needed.

The algebraic identity also holds at singular parameters for Lean's totalized
inverse; it alone does not claim invertibility at such parameters. Downstream
bounds explicitly exclude zero finite determinants. Focused Lean check passed
with standard logical axioms only; aggregate integration is tracked separately.

Aggregate verification: all 130 delivered modules freshly recompiled PASS
at 2026-11-08T23:50:27.188634Z (zero retained records), all source hashes
match, and the aggregate lake build passed with 9177 jobs.
