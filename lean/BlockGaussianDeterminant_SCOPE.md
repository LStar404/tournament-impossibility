# BlockGaussianDeterminant scope

Focused Lean check passed (exit 0) and library olean was generated.
Log: `/workspace/shared/r_upstream_audit/block_gaussian_det.log`.
Printed axioms for determinant and inverse endpoints are only propext, Classical.choice, Quot.sound.

Defines interaction M=(S+vI)/n, actual block Q=[0 M; transpose(M) 0], and B=[I alpha(S+vI); alpha(-S+vI) I]. Proves B=I+zQ using the actual tournament's skew sign matrix. All transposes are ordinary complex transposes, not adjoints.

Under v²=1, proves the Schur complement is the existing gaussianMatrix, hence det B equals its determinant. Under beta!=0 and the true-unit premise for the actual quadratic resolvent at parameter(n,z), proves B is a true unit and proves both inverse identities. The true-unit premise is explicit, not inferred merely from totalized inverse notation. The matrix scaling theorem discharges the determinant transfer.

These exact finite identities do not require zero diamonds, positive n, energy bounds, or asymptotic estimates. Restriction v²=1 is essential for the particular beta used; no identification for all |v|<=1 is claimed. This module does not yet discharge the resolvent unit premise on eventual disks or identify rawLambda with the source exponent. No Gaussian integral, permanent recovery, or full Condition R is established here. Existing 140-module snapshot and integration files were not modified.
