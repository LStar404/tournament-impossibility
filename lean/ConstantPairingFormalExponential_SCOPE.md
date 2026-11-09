# Actual constant moments, pairing counts and scalar formal exponential

Four scalar formal-series modules; validation evidence is in verification/result.json.

ConstantPairingMoments defines W_m(c) as the ACTUAL full symmetric pairing
sum on Fin m with constant covariance c. It proves the residual cardinality
and uses the previously proved deletion recurrence and genuine finite-type
transport to obtain W_(m+2)=(m+1)c W_m. Empty and odd endpoints are inherited
from the actual pairing theorems. Induction proves
  W_(2k)(c)=pairFactor(k)*c^k,
where pairFactor(k)=product_{j<k}(2j+1). A separate Nat induction proves
pairFactor(k)*2^k*k!=(2k)!. No target moment formula is assumed.

ConstantPairingCount expands the actual constant-one edge products and full
sum to prove card(Pairing(Fin(2k)))=pairFactor(k), not merely a named count.

ConstantPairingFormalExponential works over any commutative Q-algebra.
actualSeries has coefficient W_m(c)*algebraMap(1/m!). Rational normalization
is proved from the factorial identity. Even/odd coefficient proofs establish
  actualSeries c = expand 2 (rescale (c/2) (PowerSeries.exp S)).
This is exp(c*t^2/2) as a FORMAL power series. The expand/rescale order is
explicit and correct; there is no substitution of a nonzero-constant series
into exp and no analytic convergence assertion.

ScalarWickFormalExponential constructs Occ(single Unit m) ≃ Fin m and proves
that the ACTUAL full polynomial Wick functional on X_unit^m equals W_m(c).
Its exponential generating series therefore satisfies the same formal exp
identity. This is not the old squarefree projection applied to powers.

All four candidates generated oleans by focused compilation, and printed
endpoints use only propext, Classical.choice, Quot.sound; no sorryAx.

Still missing: the independent label-assignment/multinomial bridge for a
general multivariate linear source, quadratic-source determinant branch and
formal exponential identity, analytic Gaussian/continuation interpretation,
uniform tail/recovery bounds and Condition R. This scalar formal theorem
must not be advertised as those general results.
