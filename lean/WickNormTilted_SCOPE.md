# Uniform core norms/truncation and arbitrary polynomial tilted recurrence

Five candidates beyond frozen 230.

## Actual analytic core estimates
ActualWickCoefficientBounds proves an explicit M(s,R,K)=exp(s)/cos(R)+GaussianSourceProduct.errorConstant(s,R,K), with M≥0. For 0≤rho<s<R<pi/2, K≥0, a single eventual n threshold works for all D0 tournaments with scoreEnergy≤K*n and all v²=1. It proves |actual Wick coefficient k|≤M/s^k and weighted coefficient-l1 summability with total ≤M/(1−rho/s). The graph sphere bound is derived from the existing actual O(1/n) product estimate and actual target bound; it is not an input assumption.

WickGeometricTruncation proves the generic shifted absolute tail and complex Taylor remainder bounds, including m=0 and rho=0. ActualWickTruncation discharges the hypotheses with the actual graph coefficient bound and actual HasSum, obtaining uniformly for all m and |z|≤rho:
|product(T,v,z)−sum_{k<m} actualCoefficient(T,v,k) z^k| ≤ M*(rho/s)^m/(1−rho/s).
This is the analytic Gaussian/Wick core Taylor tail, NOT the finite matching/permanent true-tail theorem.

## Actual arbitrary polynomial insertion algebra
PolynomialInsertionWard derives the full inserted Ward matrix system for every MvPolynomial R, from the existing true full-Wick IBP and inserted exponential derivative. It does not extrapolate from only the one/two insertion results.
PolynomialTiltedRecurrence solves that system using the actual proved inverse B^-1, yielding
P_(Xi R)=sum_j V_ij P_(partial_j R)+u*response_i P_R.
It proves Z is a PowerSeries unit from its actual constant coefficient 1, defines tilted(R)=P_R*Z^-1, proves tilted(1)=1, and the actual normalized recurrence. Repeated polynomial indices are not removed.

The recurrence is for the unscaled X variables, with mean u*response and covariance V. The physical y=uX recurrence and exact z-descended W/eta identification have NOT yet been added in this batch. Nor have residual-activity diagram enumeration, local finiteness/counting bounds, permanent true tail, factorial restoration or full Condition R been proved.

Frozen 230 source/aggregation files were not edited. Each new module has an explicit successful focused exit and standard logical axioms only; final serial results are recorded separately.
