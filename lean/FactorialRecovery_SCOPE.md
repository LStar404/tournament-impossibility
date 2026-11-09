# True factorial ratio: fixed-order remainder and actual activity multiplier recovery

FiniteFactorialRecovery ports the upstream proof of rho(n,k)=n^k/(n.descFactorial k), positivity, logarithmic and exponential bounds, and rho<=sigma^k in an explicit window. It uses the actual finite-n ratio.

RecoveryHomogeneousList defines H through the finite geometric-product convolution for a list of nonnegative real nodes. It proves nonnegativity, H_0=1, the one-step bound H_(a+1)<=sum(nodes)*H_a, and its iterated form. This suffices for the tail estimate without assuming a stronger multidegree-submultiplicativity theorem.

RecoveryHomogeneousEvaluation proves the actual HasSum identity for the finite product of geometric factors when each node*z is in [0,1). Its positive fixed-order remainder is bounded by product*(sum(nodes)*z)^(p+1). Summability and evaluation are proved, not provided as premises.

RecoveryFiniteOrderRemainder constructs precisely the nodes 0,...,k-1, proves the finite geometric product at z=1/n equals the true rho(n,k), and obtains, for n>0 and k<=n,

  0 <= rho(n,k)-sum_(a<=p) H(k,a)/n^a
     <= rho(n,k)*(k^2/n)^(p+1).

The full range k<=n is valid because each node i is strictly smaller than n. Empty-node and k=1 cases are included. No coefficient-to-Euler-polynomial identification is claimed here.

WeightedPolynomialMultiplier proves a spare-radius finite-window bound for arbitrary complex coefficients. Its constant is the genuinely convergent positive sum B_m(t)=sum_k k^m*t^k with 0<=t<1. FactorialWeightedRemainder combines this with the actual ratio remainder, giving a fixed-order weighted error proportional to n^(-p-1)*||F||_s; explicit finite-window inequalities are retained.

ActivityFactorialMultiplier applies the estimate to the actual graph activity series proved in the preceding batch. For 1<=j<=p, the order p-j multiplier error has an n^(-p-1) bound with constants independent of n. The j=0 activity is exactly one and has exactly zero factorial-multiplier error.

FactorialLinearWindow supplies a concrete positive window k<=floor(alpha*n), alpha=log(17/16)/2. At r=1 and s=9/8, sigma=17/16 and t=17/18, all window inequalities are proved from membership. The resulting graph activity bound does not assume a window estimate or a factorial remainder.

## Boundaries
This batch treats each actual activity's multiplier recovery. Multiplying by the actual core, summing the finite activity window and the finite-order approximation, and estimating the genuine permanent high-degree tail remain separate steps. In particular the permanent circle envelope, finite-n tail recovery and the complete hypothesis R are not supplied by these theorems. The graph family remains the previously verified chosen-enumeration family; canonical popcount identification is unchanged. Three independent permanent tools are also verified in this batch: PermanentPolynomialCircleTail transfers an explicitly assumed actual circle bound to the actual polynomial tail; PermanentSpectralFrame and PermanentSpectralFactors construct XYᴴ=A and both factor Grams=diag(s), including singular cases. They do not establish the required circle envelope. PermanentPositiveMoments remains outside this batch.
