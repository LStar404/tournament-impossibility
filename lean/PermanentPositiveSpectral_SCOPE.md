# Genuine positive integral and finite spectral permanent inequality

The new modules construct a positive radial-phase product model, rather than postulating Gaussian moments or positivity of a formal Wick functional. Radial measure is Lebesgue restricted to (0,infinity), phase measure is normalized Haar on AddCircle 1. The density exp(-t) is explicitly inside each integrand. The coordinate is t^(1/2) times the unit phase. No assertion that this model equals a separately defined Gaussian probability law is needed.

PermanentPositiveMoments and PermanentPhasePowers establish Gamma factorial moments, Fourier orthogonality, actual phase powers, and fractional radial integrability. PermanentRadialPhaseMoment proves absolute integrability of each genuine mixed monomial and computes its integral as delta(a,b)*a!. The fractional exponent (a+b)/2 controls unmatched powers as well. PermanentFiniteMixedIntegral lifts this to finite independent products and finite arbitrary mixed sums with termwise integrability proved.

PermanentLinearProductIntegral expands the actual products of matrix linear forms, with label multiplicities. PermanentAssignmentFiberCount gives a true equivalence between label-matching permutations and families of fiber equivalences, yielding the product-factorial count when multiplicities agree and zero otherwise. PermanentPolarization uses this count to prove the actual positive integral of density*prod(Xg)*conj(prod(Yg)) equals permanent(XY^H).

PermanentFactorEnergy uses the previously verified concrete spectral factors of an arbitrary square complex matrix. It proves both sum_i |(Xg)_i|^2 and sum_i |(Yg)_i|^2 equal sum_i s_i |g_i|^2. PermanentPointwiseAMGM proves the pointwise bound on the product of the two linear-form products using genuine arithmetic-geometric mean.

PermanentEnergyIntegral defines h_m(s) by the standard finite piAntidiag sum over exponent vectors of total degree m. It proves the energy majorant is integrable and its exact integral is m!*h_m(s), using the multinomial theorem and the exact multinomial factorial identity. PermanentSpectralBound legitimately integrates the pointwise bound under the positive measure, obtaining for every n>0 and every actual complex n-by-n matrix A:

  |permanent(A)| <= (n! / n^n) * h_n(s(A)),

where s(A) is the actual nonnegative square root of the Gram spectrum constructed in PermanentSpectralFrame. No singular-value ordering, invertibility, external factorization, assumed moment identity or assumed circle bound appears in this endpoint. The zero-dimensional case is not included in this stated inequality (the permanent itself is one there).

## Verification and limits
Focused compiler checks passed for all eleven modules, with endpoint axioms only propext, Classical.choice and Quot.sound. Final serial logs are recorded separately before aggregate integration; full aggregate verification and publication remain parent tasks.

This is a finite spectral permanent inequality, not yet the graph-family circle envelope or true high-degree asymptotic tail. Still required are quantitative spectral perturbation/rank-one estimates for the actual graph matrices, a suitable h_n bound, the normalized circle specialization and coefficient-tail recovery. Core multiplication, finite activity-window summation, and complete hypothesis R remain separate unfinished steps. The earlier circle-tail transfer still requires its circle bound until these steps are supplied.
