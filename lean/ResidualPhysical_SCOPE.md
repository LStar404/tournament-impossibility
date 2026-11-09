# Actual residual coefficients as locally finite physical W/eta moments

Five candidates after frozen 248. This is a new coefficient-level construction,
not a restatement of the core/residual factorization.

ResidualHomogeneity proves rescaling and coefficient-map identities for the
actual divided-power/mixed exponentials, then proves the actual local residual
coefficient equals c_m times a^m. c_m is the actual scalar residual coefficient,
not an assumed homogeneous coefficient. It works in an arbitrary commutative
algebra over a characteristic-zero field.

ResidualDegreeAssignments uses the real finite-product coefficient theorem to
expand actualResidual.coeff(m) over Finset.finsuppAntidiag univ m. It constructs
an occurrence word by concatenating replicate(d_i,i), proves its length is m
and its polynomial is prod_i Xi^d_i. Thus repeated numerical labels remain
separate occurrences rather than being squarefree-projected away.

ResidualPhysicalAssignments proves the expansion of each actual shifted tilted
residual coefficient as expand_2 of a finite sum of the previously established
physical W/eta moments. Its actual_coefficient theorem connects the actual
residualZ from 248 to the explicit finite sum over m<=2k and degree assignments
at each z coefficient k. below_order proves the m>2k terms vanish. These facts
provide the real local-finiteness/physical-moment link, without assuming the
activity formula and without evaluating a formal series at u=1.

PhysicalLowMoments derives same-label moments of orders 1 through 4 from the
actual occurrence recurrence. In particular the third is eta_i^3+3 eta_i W_ii
and fourth is eta_i^4+6 eta_i^2 W_ii+3 W_ii^2. The W_ii terms retain self-pairings.
These are true old tilted moments by the previously proved expand identity.

ResidualScalarActivities computes c0=1,c1=c2=0,c3=1/3,c4=-1/4 from the actual
scalar residual. A nonzero degree-assignment weight has each degree either 0
or >=3, and its number of active numerical coordinates is <=m/3. This count is
NOT the later structural-vertex count: logarithmic exponential vertices may
share the same numerical coordinate. Do not identify those two notions.

Quantifiers are finite algebraic ones; graph-energy/n estimates are not claimed.
The actual residualZ endpoint uses the existing Algebra Q S specialization;
generic coefficient and word results require a char-zero field as stated.
Empty index sets and zero-degree coefficients are retained.

Not completed: a simplified aggregate formula for residualZ's z^2 coefficient;
full logarithmic structural-vertex C_j expansion, its pair-counting factors,
repeated-vertex-label/self-loop enumeration and full j degree constraints;
uniform (Dj/n)^j bounds, truncated activity summation, independent permanent
true-tail estimates, falling-factorial restoration, fixed-depth common projection
and complete R. The low-order moment formulas are not advertised as full C1,
and Gaussian-core Taylor tails still do not replace the permanent true tail.
