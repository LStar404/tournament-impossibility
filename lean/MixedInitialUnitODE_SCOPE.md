# Actual mixed-source initial value, time derivative, unit and solved Ward ODE

Four modules extend batch 194 without changing its frozen source.

* `MixedWardUnit` computes the actual B=I+u²KA constant matrix as I, maps its determinant through constantCoeff, proves det B and B are genuine units, and establishes both nonsingular-inverse multiplication identities. No invertibility of covariance K is required.
* `MixedFormalTimeDerivative` derives the formal u derivative from actual divided-power coefficients, including the expand2 quadratic factor, proves E'=(L+2uH)E and proves the linear functional lift commutes with the u derivative. This is distinct from the previously proved polynomial partial derivatives.
* `MixedWardSolution` solves the ACTUAL Ward equations using that proved inverse. With V=B^-1 K and v=Vh, it proves G_i=u v_i Z and H_ij=V_ij Z+u²v_i v_j Z. It never divides by Z or assumes a covariance formula.
* `ActualMixedSourceTimeODE` proves W(1)=1 and Z(0)=1 from the actual empty pairing, proves Z'=sum h_i G_i−u sum A_ij H_ij from the actual polynomial series, and substitutes the actual solved moments to prove Z'=FZ with explicitly defined F:

 F = sum_i h_i u v_i − u sum_ij A_ij (V_ij+u²v_i v_j).

All quantities are formal series with scalar constants embedded by PowerSeries.C. Covariance and interaction symmetry hypotheses are explicit. No Gaussian measure or positivity is used. All quadratic forms are bilinear.

## Scope still open

The scalar ODE is now derived for the actual mixed Wick series. This batch does not yet prove ODE uniqueness, a general normalized determinant inverse-square-root, full Jacobi differentiation, or equality to the determinant-times-exponential candidate. Even-series descent to raw z, analytic branch matching/convergence, recovery bounds and full Condition R also remain separate. Only Z's initial value is asserted here; G/H initial values are not separately packaged.

All four focused checks pass with standard axioms propext, Classical.choice, Quot.sound. No target ODE or Ward equation is introduced as an external hypothesis.
