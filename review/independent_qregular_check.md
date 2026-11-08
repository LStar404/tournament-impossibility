# Independent verification of the proposed unconditional digit-model obstruction

## Verdict

The proposed result is correct under the manuscript's definition of q-regularity (finite-dimensional complex span of the q-kernel). It needs no condition R. A slightly stronger general statement is available: a rational-valued q-regular sequence which converges has a rational limit. More generally, if b_n is rational-valued and b_n/n^k tends to an irrational limit for an integer k >= 0, then b_n is not q-regular in any fixed base q >= 2.

This is a mathematical verification, not a claim that this general observation is new in the literature.

## Lemma: descent of rational functions

If B(t) belongs to C(t) and its formal Taylor series belongs to Q[[t]], then B(t) belongs to Q(t).

Proof. Write QB=P with P,Q in C[t] and Q nonzero. Choose a Q-linearly independent basis beta_1,...,beta_s for the finite Q-vector space spanned by all coefficients of P and Q. Express P=sum_i beta_i P_i and Q=sum_i beta_i Q_i with P_i,Q_i in Q[t]. Every coefficient of Q_i B-P_i is rational. Comparing formal coefficients in sum_i beta_i(Q_i B-P_i)=0 gives Q_i B=P_i for every i. Some Q_i is nonzero, so B=P_i/Q_i is rational over Q. This argument does not require Q_i(0) nonzero; the identity takes place in the field of Laurent series and B is already known to be a Taylor series.

## Theorem and complete proof

Fix q >= 2 and an integer k >= 0. Let (b_n) be rational-valued and suppose b_n/n^k -> c, with c finite. If b is q-regular over C, then c is rational.

Choose a basis of its finite q-kernel span. With its values written as a column vector v(n), there are constant complex matrices M_r and a row ell with v(qn+r)=M_r v(n) and b_n=ell v(n). In particular,

b_(q^e)=ell M_0^e v(1), for all e >= 0.

Set x_e=q^(-ke)b_(q^e). Then x_e is rational and tends to c. Formally,

B(t)=sum_(e>=0) x_e t^e = ell(I-t q^(-k)M_0)^(-1)v(1),

so B belongs to C(t). The descent lemma gives B in Q(t). Because x_e is convergent it is bounded, so its series is analytic for |t|<1. Abel's limit theorem gives (1-t)B(t) -> c as t approaches 1 from below. A rational function over Q with a finite limit at the rational point 1 has a removable singularity there; after cancelling common powers of t-1, its value is a quotient of rational polynomial values. Thus c belongs to Q.

No assumption that the representation matrices have rational entries was made. No inversion of M_0 is required. The resolvent I-t q^(-k)M_0 has constant term I and is formally invertible.

## Applications to the actual sequences

1. a_n=P(n)/(n!/2^(n-1)) is rational and a_n -> L=cosh(1)/cos(1). The external asymptotic theorem and the manuscript's Lindemann-Weierstrass argument imply that L is transcendental, hence irrational. Apply k=0. Therefore a is not q-regular for every fixed q >= 2, independently of R.

2. m_n=n^2 a_n - 2*1_(2 divides n)*a_(n/2) is rational. The sequence a is bounded, hence m_n/n^2 -> L. Apply k=2 directly to m. This avoids asserting that division by n^2 preserves q-regularity (that assertion is not needed and should not be used).

3. P(n) itself is excluded even more simply by its factorial growth. If q-regular then |P(q^e)| <= C R^e for fixed C,R from the matrix representation. But the elementary tournament expectation lower bound P(n)>=n!/2^(n-1), evaluated at n=q^e, grows faster than R^e. Thus P is not q-regular. This does not imply non-P-recursiveness.

## Essential boundaries

- Here 'unconditional' means no additional R or extremizer-structure hypothesis; the cited extremal asymptotic theorem remains an external mathematical input.
- For a sequence beginning at n=1, choose any rational b_0. A finite initial modification cannot remove the irrational-limit obstruction.
- Only fixed-base, fixed-dimensional linear representations with constant matrices and linear output are excluded. Nonlinear output, n-dependent matrices, dimension growing with input, and general algorithms are not covered.
- Rationality of the coefficients matters: the constant sequence b_n=L is q-regular over C despite its irrational limit.
- The convergence assumption matters: a rational q-regular sequence need not converge at all.
- This obstruction does not yield non-D-finiteness, non-P-recursiveness, or a natural boundary. Those conclusions retain their own hypotheses and proofs.
- The lemma is a necessary obstruction, not a classification of rational-limit q-regular sequences.

## Scope of this check

Read the actual definitions of a_n, m_n and q-regularity in paper/nonalgebra_en.md. Verified the proof algebraically from the finite-kernel representation and supplied an independent elementary rational-function descent argument. No Lean execution or entire-manuscript re-verification was performed.
