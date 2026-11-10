# Non-algebraicity of the Extremal Hamiltonian Path Sequence and Formula Restrictions

Xingchen Liu

School of Mathematics, Sichuan University

`lxc-em5158@outlook.com`

10 November 2026 · Local revision v0.4.1

## Abstract
Let $P(n)$ be the maximum number of directed Hamiltonian paths in an $n$-vertex tournament, and put $a_n=2^{n-1}P(n)/n!$. An existing asymptotic theorem gives $a_n\to L=\cosh1/\cos1$. We supplement it with a formal sharp bound $a_n=L+O(1/n)$ and linear raw score energy for actual maximizers, using a spectral-moment comparison and a positive log-ratio expansion. Rationality of the coefficients and transcendence of $L$ imply non-algebraicity of the ordinary, exponential and half-scale remainder generating functions. The same limit also excludes finite-dimensional linear digit representations in every integer base: more generally, a rational-valued $q$-regular sequence with a finite limit after division by an integer power of $n$ has a rational limit. Separately, an explicit radial boundary condition R implies a natural boundary, non-P-recursiveness and necessary cancellation identities for mixed derivative--contraction relations. R is an additional hypothesis for the actual extremal sequence, not a consequence of its asymptotic limit. These results exclude specified classes of formulas, not all closed forms or efficient algorithms.

Keywords: tournaments; Hamiltonian paths; extremal counting; generating functions; $q$-regular sequences.

## The problem and the line of attack
In a tournament any two distinct vertices are joined by exactly one directed edge. A directed Hamiltonian path traverses every vertex exactly once, following the edge directions. Let $H(T)$ be the number of vertex permutations of a tournament $T$ that form such a path, and set
$$
P(n)=\max_{|V(T)|=n}H(T).
$$
To study exact expressions for $P(n)$ this paper first examines several families of formulas that can be excluded.

To separate the main growth of $P(n)$ we normalise by the expected number of paths in a random tournament:
$$
\mu_n=\frac{n!}{2^{n-1}}.
$$
There are $n!$ vertex permutations, and in each of them the $n-1$ consecutive edges have the required directions with probability $2^{-(n-1)}$, which gives the average above. Introduce the normalised quantity
$$
a_n=\frac{P(n)}{\mu_n},
$$
the ratio of the maximal number of paths to the random average. The asymptotic theorem of Divoux and Wang [1, Theorem 1.4] gives
$$
a_n\longrightarrow L=\frac{\cosh1}{\cos1}.
$$
This known limit is the starting point of the analytic argument. Theorem 4 below also derives the stronger error $a_n=L+O(1/n)$ from the established matrix-moment and path-comparison estimates, with an explicit bridge to the formal sequence encoding.

Define the generating function of the sequence $(a_n)$ by
$$
A(z)=a_1z+a_2z^2+\cdots=\sum_{n\ge1}a_nz^n.
$$
A generating function encodes the whole sequence as one function, which makes it possible to ask which equations it can satisfy. Restricting the form of a generating function is not the same as excluding all closed formulas for its coefficients.

## Exclusions that do not depend on structural classification
A function is called algebraic if it satisfies a nonzero polynomial equation $F(z,G(z))=0$; rational functions and algebraic expressions such as square roots belong to this class.

**Result 1.** $A(z)$ is not algebraic. The exponential generating function of the original extremal sequence,
$$
E(z)=\sum_{n\ge1}\frac{P(n)}{n!}z^n=2A(z/2),
$$
is not algebraic either. The conclusion holds even when the coefficients of the equation may be arbitrary complex numbers.

The proof uses two facts: the constant $L=\cosh1/\cos1$ is transcendental, that is, it is not a root of any nonzero polynomial with rational coefficients; and every $a_n$ is rational. If $A$ were algebraic, then, because its power-series coefficients are rational, the following limit, whenever it exists and is finite, would have to be algebraic:
$$
\lim_{z\to1^-}(1-z)A(z).
$$
By the known asymptotics this limit equals $L$, contradicting its transcendence. The complete argument is Appendix A.

We next examine a recurrence that relates scale $n$ to scale $n/2$, and study its remainder. For the actual sequence $(a_n)$, define $m_n$ at even $n$ by
$$
n^2a_n=2a_{n/2}+m_n,
$$
and at odd $n$ by $m_n=n^2a_n$. The generating function of the remainder is
$$
M(z)=\sum_{n\ge1}m_nz^n.
$$
**Result 2.** $M(z)$ is not algebraic either. Hence the remainder of this half-scale recurrence cannot have a rational or algebraic generating function.

The proof follows the same pattern as Result 1, with the limit
$$
\lim_{z\to1^-}(1-z)^3M(z)=2L.
$$
Result 2 can be used to screen candidate remainders for the recurrence above: if such a remainder had a rational or algebraic generating function, it could not recover the actual $P(n)$. The restriction concerns the form of the remainder only; it does not exclude the recurrence itself.

**Result 3.** For every integer base $q\ge2$, neither $(a_n)$ nor $(m_n)$ is $q$-regular over $\mathbb C$. In other words, neither sequence admits a fixed-dimensional representation by constant matrices reading the base-$q$ digits and a fixed linear output. The obstruction is the rational-valued limit criterion proved in Theorem A.5, applied with $a_n\to L$ and $m_n/n^2\to L$. The unnormalised sequence $P(n)$ is excluded by its factorial growth instead. None of these exclusions requires R; they concern linear digit representations, not arbitrary algorithms.

## Further results under an additional condition
Stronger restrictions depend on the boundary behaviour of $A(z)$ on the unit circle. Write R for the required additional condition: at a set of increasingly dense points on the unit circle, a specified derivative (whose order depends on the point) exhibits a logarithmic divergence of prescribed strength for the first time. The boundary points, the order of the derivative and the coefficient of the divergence are given in Appendix B, which also provides a sufficient criterion for R.

**Every conclusion in this section assumes that the actual $A(z)$ satisfies R. This paper does not prove that assumption.**

If R holds, the unit circle is the natural boundary of $A$: $A$ cannot be continued analytically from the interior of the disc across any point of the circle. Such boundary behaviour restricts the finite equations the function can satisfy.

Using the sharper boundary behaviour prescribed by R one also obtains the following two families of exclusions.

- **Fixed-order linear recurrences with polynomial coefficients.** $P(n)$ cannot eventually satisfy a nontrivial relation $\sum_{j=0}^{d}p_j(n)P(n+j)=0$ with fixed order $d$ and polynomial coefficients $p_j$. This does not exclude other kinds of recurrence.

- **Certain contraction formulas.** These are finite linear relations among the functions $A(z)$, $A(z^2)$, $A(z^3)$ and so on. If the relation contains no derivatives, has rational-function coefficients in $z$, and after clearing denominators its right-hand side continues analytically across every point of the unit circle except finitely many, then the relation cannot hold. When derivatives are allowed a whole family is still excluded for integer bases that are not powers of two; binary contractions are not fully excluded. The complete range is Appendix C.

These restrictions concern neighbouring-term recurrences and integer contractions of generating functions. The mixed derivative--contraction theorem gives necessary cancellation identities, not sufficient conditions for a relation to exist. A natural boundary alone does not rule out Mahler-type equations; the finer radial information in R is essential (compare [6]). The D-finite restrictions use the classical finite-singularity principle [3,5].

## Scope of the conclusions
Non-algebraicity of a generating function does not imply that its coefficient sequence lacks a simple closed formula. For example $1/n$ has a simple closed formula, while its generating function $-\log(1-z)$ is not algebraic.

A natural boundary does not exclude short recurrences either. Appendix E gives an example, different from the actual extremal sequence: odd indices vanish and even indices satisfy
$$
s_n=-\frac1n+\frac{2}{n^2}s_{n/2}.
$$
The generating function of this sequence has a natural boundary, yet $s_n$ can be computed exactly by repeated halving. A natural boundary and a short evaluation rule are therefore not in conflict.

The scope of the results above is as follows.

- **Proved for the actual extremal sequence:** the actual $A$, $E$ and $M$ are not algebraic, and $a_n,m_n,P(n)$ are not $q$-regular for any $q\ge2$. The graph-theoretic limit is both externally known and supplied by Theorem 4; no additional classification of extremal tournaments is needed. The formal non-algebraicity and normalized non-$q$-regularity applications retain the stated transcendence-theory input.

- **Conditional on R:** the natural-boundary, non-P-recursiveness and contraction conclusions. The research notes contain a route to R whose upstream structural dependencies are specified in Appendix B; those dependencies are not all reverified here.

- **Still open here:** whether $P(n)$ admits an exact closed form of some other kind, whether an efficient exact algorithm exists, and whether the actual remainder $M$ has a transcendental expression that can be evaluated independently.

No NP-hardness statement or general algorithmic lower bound is obtained. Establishing R for the actual extremal sequence requires additional verified input.

## Sharp path asymptotics and the remaining structural gap
**Theorem 4 (uniform sharp bound and maximizer energy).**
There exist $C,D\ge0$ and $N\ge2$ such that, for every $n\ge N$,
$$
 \left|\frac{P(n)}{\mu_n}-L\right|\le\frac Cn,
 \qquad \frac{H(T)}{\mu_n}\le L+\frac Cn
 \quad\hbox{for every $n$-vertex tournament }T.
$$
Every maximizing tournament of such order also satisfies
$$
 \tau(T):=\sum_i\left(\frac{s_i}{n-1}\right)^2\le\frac Dn,
 \qquad s=S\mathbf1,
 \qquad \sum_i s_i^2\le Dn.
$$
Here $S$ is the skew sign matrix and $s_i$ is outdegree minus indegree.
The constants and threshold are independent of the tournament. No energy
bound is asserted for arbitrary, nonmaximizing tournaments. The raw energy
bound is linear, not bounded independently of $n$.

**Traceable proof inputs.** The all-power input is
`actual_all_integer_moments` in `lean/ReferenceMomentEndpoint.lean`; the spectral bridge is
`SpectralMomentBridgeCandidate.paired_moments_le_transitive`, followed by
`ActualSharpSpectralCandidate.actual_spectralRatio_upper_uniform`.
The path, entrance and reference inputs are respectively
`ActualCappedPathUpperCandidate.actual_capped_path_upper`,
`ActualExceptionalAssemblyCandidate.actual_maximizers_eventually_capped`, and
`ActualMaxPathsLowerCandidate.actual_maxPaths_lower_uniform`.
These are proved endpoints, not additional hypotheses. The resulting bounds are
`ActualSharpPathEnergyCandidate.actual_maxPaths_abs_error_uniform` and
`ActualSharpPathEnergyCandidate.actual_maximizers_energy_O_inv`; the actual
sequence connection is
`ActualExtremalAsymptoticCandidate.actual_ExtremalAsymptotic`.

**Spectral comparison.** Let $T_n$ denote the transitive sign matrix.
The established all-power Frobenius comparison for actual tournament matrices is
$$
 \|S^r\|_F^2\le\|T_n^r\|_F^2\qquad(r\in\mathbb N).
$$
To pass from this matrix statement to the spectral ratio, let $\lambda_j>0$
be the positive skew frequencies, counted with multiplicity, and set
$x_j=(\lambda_j/n)^2$. Unitary diagonalization and pairing the positive
and negative frequencies give, for $r\ge1$,
$$
 \|S^r\|_F^2=2n^{2r}\sum_jx_j^r.
$$
Zero frequencies contribute zero here; the restriction $r\ge1$ is essential.
Writing $y_j$ for the corresponding transitive masses, the matrix comparison
therefore gives $\sum_jx_j^r\le\sum_jy_j^r$ for every positive integer $r$.
The lists may have different lengths; multiplicities are retained.

The previously proved operator bound gives $0\le x_j,y_j<1/2$.
The actual determinant ratio has the paired-product expression
$$
 \rho(T)=\prod_j\frac{1+x_j}{1-x_j},\qquad
 \log\frac{1+x}{1-x}=2\sum_{k\ge0}\frac{x^{2k+1}}{2k+1}\quad(0\le x<1).
$$
The series converges and its coefficients are positive. Finite summation
and the positive odd-moment inequalities imply
$\log\rho(T)\le\log\rho(T_n)$, hence $\rho(T)\le\rho(T_n)$.
This argument uses power moments, not majorization of the ordered squared
frequencies. The actual transitive determinant-ratio estimate gives
$|\rho(T_n)-L|\le C_s/n$ eventually. Thus the old packing upper constant
$U>L$ can be replaced by $L+C_s/n$ at the spectral step.

**Path and energy closure.** The established reference lower bound is
$P(n)/\mu_n\ge L-C_r/n$. Actual maximizers eventually satisfy the fixed
score cap and logarithmic energy entrance needed for the strong path estimate
$$
 \frac{H(T)}{\mu_n}\le\rho(T)e^{-\tau(T)/2}+\frac{C_p}{n}.
$$
These entrance conditions are conclusions, not extra assumptions on the
maximizer. Since $e^{-\tau/2}\le1$, the sharp spectral estimate yields
$$
 L-\frac{C_r}{n}\le\frac{P(n)}{\mu_n}
 \le L e^{-\tau(T)/2}+\frac{C_p+C_s}{n}.
$$
Dropping the exponential proves the uniform absolute error bound; every
other tournament inherits the upper bound from the finite maximum.
Put $B=C_r+C_p+C_s$. For $B/(Ln)\le1/2$ the same inequality gives
$e^{-\tau/2}\ge1-B/(Ln)$ and
$\tau\le-2\log(1-B/(Ln))\le4B/(Ln)$.
Finally $\sum_i s_i^2=(n-1)^2\tau\le Dn$. This proves the stated bounds
from the established moment, reference and path-comparison ingredients.

**Connecting the formal sequence encodings.** The path-bound development
uses actual tournaments, while the generating-function development uses a
redundant orientation encoding. Each orientation defines an actual tournament,
and every tournament has a representing orientation. Their Hamiltonian orders
are the same vertex permutations, so both path counts and their finite maxima
coincide, including at order zero. For $n>0$, the rational coefficient in the
second development is therefore exactly $P(n)/\mu_n$. The zero constant-term
convention changes no limit. The real constant $L$ maps to the same complex
constant used in the analytic argument. The uniform error bound consequently
proves the actual `ExtremalAsymptotic` interface rather than assuming it.

The new interface directly supplies the asymptotic argument in the existing
non-algebraicity theorems for $A$, $E$ and $M$, and in the non-$q$-regularity
theorems for $a_n$ and $m_n$. Their formal proofs still require
`FourExponentialIndependence`, the stated Lindemann--Weierstrass input.
For the raw counts $P(n)$, the separate conclusion is that no constants
$C_0,D_0\ge0$ bound all terms by $C_0D_0^n$; this growth obstruction has
no external asymptotic or transcendence premise. These are distinct claims
about normalized coefficients and unnormalized counts.

Neither the sharp scalar error nor linear raw energy establishes zero diamonds,
a canonical extremizer classification, the all-order expansions F, or the
common all-multiples jump J. The new scalar estimate supplies only the
order-zero expansion. The conditional R conclusions remain conditional.
The current theorem does not supply the higher coefficients or structural information needed for J and R.

## Appendix A. Complete proof of the unconditional results
This appendix proves Results 1--3 of the main text. We keep the notation $A,E,M$ of the main text and write $\Theta=z\frac{d}{dz}$.

**Lemma A.1.** $L=\cosh1/\cos1$ is transcendental.

**Proof.** If $L$ were algebraic, then
$$
e+e^{-1}-Le^i-Le^{-i}=0.
$$
The exponents $1,-1,i,-i$ are four distinct algebraic numbers and the coefficients $1,1,-L,-L$ are algebraic numbers not all zero. This contradicts the Lindemann--Weierstrass theorem [2]. Since $\cos1\ne0$ the expression is defined.

**Lemma A.2 (descent of algebraic relations).** If $B(z)\in\mathbb Q[[z]]$ is algebraic over $\mathbb C(z)$, then it is algebraic over $\mathbb Q(z)$.

**Proof.** After clearing denominators take a nonzero relation $H(z,B(z))=0$ with $H\in\mathbb C[z,Y]$. Choose a rational linear basis $\beta_1,\ldots,\beta_s$ of the finitely many complex coefficients and write
$$
H(z,Y)=\sum_{j=1}^s\beta_jH_j(z,Y),\qquad H_j\in\mathbb Q[z,Y].
$$
Each $H_j(z,B(z))$ has rational power-series coefficients. Comparing coefficients and using the rational linear independence of the $\beta_j$ gives $H_j(z,B(z))=0$ for every $j$. At least one $H_j$ is nonzero, which is the required relation.

**Lemma A.3 (finite radial limits).** Let $B\in\mathbb Q[[z]]$ be analytic in the unit disc and algebraic over $\mathbb C(z)$. If some integer $d\ge0$ makes $(1-\rho)^dB(\rho)$ tend to a finite limit $c$ as $\rho\uparrow1$, then $c$ is algebraic.

**Proof.** By Lemma A.2, $C(z)=(1-z)^dB(z)$ satisfies a nonzero relation $R(z,C(z))=0$ with $R\in\mathbb Q[z,Y]$. Removing the highest common power of $(z-1)$ from the coefficients of $R$ as a polynomial in $Y$, we may assume $R(1,Y)\not\equiv0$. Taking the radial limit gives $R(1,c)=0$, which proves the claim; if $R(1,Y)$ is a nonzero constant we already have a direct contradiction.

**Theorem A.4.** $A(z)$, $E(z)$ and
$$
M(z)=\Theta^2A(z)-2A(z^2)
$$
are all transcendental over $\mathbb C(z)$.

**Proof.** The coefficients $a_n$ are rational and tend to $L$, so Abel's limit gives $(1-\rho)A(\rho)\to L$. Lemmas A.1 and A.3 exclude algebraicity of $A$; the rescaling identity then excludes algebraicity of $E$.

Write $M(z)=\sum_{n\ge1}m_nz^n$. Then
$$
m_n=n^2a_n-2\mathbf1_{\{2\mid n\}}a_{n/2},\qquad m_n\in\mathbb Q,\qquad \frac{m_n}{n^2}\longrightarrow L,
$$
where no half-integer index is needed when the indicator vanishes. Using
$$
\sum_{n\ge1}n^2\rho^n=\frac{\rho(1+\rho)}{(1-\rho)^3}
$$
we get $(1-\rho)^3M(\rho)\to2L$. Concretely, split $m_n/n^2-L$ into a finite prefix and a tail of absolute value below any given $\varepsilon$; the finite prefix tends to zero and the tail contributes at most $2\varepsilon$ in the limit. Letting $\varepsilon\downarrow0$ finishes the argument. Lemma A.3 again contradicts the transcendence of $L$.

Consequently the concrete equation $\Theta^2A-2A(z^2)=F$ cannot have an algebraic right-hand side, even when the algebraic relation may use arbitrary complex constants. Multiplying by a nonzero rational function or adding an algebraic function cannot make $M$ algebraic either. This does not exclude $M$ being a transcendental D-finite function: for instance $e^z/(1-z)^3$ has rational Taylor coefficients and is D-finite, yet its normalised radial limit is the transcendental number $e$.

**Theorem A.5 (rational limits of regular sequences).** Let $u_n\in\mathbb Q$ for $n\ge0$, and let $d\ge0$ be an integer. If $u$ is $q$-regular over $\mathbb C$ for an integer $q\ge2$ and $q^{-de}u_{q^e}\to c$ as $e\to\infty$, then $c\in\mathbb Q$. In particular, if $u_n/n^d\to c\notin\mathbb Q$, then $u$ is not $q$-regular.

**Proof.** The $q$-kernel consists of the sequences $(u_{q^e n+r})_{n\ge0}$, where $e\ge0$ and $0\le r<q^e$; regularity means that their complex linear span is finite-dimensional [4]. A basis, arranged as a column $v(n)$, gives constant matrices $M_j$ and a row $\ell$ satisfying $v(qn+j)=M_jv(n)$ and $u_n=\ell v(n)$. Hence $u_{q^e}=\ell M_0^ev(1)$. The rational numbers $b_e=q^{-de}u_{q^e}$ converge to $c$, and their generating function is
$$
 B(t)=\sum_{e\ge0}b_et^e=\ell(I-tM_0/q^d)^{-1}v(1)\in\mathbb C(t).
$$
In fact $B\in\mathbb Q(t)$. To see this, write $B=P/Q$ with complex polynomials and choose a rational linear basis $\beta_i$ for their finitely many coefficients. Write $P=\sum_i\beta_iP_i$, $Q=\sum_i\beta_iQ_i$ with rational polynomials. Since $B$ has rational coefficients, comparison of each coefficient in $QB=P$ gives $Q_iB=P_i$ for every $i$. Some $Q_i$ is nonzero, proving the claim. This step does not assume rational matrix entries.

Boundedness of $b_e$ gives convergence for $|t|<1$, and Abel's theorem yields $(1-t)B(t)\to c$ as $t\uparrow1$. A rational function over $\mathbb Q$ with a finite limit at the rational point $1$ has a rational limit: cancel any common powers of $t-1$ and evaluate. Thus $c\in\mathbb Q$.

**Corollary A.6.** None of $a_n,m_n,P(n)$ is $q$-regular over $\mathbb C$, for any integer $q\ge2$.

**Proof.** Set the zeroth terms to zero. The first application of Theorem A.5 takes $u_n=a_n$, $d=0$. For the second,
$$
 m_n/n^2=a_n-2\mathbf1_{2\mid n}a_{n/2}/n^2\longrightarrow L,
$$
so take $u_n=m_n$, $d=2$. All terms are rational, while $L$ is transcendental by Lemma A.1. Finally, any finite-dimensional constant-matrix digit representation has polynomial growth: a word of length $k=O(\log n)$ has matrix norm at most $R^k$ for a fixed $R\ge1$. But $P(n)\ge\mu_n=n!/2^{n-1}$ grows faster than any polynomial. This excludes $P(n)$ by a different argument.

These are consequences of finite-dimensional kernel representations and the known extremal asymptotic, not a classification of general digit algorithms. Changing finitely many initial terms does not affect regularity: the $q$-kernel of a finitely supported sequence spans a finite-dimensional space.

## Appendix B. The radial condition R and a sufficient criterion
Let $\nu_2(n)$ be the exponent of $2$ in a positive integer $n$, so that $\nu_2(12)=2$.

In what follows $G$ is analytic in the unit disc and $C\ne0$ is a fixed complex number.

**Assumption R.** There is an integer $r_0\ge1$ such that, for every fixed $r\ge r_0$ and every primitive $2^{r+1}$-th root of unity $\omega$, all derivatives of $x\mapsto G(\omega x)$ of order below $2r$ have finite limits as $x\uparrow1$ and
$$
\frac{d^{2r}}{dx^{2r}}G(\omega x)=C\,2^{r^2-1}\log(1-x)+O_{r,\omega}(1).
$$
This is an assumption about the actual derivatives; it cannot be replaced by differentiating the unknown $O$-remainder. Each time $r$ and $\omega$ are fixed first and the radial limit is taken afterwards; no uniform bound in the growth depth is required.

**Proposition B.1 (criterion via periodic asymptotics).** Let $G(z)=\sum_{n\ge1}b_nz^n$ with bounded $b_n$. The following two items are sufficient for Assumption R.

- For every fixed $s\ge0$ and every fixed $J$ there is a constant-coefficient expansion on the integers with $\nu_2(n)=s$,
$$
b_n=\sum_{j=0}^J\alpha_{s,j}n^{-j}+O_{s,J}(n^{-J-1}).
$$

- For every fixed $r\ge r_0$ there is a function $B_r$ analytic at the origin such that, uniformly for all sufficiently large $n$ with $2^r\mid n$,
$$
b_n=B_r(1/n)-\kappa_r\mathbf1_{\{2^{r+1}\mid n\}}n^{-2r-1}+O_r(n^{-2r-2}),\qquad \kappa_r=C\,2^{r(r+1)}.
$$

**Proof.** Fix $r$, put $q=2^{r+1}$ and $d=2r+1$. Use the first item on the finitely many valuation classes $s<r$ and the second on the remaining integers, obtaining
$$
b_n=\sum_{j=0}^{d}c_j(n)n^{-j}+O_r(n^{-d-1}),
$$
where each $c_j$ is $q$-periodic. For $j<d$ its period divides $2^r$; the top term can be written $c_d(n)=u(n)-\kappa_r\mathbf1_{\{q\mid n\}}$ with $u$ also $2^r$-periodic. Hence, with the convention
$$
\widehat c_j(\omega)=\frac1q\sum_{t=1}^{q}c_j(t)\omega^t,
$$
we have $\widehat c_j(\omega)=0$ for $j<d$ and $\widehat c_d(\omega)=-\kappa_r/q$.

A finite Fourier decomposition writes the explicit part as a finite linear combination of polylogarithms $\operatorname{Li}_j(z/\zeta)$; non-positive indices are interpreted through derivatives of the geometric series. Apart from $\zeta=\omega$ these functions continue analytically near $z=\omega$ in a way compatible with the branch on the disc. The only leading resonant term is $-(\kappa_r/q)\operatorname{Li}_{2r+1}(z/\omega)$.

The remainder coefficients are $O_r(n^{-2r-2})$, which is absolutely summable after $2r$ differentiations, so that derivative has a finite radial limit. On the other hand the $2r$-th derivative of $\operatorname{Li}_{2r+1}(x)$ is $-\log(1-x)+O(1)$, while all lower derivatives are finite; this follows directly from $\Theta^{2r}\operatorname{Li}_{2r+1}=\operatorname{Li}_1=-\log(1-x)$ and from the relation between the Euler operator and ordinary derivatives. Thus the leading coefficient is $\kappa_r/q=C2^{r^2-1}$, which is R. The finitely many initial terms only add a polynomial.

**Relation to the research notes.** The research notes [7], fixed at commit `c049e040`, provide a route for the actual sequence: the common-expansion and resonant-jump statements F/J in `round96core` have $\kappa_r=2^{r(r+1)}L$ for $r\ge4$, and `round98sources` derives the radial condition from those inputs. Thus accepting the stated structural and exact-recovery inputs gives R with $C=L$ and $r_0=4$. The analytic implication F/J $\Rightarrow$ R has been checked for this revision. Recent isolated results establish the actual recovery, tail and maximizer-entrance estimates used in the path-bound argument, now sharpened by Theorem 4. They do not establish the zero-diamond structural window, depth-induction conclusions, or the actual fixed-valuation F and common all-multiples J required by this route to R. The abstract analytic implication remains distinct from its application to the extremal sequence. The notes therefore contain a proof route, rather than no argument, but this manuscript does not present that entire route as an independently certified unconditional theorem. Its applications in Appendices C and D retain R explicitly; Appendix A does not depend on this chain.

## Appendix C. Ruling out contraction relations
A germ is D-finite if it satisfies a nonzero linear differential equation with polynomial coefficients. This appendix first establishes the natural boundary and then uses the exact divergence coefficients in R to study contractions.

**Theorem C.1.** If $G$ satisfies R, the unit circle is its natural boundary and $G$ is not D-finite.

**Proof.** R makes some fixed-order radial derivative diverge logarithmically at every primitive binary root of sufficiently high order, so $G$ cannot be continued analytically at such a point. These roots are dense on the unit circle, so no continuation across a nonempty arc is possible. Local branches of a D-finite function can have only finitely many planar singularities, located at zeros of the leading coefficient of its differential equation, so such a natural boundary is impossible.

The right-hand condition below is slightly stronger than analyticity on the disc: after clearing the common denominator of the rational coefficients, the chosen branch of the right-hand side continues analytically across every point of the unit circle except finitely many. D-finite right-hand sides satisfy it.

**Theorem C.2 (necessary leading terms for mixed contractions).** Let $\mathcal M$ be a finite set of distinct positive integers and consider a nontrivial relation
$$
\sum_{m\in\mathcal M}Q_m(z,\Theta)[G(z^m)]=F(z),
\qquad
Q_m(z,\Theta)=\sum_{j=0}^{d_m}p_{m,j}(z)\Theta^j,
$$
where $p_{m,j}\in\mathbb C(z)$, $p_{m,d_m}\ne0$, and $F$ satisfies the right-hand condition above. The coefficients sit to the left of the operator and $\Theta$ acts on the whole composite function. Write
$$
m=2^{s_m}t_m,\qquad t_m\in2\mathbb Z+1,\qquad w=\max_{m\in\mathcal M}(d_m+2s_m).
$$
For each odd $t$ let $I_t=\{m\in\mathcal M:d_m+2s_m=w, t_m=t\}$. If $G$ satisfies R then
$$
\sum_{m\in I_t}2^{-s_m^2}t^{-2s_m}p_{m,d_m}(z)=0
$$
is an identity of rational functions.

**Proof.** Clear denominators so that all coefficients are polynomials; the common denominator is multiplied on the left of the operator only and does not commute with $\Theta$. Fix $r$ large enough that $r-s_m\ge r_0$ and $K=2r-w\ge0$, and take a primitive $2^{r+1}$-th root $\omega$. Since $\omega^m$ has order $2^{r+1-s_m}$, the first derivative order at which $G(\omega^m y)$ diverges is $k_m=2(r-s_m)$.

Along $z=\omega x$ we have $\Theta=x\,d/dx$. Differentiating the relation $K$ more times radially, only the terms with $d_m+2s_m=w$ reach the actual derivative order $k_m$; all other terms involve lower derivatives and have finite limits. In the product rule, the Euler expansion and the chain rule the unique leading coefficient at the endpoint is $p_{m,d_m}(\omega)m^{k_m}$. Hence the coefficient of the first logarithmic divergence of that term is
$$
C\,2^{(r-s_m)^2-1}m^{2(r-s_m)}p_{m,d_m}(\omega)
=C\,2^{r^2-1}t_m^{2r}2^{-s_m^2}t_m^{-2s_m}p_{m,d_m}(\omega).
$$
All factors differ from their endpoint values by $O(1-x)$, which stays bounded against the logarithm. Away from the finite exceptional set, the corresponding derivative of the right-hand side has a finite limit; hence the sum of the leading logarithmic coefficients vanishes.

Thus for each fixed $r$ we obtain a polynomial identity in $\omega$ whose degree is controlled by the degrees of the original coefficients and does not depend on $r$. There are $2^r$ primitive $2^{r+1}$-th roots; for $r$ large enough, even after removing the finitely many exceptions, they outnumber that fixed degree, so the polynomial vanishes identically.

Grouping by odd part and writing $T_t(z)=\sum_{m\in I_t}2^{-s_m^2}t^{-2s_m}p_{m,d_m}(z)$, we have $\sum_t t^{2r}T_t(z)=0$ for all sufficiently large integers $r$. Choosing as many consecutive $r$ as there are distinct $t$, the coefficient matrix is a Vandermonde matrix in the distinct $t^2$ times a nonzero diagonal matrix, hence invertible. Therefore every $T_t=0$. The proof fixes $r$ one at a time, takes the limit, and then performs only finite algebraic elimination; it never exchanges the growth depth with the radial limit.

**Corollary C.3.** Under R there is no nontrivial finite relation $\sum_m p_m(z)G(z^m)=F(z)$ with rational coefficients whose right-hand side satisfies the condition of Theorem C.2.

**Proof.** Here all $d_m=0$, so the top-weight group shares the same maximal $s_m$. Distinct $m$ in it have distinct odd parts, so each nonempty $I_t$ is a singleton, contradicting a nonzero leading coefficient.

**Corollary C.4.** If the ratio of any two contraction parameters is not an integer power of two, the relation of Theorem C.2 is impossible even when derivatives of arbitrary finite order are allowed. In particular, for an integer $b\ge2$ that is not a power of two there is no linear differential--Mahler relation of finite order $\sum_jQ_j(z,\Theta)[G(z^{b^j})]=F(z)$.

**Proof.** Distinct contraction parameters have distinct odd parts, so every nonempty group of top weight is a single term. For $b=2^hu$ with odd $u>1$ the odd parts of $b^j$ are the distinct values $u^j$.

Similarly, in any admissible relation every nonempty odd-part group of top weight contains at least two terms, whose differential orders must differ by $2(s_2-s_1)$. If the spread of the top differential orders is at most $1$, no relation can hold. For a two-term relation $p(z,\Theta)G(z)-q(z,\Theta)[G(z^2)]=F$ the necessary condition is exactly $\deg_\Theta p=\deg_\Theta q+2$ and $q_{\mathrm{top}}=2p_{\mathrm{top}}$. This is only a necessary condition.

## Appendix D. Linear digit models and linear recurrences
A sequence is P-recursive if it eventually satisfies a nonzero linear recurrence of finite order with polynomial coefficients. For ordinary generating functions, D-finiteness is equivalent to P-recursiveness of the coefficients [3], up to finitely many initial terms.

For a sequence $(b_n)_{n\ge0}$ and a fixed integer base $q\ge2$, consider all subsequences $n\mapsto b_{q^en+t}$ with $e\ge0$ and $0\le t<q^e$. The sequence is called $q$-regular [4] if the complex span of these sequences is finite-dimensional.

**Theorem D.1.** If $G(z)=\sum_{n\ge0}b_nz^n$ satisfies R, then its coefficient sequence is not regular in any fixed integer base $q\ge2$; modifying finitely many terms does not change this.

**Proof.** Suppose the kernel space has dimension $D$. Choose basis vectors $v(n)$; extracting subsequences modulo $q$ preserves the space, so there are constant matrices $M_j$ with $v(qn+j)=M_jv(n)$ and $b_n=\ell v(n)$. The vector generating function $V$ satisfies
$$
V(z)=\left(\sum_{j=0}^{q-1}z^jM_j\right)V(z^q),\qquad G(z)=\ell V(z).
$$
This holds at the level of formal power series, including $n=0$; the matrices need not be invertible. Expanding $G(z),G(z^q),\ldots,G(z^{q^D})$ into the same vector $V(z^{q^D})$ produces $D+1$ row vectors in $\mathbb C(z)^D$. Linear dependence gives a nontrivial finite contraction relation without derivatives, contradicting Corollary C.3. Changing finitely many terms only changes the generating function by a polynomial, so the right-hand side stays rational and the contradiction persists.

A canonical digit representation may initialise the first nonzero digit to a fixed vector, which only adds a finite polynomial to the vector generating function; adjoining one constant direction allows the same elimination. The theorem therefore also excludes exact digit models with fixed dimension, constant matrix updates and a fixed linear readout, but not models whose state dimension varies with the input, nonlinear updates or general algorithms.

**Conditional Corollary D.2.** If the actual $A$ satisfies R with $C=L$, then the natural boundary of $A$ is the unit circle, the natural boundary of $E$ is the circle of radius $2$, and $P(n)$ is not P-recursive. All contraction restrictions of Appendix C and Theorem D.1 then apply to $a_n$.

Here $P(n)$ is not P-recursive because $A$ is not D-finite; the factor $P(n)=n!2^{1-n}a_n$ is hypergeometric, so substituting it into a finite-order recurrence and clearing denominators shows that P-recursiveness is equivalent for the two sequences. The digit-representation exclusions for $a_n,m_n,P(n)$ already follow without R from Corollary A.6. Theorem D.1 retains a separate analytic exclusion for general functions satisfying R.

If the actual remainder $m_n$ can be determined independently, unfolding the half-scale relation level by level gives
$$
a_n=\sum_{j=0}^{\nu_2(n)}\frac{2^{j(j+2)}}{n^{2j+2}}m_{n/2^j}.
$$
At present this is only a reconstruction identity: $m_n$ is defined as the difference of the unknown $a_n$ and substituted back, which yields no independent closed form.

## Appendix E. A short formula with a natural boundary
The example of the main text corresponds to $C=1$ below; an arbitrary fixed nonzero complex $C$ is allowed.

For fixed $C\ne0$ define
$$
s_n=-C\sum_{j=0}^{\nu_2(n)-1}2^{j(j+1)}n^{-2j-1},\qquad S(z)=\sum_{n\ge1}s_nz^n.
$$
The sum is empty at odd $n$. Separating the leading term at even $n$ gives $s_n=-C/n+2s_{n/2}/n^2$, hence exactly
$$
\Theta^2S(z)-2S(z^2)=-\frac{2Cz^2}{(1-z^2)^2}.
$$
On the other hand fix $r$ and split the definition into $j<r$, $j=r$ and $j>r$. Consecutive surviving terms in the tail differ by a factor of at most $1/4$, so the tail coefficients are $O_r(n^{-2r-3})$. Put $q=2^{r+1}$. At a primitive $q$-th root the lower layers produce only non-resonant polylogarithms, the leading resonant term being $-\kappa_r\operatorname{Li}_{2r+1}(z^q)/q^{2r+1}$ with $\kappa_r=C2^{r(r+1)}$. Differentiating $2r$ times along $z=\omega x$ gives a leading chain factor $q^{2r}$, so the coefficient of the logarithm is $\kappa_r/q=C2^{r^2-1}$; the lower chain terms are finite and the tail is absolutely summable at that order. This yields condition R, so $S$ has a natural boundary.

At the same time $-s_n/C$ is a rational sum of at most $\nu_2(n)$ terms. For odd $n$ the output is zero; for $\nu_2(n)\ge1$ the common denominator may be taken as $n^{2\nu_2(n)-1}$, and numerator and denominator have bit length $O((\log n)^2)$, so the value can be computed exactly in polynomial time in the input length. What is computed exactly is the rational number $-s_n/C$, or one may simply take $C=1$. This example has both a natural boundary and a short differential--binary recurrence. Its coefficients tend to zero and it is not the actual $a_n$; its rational right-hand side cannot be transplanted to the actual remainder handled by Theorem A.4.

The main text also mentions the generating function of $1/n$. Term-by-term integration of the geometric series gives $\sum_{n\ge1}z^n/n=-\log(1-z)$. Continuing once around $z=1$ changes the value of the logarithm by $2\pi i$, and repeated circuits produce infinitely many branches; an algebraic function has only finitely many branches, so this generating function is not algebraic.

## Research status and licence
This is a research draft, not an externally peer-reviewed result. AI tools assisted with derivation organisation, translation, typesetting and consistency checks; the author remains responsible for the final content.

A separate, isolated integration snapshot passed fresh compilation of all 557 modules and type/axiom auditing of all 7,907 declarations on 10 November 2026 at 08:20:17 UTC. It contains the 413 unchanged baseline modules and 144 new modules. Each project module was compiled by direct Lean invocation in topological order into an isolated object directory, followed by an imported-kernel inventory equality check and full declaration type/axiom auditing; this was not a new Lake build. No historical project objects were reused; interrupted checkpoints from this same fresh run were hash-verified before resumption. The independent audit found no nonstandard axioms or provenance/coverage errors. That certificate refers to the exact snapshot at that time. Subsequently, 30 comment-corrected modules were recompiled and the 557-module tree was audited again before publication at commit `88ef91e`. Commit `17821c9` subsequently rebuilt only the two PDFs; its Markdown and TeX sources are unchanged. These historical checks are distinct from the six-module sharp extension and its combined-tree audit below. The copied `lean/verification` directory remains the historical 413-module record; the fresh integration has a separate verification record.

In addition to the non-algebraicity conclusions of Appendix A.4, they formalise the non-$q$-regularity of the actual sequences $a_n$ and $m_n$ for every integer $q\ge2$, using the finite-dimensional complex span of the $q$-kernel as the definition. For $P(n)$ they formalise the growth obstruction and exclude fixed finite-alphabet continuous-linear digit transitions with a fixed linear output, including finite-dimensional complex matrix models. The equivalence between this representation and the $q$-kernel definition is not formalised in that application.

Version 0.4.0 formalised the full-sequence rational-limit statement: for a rational-valued $q$-regular sequence, convergence of $u(n)/n^d$, with $d$ a nonnegative integer, forces the limit to be rational. Its modules `RationalRadial`, `RationalLinearDescent`, `RationalSeriesLimit` and `QRegularRationalLimit` provide that proof. This endpoint had a stronger convergence premise than Theorem A.5, which assumes only convergence of $q^{-de}u(q^e)$. Version 0.4.1 adds `QRegularGeometricLimit`; its theorem `NonAlgebraicity.qRegular_geometric_limit_rational` matches this geometric-subsequence statement exactly, using the same complex-span definition of $q$-regularity, with no full-sequence convergence or Lindemann--Weierstrass premise. The existing full-sequence result and the non-$q$-regularity applications remain valid. This corrects the earlier description of formal coverage, not the mathematical statement or proof of Theorem A.5. The new encoding bridge proves `ExtremalAsymptotic`. Its direct wrappers for $A$ and $a_n$, and direct instantiation of the existing theorems for $E$, $M$ and $m_n$, retain only `FourExponentialIndependence`, the required Lindemann--Weierstrass input. The raw-count theorem excluding every exponential upper bound has no external asymptotic or transcendence premise. The abstract implication from F and common all-multiples J to radial asymptotics is formalised. Its hypotheses have not been established for the actual extremal sequence; full Condition R and the complete downstream arguments of Appendices C--E are not certified here. The historical and fresh integration verification records must be distinguished as above; source files alone do not certify a successful verification run.

\paragraph{Sharp endpoints and their provenance.} Theorem 4 strengthens the two-constant result of the historical 557-module snapshot. Six new modules, containing 63 kernel declarations, were independently freshly compiled over hash-verified 557-module objects and fully audited. This was not a fresh rebuild of all 563 modules. The version 0.4.0 combined integration passed on 10 November 2026 at 10:23 UTC: the six new modules and updated EndpointCheck were freshly compiled, with 556 unchanged, hash-verified upstream objects reused. All 563 modules and 7,970 kernel declarations underwent complete type/axiom auditing. Global kernel names, raw expression types, universes, declaration kinds and axioms agree exactly with the 7,907 old and 63 independently checked new declarations. Ten generated declarations changed only module attribution, and 46 pretty-printed displays differed without any underlying type change. Both exact-instantiation drivers for $E,M,m_n$ passed, retaining the explicit Lindemann--Weierstrass input. The final check validated 2,302 evidence-file hashes. This was not a full 563-source rebuild or a new Lake build. The sharp bounds and actual sequence interface require no external graph-asymptotic input. Structural classification and actual F/J/R remain unproved.

\paragraph{Version 0.4.1 geometric-subsequence correction.} On 10 November 2026 at 12:13 UTC, the combined 564-module audit completed successfully for all 7,979 declarations. The new `QRegularGeometricLimit` module and updated `EndpointCheck` were freshly compiled; 562 unchanged, hash-verified project objects were reused. This was not a full fresh rebuild of 564 sources or a new Lake build. A full-kernel scan of 823,773 constants confirmed the complete project inventory. Names, raw expression types, universes, declaration kinds and axioms matched the previous 7,970 declarations plus the nine new declarations exactly, with no module-attribution or pretty-print differences. The A.5 examples and full-sequence corollary, and both exact-instantiation checks for $E,M,m_n$, passed in the same audited environment; the latter retain the explicit Lindemann--Weierstrass input. The geometric-subsequence endpoint itself has no such premise. The final source, object and dependency recheck completed at 12:14 UTC; all 79,506 dependency hashes were unchanged. The published Zenodo record <https://zenodo.org/records/24104925> remains the historical version 0.4.0 record, not a publication of this patch.

A separate group of checked upstream lemmas covers finite ordered cancellation, shortest color-word swaps and zero-diamond tournament repair, vector weak majorization for actual tournament matrices, and Frobenius-norm comparisons for all nonnegative integer powers. The all-ones source-energy series and the actual resolvent identity are proved for $q\ge0$ with $q(n-1)^2<1$, including $q=1/n^2$ for $n>0$, with convergence and two-sided invertibility established internally. The exact even-subset convolution S1 and zero-diamond two-permanent average use this repository's actual Hamiltonian path count. Ordered strongly connected component reconstruction also gives, for $n\ge4$, $D>0$ and $24D\le n^2$, the finite small-defect bound $6n^2D\le\lVert T_n^3\rVert_F^2-\lVert S^3\rVert_F^2$. Here $S$ is the original skew sign matrix, $T_n$ is transitive, and $D$ counts unordered four-vertex diamonds.

For actual zero-diamond tournaments, the formalisation now reaches fixed complex disks. The finite kernel identity is
$$
\det(I+aS)=\frac{(1+a)^n+(1-a)^n}{2}.
$$
Its imaginary-parameter normalisation converges uniformly to $\cos w$ on compact sets; for $|w|\le R$, the error is at most $2e^R R^2/n$ once $n>0$, $R/n\le1/2$ and $R^2/n\le1$. For each fixed $0\le R<\pi/2$, one further order threshold, independent of the graph and $w$, gives genuine two-sided inverses and
$$
\left\|(I+(w/n)^2S^2)^{-1}\right\|_{2\to2}\le C_R^2,
\qquad C_R=\frac{2(1+R)e^R}{\cos R}.
$$
This bound follows from an explicit inverse-entry formula and a Euclidean operator-norm estimate, not from the determinant lower bound alone. For the actual real score vector $b=S\mathbf1$, the additional energy assumption $\lVert b\rVert_2^2\le Kn$ yields
$$
\frac{\left|b^{\mathsf T}(I+(w/n)^2S^2)^{-1}b\right|}{n^2}
\le\frac{KC_R^2}{n}.
$$
The score-energy identity and the passage from the Hermitian inner product to this ordinary bilinear source are formalised. Zero-diamond status alone does not imply the energy assumption. Theorem 4 supplies the energy bound eventually for actual maximizers, but does not supply the zero-diamond hypothesis needed to apply these analytic results to them.

For the branch-defined Gaussian/source factor, put
$$
 \beta_n(z)=1-z^2/n^2,\quad k_n(z)=z\exp[-\tfrac12\log\beta_n(z)],\qquad
 G_n(z)=\frac{\exp[-\tfrac n2\log\beta_n(z)]}{H_n(k_n(z))},
$$
where the logarithm fixes the branch at zero and
$H_n(w)=((1+iw/n)^n+(1-iw/n)^n)/2$. With the actual score source
$\Psi_S(w)=b^{\mathsf T}(I+(w/n)^2S^2)^{-1}b$, define
$$
 \Lambda_{v,S}(z)=\frac{vz}{1+vz/n}
 -\frac{k_n(z)^2\Psi_S(k_n(z))}{n^2(1+vz/n)},\qquad
 P_{v,S}(z)=G_n(z)e^{\Lambda_{v,S}(z)}.
$$
The checked finite determinant identity gives
$G_n(z)^2\det(\beta_n(z)I+(z/n)^2S^2)=1$, with $G_n(0)=1$, on the stated nonvanishing domain. The parameter branch, actual source, and assembled product are analytic on a common disk for sufficiently large orders. For fixed $0\le r<R<\pi/2$, $K\ge0$, and each fixed derivative order $j$, the formalisation supplies an explicit constant $C_{j,r,R,K}$ such that
$$
 \sup_{|z|\le r}\left|\frac{d^j}{dz^j}
 \left(P_{v,S}(z)-\frac{e^{vz}}{\cos z}\right)\right|
 \le \frac{C_{j,r,R,K}}n.
$$
This holds eventually in $n$, uniformly over actual zero-diamond tournaments satisfying $\|S\mathbf1\|_2^2\le Kn$ and complex $|v|\le1$. Derivative estimates follow from a larger-disk value bound and Cauchy's estimate, not from formal differentiation of a pointwise error term.

For the original two branches $v^2=1$, the finite block bridge is also proved. Set $M_v=(S+vI)/n$, $Q_v=\left(\begin{smallmatrix}0&M_v\\M_v^{\mathsf T}&0\end{smallmatrix}\right)$, and $B_v=I+zQ_v$. Under the stated nonvanishing and invertibility conditions, $B_v$ has a genuine two-sided inverse, and the original $2n$-dimensional source satisfies
$$
 \tfrac12\mathbf1^{\mathsf T}(B_v-I)B_v^{-1}\mathbf1=\Lambda_{v,S}(z),
 \qquad G_n(z)^2\det B_v=1.
$$
The source on the left is defined independently from the block matrix; its equality to the reduced expression follows by solving the block equations and using skew-symmetry. The extension to complex $|v|\le1$ above concerns the branch-defined factor only: these block identities require $v^2=1$.

The first finite pairing bridge is also formalised: for the block covariance with cross-colour entries $M_{ij}$ and zero same-colour entries, the sum of weights over all perfect pairings of two labelled $n$-element sets equals $\operatorname{per}M$. Each unoriented edge has exactly one representative in the weight product. Pairings with a same-colour edge vanish; the surviving bipartite pairings are related to permutations by a proved bijection, not merely assigned the permanent as their definition. The empty case $n=0$ is included, with pairing sum and permanent both equal to one. This is a finite algebraic identity over a commutative semiring, not a Gaussian-measure expectation theorem.

The finite pairing identity also applies after restricting the original matrix to actual left and right vertex subsets $I,J$. The pairing sum vanishes when $|I|\ne|J|$; when $|I|=|J|=k$, it equals the permanent of the selected $k$ by $k$ submatrix under the explicit finite enumerations. The covariance is restricted before summing pairings. Thus the subset statement concerns the original matrix entries, not an unrelated square matrix introduced as a new assumption.

The global squarefree step is now proved as well. A linear coefficient-contraction map on multivariate polynomials is explicitly defined using the actual subset pairing weights. Expanding $\prod_{x\in[n]\sqcup[n]}(1+X_x)$ and applying this map with cross-covariance $zM$ gives the frozen polynomial
$$
 F_M(z)=\sum_{k=0}^{n}F_k(M)z^k,\qquad
 F_k(M)=\sum_{|I|=|J|=k}\operatorname{per}M[I,J].
$$
The scaling and regrouping by subset size are proved, with $F_0(M)=1$ and degree at most $n$. This contraction agrees with the proved finite pairing weights on squarefree monomials, but its definition ignores nonsquarefree monomials. It is not yet a Wick functional for repeated indices, and cannot be applied to an exponential or logarithmic series as though that extension had been established.

A separate full polynomial Wick functional now retains repeated labels. For a monomial with exponent vector $d$, its pairing positions are the distinct occurrences $(i,a)$ with $0\le a<d_i$, not merely the support of $d$. The monomial value is the sum over all perfect pairings of these positions, and linear extension defines a functional on multivariate polynomials. For symmetric covariance its value is unchanged by any enumeration of the occurrences, including permutations mixing the two colours. Separately, the complete fourth-order occurrence-pairing formula is proved, including
$$
 m_C(x,x,y,y)=C_{xx}C_{yy}+2C_{xy}^2,
$$
with no zero-diagonal assumption; the diagonal contribution is not discarded.

The full polynomial Wick functional now agrees with the earlier contraction on squarefree basis monomials. The bridge uses an explicit label-preserving equivalence between occurrence positions and the selected vertex subsets. Consequently the full functional, applied to the actual product $\prod_x(1+X_x)$ with scaled block covariance, gives the frozen polynomial $F_M(z)$. This is compatibility on the squarefree subspace, not equality of the two maps on arbitrary polynomials with repeated variables.

For arbitrary finite occurrence sets and symmetric covariance, an all-orders pairing recurrence is proved:
$$
 m_C(V)=\sum_{s\in V\setminus\{o\}} C(o,s)\,
 m_{C|_{V\setminus\{o,s\}}}(V\setminus\{o,s\}).
$$
The proof constructs a genuine bijection between pairings and the choice of the distinguished point's partner together with a residual pairing, and derives the edge-weight factorization. Odd-cardinality moments vanish; the empty moment equals one. These are finite algebraic results.

For constant covariance $c$, the recurrence gives the actual pairing moments $m_c(2k)=(2k-1)!!c^k$ and $m_c(2k+1)=0$, with the empty moment one. The pairing count and its factorial normalization are proved, rather than supplied as hypotheses. An explicit occurrence equivalence identifies these moments with the full one-variable polynomial Wick functional $\mathcal W_c(X^m)$. Over a commutative $\mathbb Q$-algebra this yields the formal power-series identity
$$
 \sum_{m\ge0}\frac{\mathcal W_c(X^m)}{m!}t^m
 =\exp(ct^2/2).
$$
Here the right side is the formal exponential with rescaling and degree doubling; no analytic convergence or probability measure is asserted.

The scalar identity extends to every finite linear source $\ell_h(X)=\sum_i h_iX_i$ and symmetric covariance $C$. Expansion into labelled occurrences, a genuine pairing-endpoint bijection, and the factorization of each fixed pairing prove
$$
 \mathcal W_C(\ell_h^m)=m_{h^{\mathsf T}Ch}(m),\qquad
 \sum_{m\ge0}\frac{\mathcal W_C(\ell_h^m)}{m!}t^m
 =\exp\!\left(\tfrac12 h^{\mathsf T}Ch\,t^2\right).
$$
The second identity is a formal power-series identity over a commutative $\mathbb Q$-algebra, derived from the actual repeated-index polynomial functional. It requires symmetry, not positive definiteness or a Gaussian probability measure.

The full pairing functional also satisfies the algebraic integration-by-parts identity
$$
 \mathcal W_C(X_iP)=\sum_j C_{ij}\mathcal W_C(\partial_jP)
$$
for every polynomial $P$, finite label set and symmetric covariance over a commutative semiring. Deleting actual paired occurrence positions gives each monomial multiplicity; polynomial induction completes the proof. Repeated labels are retained. This is an algebraic identity, not a probability integral.

For symmetric matrices $K,A$ over a field of characteristic zero, the mixed formal series
$$
 E(u,X)=\exp(u h^{\mathsf T}X)\exp(-u^2X^{\mathsf T}AX/2)
$$
is defined by finite coefficient sums. Applying the actual Wick functional coefficientwise defines $Z_W=\mathcal W_K(E)$, $G_i=\mathcal W_K(X_iE)$ and $H_{ij}=\mathcal W_K(X_iX_jE)$. Polynomial-variable differentiation and algebraic integration by parts give the two Ward systems
$$
 B G=u(Kh)Z_W,\qquad B H=KZ_W+u(Kh)G^{\mathsf T},\qquad B=I+u^2KA.
$$
The formal matrix $B$ is proved to be a unit with a genuine two-sided inverse. Set $r=B^{-1}Kh$ and $D=B^{-1}K$. Solving these actual Ward systems, without dividing by $Z_W$, gives
$$
 G=urZ_W,\qquad H=(D+u^2rr^{\mathsf T})Z_W.
$$
The parameter derivative is also proved coefficientwise, together with $Z_W(0)=1$:
$$
 Z_W'=q(u)Z_W,\qquad
 q(u)=u h^{\mathsf T}r-u\sum_{i,j}A_{ij}(D_{ij}+u^2r_ir_j).
$$
The initial value follows from the actual empty pairing moment. Full Jacobi differentiation, the inverse derivative and uniqueness for the formal scalar ODE now yield the general mixed-source identity
$$
 \begin{aligned}
 Z_W(u)&=\Delta(u)\exp(\Phi(u)),&
 \Phi(u)&=\frac{u^2}{2}h^{\mathsf T}B(u)^{-1}Kh,\\
 \Delta(u)^2\det B(u)&=1,& \Delta(0)&=1.
 \end{aligned}
$$
This holds for every finite label set, symmetric $K,A$ over a characteristic-zero field with its rational algebra structure, and arbitrary $h$. The covariance $K$ need not be invertible. The determinant branch is constructed from the universal binomial series of exponent $-1/2$ by substituting $\det B-1$; the formal exponential is substituted at $\Phi$. Both substituted series have proved zero constant term. The proof derives full Jacobi differentiation from the permutation determinant, proves $B^{-1}K$ symmetric without assuming $B$ symmetric, and checks that the candidate and the actual Wick series satisfy the same ODE and initial value. Thus this is an identity for the original finite Wick coefficients, including repeated indices, not an assumed Gaussian formula. The earlier rank-one quadratic branch is also proved separately.

The change of grading $z=u^2$ is now proved for the actual Wick series: the descended coefficient of $z^n$ is its original coefficient of $u^{2n}$, every odd coefficient vanishes, and expansion by two reconstructs the original series. This is coefficient extraction, not evaluation at $u=1$. The matrix $B_z=I+zKA$, its true inverse, the determinant branch and the source exponential are transported through the expansion homomorphism.

Specializing $A=I$ and $h=\mathbf1$ identifies the source with the actual matrix expression
$$
 \frac12\mathbf1^{\mathsf T}(B_z-I)B_z^{-1}\mathbf1.
$$
The resulting formal determinant–exponential identity is also specialized to the original doubled tournament covariance $Q_v$, whose symmetry is proved, for every finite order and every complex $v$. This does not extend the separate block reduction that requires $v^2=1$.

A local analytic bridge is now available for the determinant factor. Actual Taylor coefficients, defined by iterated derivatives divided by factorials, are proved compatible with finite arithmetic, determinants and the genuine matrix inverse. For every finite complex matrix $Q$, the Taylor series of $I+zQ$, its determinant and its inverse are identified with their formal counterparts near zero. No symmetry or positivity of $Q$ is needed for this matrix result. Uniqueness of normalized inverse-square-root branches then identifies the Taylor series of the existing analytic Gaussian factor with the canonical formal determinant branch for diamond-free tournaments and $v^2=1$. Its analyticity, value one at zero and local square identity are proved, not supplied as additional hypotheses.

The raw source and exponential Taylor identities are now proved as well. For every finite complex matrix $Q$, the actual inverse-quadratic source is analytic near zero, vanishes there, and has the formal raw-source coefficients. Taylor differentiation, the analytic chain rule and formal ODE uniqueness identify its exponential without an interchange of infinite sums. Combining these results with the normalized determinant branch gives a genuinely convergent local expansion whose coefficients are the previously defined descended full-Wick coefficients. For $n>0$, a diamond-free tournament and $v^2=1$, the raw source is identified with the original block expression and the finite source elimination identifies this expansion with the existing product $P=G\exp\Lambda$. Thus the original product, not merely a newly defined candidate, has the actual Wick coefficient series near zero. The normalization already contained in $Q_v$ is unchanged.

Convergence now extends to every closed inner disk with a common size threshold. For fixed $0\le r<R<\pi/2$, one threshold in $n$ works for every diamond-free tournament, every $v^2=1$ and every $|z|\le r$: the actual Wick series sums to the original product. No score-energy hypothesis is needed for this result. The conclusion is a proved sum at each point under these uniform quantifiers, not an asserted uniform convergence rate.

Writing $c_k$ for the actual Wick coefficients, their estimates now have a proved graph-uniform bound. For $0\le\rho<s<R<\pi/2$ and $K_0\ge0$, assume score energy at most $K_0n$. An explicit $M=\exp(s)/\cos R+C(s,R,K_0)$, where $C$ is the proved product-error constant, gives, after a common threshold for all such diamond-free tournaments and $v^2=1$,
$$
 |c_k|\le M/s^k,\qquad \sum_{k\ge0}|c_k|\rho^k\le\frac{M}{1-\rho/s},
$$
$$
 \left|P(T,v,z)-\sum_{k<m}c_kz^k\right|
 \le\frac{M(\rho/s)^m}{1-\rho/s}\quad(m\ge0, |z|\le\rho).
$$
The sphere bound is derived from the actual product estimate, not assumed. The last inequality is the analytic Wick-core Taylor remainder; it is not the true tail estimate for the finite matching polynomial or permanent.

For every polynomial insertion $F$, the inserted Ward system and its solution by the true inverse are also proved. With $V=B^{-1}K$ and $r=Vh$, the normalized tilted functional satisfies
$$
 \widetilde{\mathcal W}(X_iF)
 =\sum_jV_{ij}\widetilde{\mathcal W}(\partial_jF)
   +u r_i\widetilde{\mathcal W}(F),\qquad
 \widetilde{\mathcal W}(1)=1.
$$
Normalization uses the proved unit $Z_W$, and repeated indices are retained. Physical scaling and even descent are now proved for actual polynomial insertions. For a label word $w$, the physical moment is defined as $u^{|w|}\widetilde{\mathcal W}(\prod_{i\in w}X_i)$, with one factor per occurrence. Its first-occurrence deletion recurrence follows from the polynomial Ward identity. An independently defined terminating $z$-recurrence, with
$$
 W=z(I+zKA)^{-1}K,\qquad \eta=Wh,
$$
reconstructs that actual moment under $z=u^2$. For $A=I$, true two-sided inverse identities also give $W=zK(I+zK)^{-1}$. Both $W$ and $\eta$ have zero constant term. The empty moment is one; all odd $u$ coefficients vanish, and the descended coefficient of degree $k$ vanishes when $2k<|w|$. Invariance under word permutations is transported from the actual commutative polynomial product, not assumed of the recurrence. Repeated labels and empty words are included. These are finite formal identities; they introduce no graph-energy or size hypotheses.

The residual factorization is now proved at the $u$-graded polynomial-series level. Independently define
$$
 r_i=(1+uX_i)\exp(-uX_i+u^2X_i^2/2),\qquad R=\prod_i r_i.
$$
Formal exponential addition and inversion in the polynomial algebra give $ER=\prod_i(1+uX_i)$ for the existing core with $A=I$, $h=\mathbf1$. Direct coefficient calculations give $[u^0]r_i=1$ and $[u]r_i=[u^2]r_i=0$. The residual is not defined by dividing the desired answer by the core.

For $R=\sum_aR_au^a$, define the normalized insertion convolution by
$$
 [u^n]\mathcal T(R)=\sum_{a+b=n}[u^b]\widetilde{\mathcal W}(R_a).
$$
Actual Wick linearity and the proved unit normalization then give
$$
 \mathcal W\!\left(\prod_i(1+uX_i)\right)=Z_W\mathcal T(R).
$$
Every coefficient sum is finite. This uses neither multiplicativity of Wick nor analytic summation, and keeps repeated labels and self-pairings.

The finite frozen polynomial is now connected to this actual residual. Grouping the true subset pairing weights proves that Wick of the shifted product is the degree-doubling expansion of the canonical power-series image of the existing frozen polynomial. Unequal subset sizes contribute zero by the pairing theorem. Let $T_U$ denote the actual insertion convolution above and define $T_Z$ by $[z^k]T_Z=[u^{2k}]T_U$. Unit cancellation using the actual core's constant term one proves that the odd coefficients of $T_U$ vanish and that expansion by two reconstructs $T_U$. Consequently, for the original bipartite covariance built from $M$,
$$
 \operatorname{frozenPolynomial}(M)=\operatorname{core}(M)\,T_Z(M)
$$
as formal power series. Here the core is the actual descended Wick series; the residual is defined by finite insertion coefficients and even extraction, not by dividing the desired polynomial by the core. Its explicit finite antidiagonal coefficient formula and the core's determinant–source formula are proved. The empty case and constant coefficient are retained, with no graph-energy or asymptotic hypothesis.

The residual coefficients now have a locally finite physical-moment description. The actual local coefficient of degree $m$ is proved to be $\gamma_mX_i^m$. Expanding the finite residual product over degree assignments constructs a word with one position per occurrence, and connects each actual residual coefficient to the previously proved $W,\eta$ moments. At degree $z^k$ only assignments with total degree $m\le2k$ contribute; higher-degree contributions vanish. This is a proved coefficient identity, not an assumed activity expansion or evaluation at $u=1$.

Direct scalar calculations give $\gamma_0=1$, $\gamma_1=\gamma_2=0$, $\gamma_3=1/3$ and $\gamma_4=-1/4$. Every active numerical coordinate in a nonzero assignment therefore has degree at least three, so their number is at most $m/3$. Numerical coordinates are not structural vertices: several later logarithmic vertices may share a label. The actual same-label moments of orders one through four are also proved, including
$$
 M_3(i)=\eta_i^3+3\eta_iW_{ii},\qquad
 M_4(i)=\eta_i^4+6\eta_i^2W_{ii}+3W_{ii}^2.
$$
Self-pairings are retained. The actual scalar residual is now proved to equal $\exp L$, where $L$ is independently specified by zero coefficients in degrees zero through two and coefficient $(-1)^k/(k+3)$ in degree $k+3$. The identity follows from the actual residual's differential equation and formal uniqueness. Since $L=u^3H$, its exponential coefficient of degree $n$ is a finite sum over $b\le\lfloor n/3\rfloor$, with weight $1/b!$ and genuine ordered vertex-degree assignments. This is a scalar, local structural-vertex expansion, not the global labelled $C_j$ formula.

For the actual bipartite residual, the first three coefficients are now proved to be $1,0,0$. The proof uses the true physical covariance coefficient $[z]W_{ij}=K_{ij}$ and the fact that a nonzero assignment of total degree below six has only one active coordinate. The bipartite covariance has zero diagonal; the resulting low-order cancellation is derived, not imposed by discarding self-pairings. Consequently, for every matrix $M$, the existing frozen polynomial and actual Wick core agree exactly in degrees zero, one and two. This is not a higher-order error bound, and the activity index $j$ is not the power of $z$.

The actual physical moments now have a genuine partial-matching representation. On the occurrence positions, choose a paired subset with a fixed-point-free involution; multiply the existing unordered edge weights on this subset and the means on its complement. Finite subset expansion identifies this sum with full Wick applied to the affine product, and the proved recurrence identifies it with the previously defined physical moment. A separate bijection identifies these objects with involutions allowing fixed points. Repeated numerical labels, internal pairs and empty sets are retained. Substitution into the actual residual coefficient formula gives a finite sum of these partial-matching weights, rather than a newly defined surrogate.

For $b$ structural vertices of degrees at least three, let $D$ be the number of occurrence positions, $e$ half the cardinality of the paired subset, and $h$ the number of unpaired positions. The actual pairing gives $D=2e+h$. With $j=e+h-b$, the proved counting bounds are $b\le2j$, $D\le6j$ and $e+h=j+b$. The existing unordered edge set is now proved to have cardinality $e$. Since each actual covariance and mean has zero constant coefficient, the physical partial-matching weight is divisible by $z^{e+h}$; its coefficients below degree $j+b$ vanish. Repeated numerical labels and internal pairs are retained. This is a formal order bound, not a norm estimate, and $j$ is not the power of $z$.

The actual polynomial-valued residual product is also proved to equal the formal exponential of the sum of its local logarithms. At degree $m$, its coefficient has a finite expansion over $b\le\lfloor m/3\rfloor$, with the exact factor $1/b!$, ordered vertex-label maps and degree assignments summing to $m$. Repeated labels are allowed, and any term with a structural degree below three vanishes. This is an identity for the previously defined residual, not a replacement definition.

The global finite structural regrouping is now proved for the actual residual coefficients. The actual additive tilted functional is applied to the ordered-vertex expansion, without assuming that Wick or tilted insertion is multiplicative. A genuine word-to-occurrence-position identity transports each term to the physical partial-matching sum. The resulting coefficient $[z^k]T_Z$ is a finite sum over total degree $m\le2k$, vertex count $b\le\lfloor m/3\rfloor$, arbitrary vertex labels, degree assignments and actual partial matchings, retaining the factor $1/b!$ and the logarithm coefficients. The finite sum over $j$ can then be put outermost. Terms outside $b\le2j$, $m\le6j$ or $j+b\le k$ vanish by the proved coefficient-order and counting results, rather than by an imposed truncation. Empty structures, repeated labels, same-vertex pairs and singleton positions remain included; $j$ is not the coefficient degree $k$.

Quantitative ingredients are now available, with their hypotheses kept separate. The weighted sum of absolute coefficients is proved submultiplicative for summable series, including finite products; an actual local power-series expansion and a larger-circle bound give the corresponding weighted coefficient bound at a smaller radius. Applied to the existing partial-matching weights, bounds $B$ for each covariance and $E$ for each mean give $B^eE^h$. Summing over all vertex-label maps contributes $|I|^b$, retaining repeated labels and loops. Summability and the entrywise coefficient bounds are explicit hypotheses, not consequences of a formal identity alone.

For a complex matrix $Q$ of dimension $2n$, $n>0$, suppose $|Q_{ij}|\le C/n$, $|(Q\mathbf1)_i|\le K_0/n$, $|z|\le s$, and a genuine inverse $R(1+zQ)=I$ has Euclidean operator norm at most $L$. Complex bilinear row--inverse--column estimates then give, for $W=(zQ)R$ and $\eta=W\mathbf1$,
$$
 |W_{ij}|\le\frac{sC+2s^2C^2L}{n},\qquad
 |\eta_i|\le\frac{sK_0+2s^2CLK_0}{n}.
$$
For the raw matrix hypotheses, the inverse, analyticity and coefficient bridges are now derived rather than assumed. If $\|Q\|_{\mathrm{op}}\le q$ and $sq<1$, the convergent Neumann series proves that $I+zQ$ is invertible on $|z|\le s$, with inverse norm at most $1/(1-sq)$. The actual coordinates of $zQ(I+zQ)^{-1}$ and its all-ones mean are analytic there, and their Taylor series are proved equal to the previously defined formal physical covariance and mean. With the entry and coordinatewise score assumptions above, Cauchy estimates give summability and explicit weighted coefficient bounds at $0\le\rho<s$. Applying these derived bounds to the existing partial-matching weights closes the conditional raw label-sum estimate, including repeated labels and loops. A score-energy bound still cannot replace the coordinatewise bound on $Q\mathbf1$.

The raw spectral hypothesis is now discharged for real skew matrices: if $S$ is real skew with $|S_{ij}|\le1$, $v$ is real with $|v|\le1$, and $n\ge24$, then $M=(S+vI)/n$ and its actual bipartite block $Q$ satisfy $\|Q\|_{\mathrm{op}}\le3/4$ and $|Q_{ij}|\le1/n$. The proof uses a real skew Lagrange identity, complexification and a genuine block-norm estimate, not an assumed singular-value pairing. With the remaining coordinatewise score bound $|(Q\mathbf1)_i|\le K_0/n$, the existing physical covariance and mean have summable weighted coefficients at radius $9/8$, bounded respectively by $1025/(2n)$ and $1025K_0/(2n)$. The outer circle is $5/4$; no separate spectral, inverse or analyticity assumption remains in this theorem.

For an explicitly defined finite bit-word family, the score assumption is also discharged. At every positive depth $d$, balanced signs on $2^d$ bit words and the signed-transitive local matrix under a chosen enumeration give actual normalized row and column bounds. Transport through a genuine graph relabeling yields, for the existing physical series,
$$
 \|W_{ij}\|_{9/8}\le\frac{1025}{2n},\qquad
 \|\eta_i\|_{9/8}\le\frac{1025(2^d+1)}{2n},
$$
These are summable weighted coefficient norms. The theorem assumes positive depth, the chosen enumeration and relabeling, real skew coarse entries bounded by one, real $|v|\le1$ and $n\ge24$; the relabeling enforces $n=|C|2^d$. No raw score, spectral, inverse or analytic premise remains. The exact canonical numerical identification is supplied below.

The finite structural activities $C_j$ are now defined directly from the existing physical partial-matching weights, with total degrees at most $6j$, the original logarithm coefficients and the factor $1/b!$. Their coefficients recover the original residual:
$$
 [z^k]T_Z=\sum_{j=0}^{k}[z^k]C_j,\qquad C_0=1.
$$
The actual pairing count is $\binom{D}{2e}\operatorname{pairFactor}(e)\le2^D D^e$. Ordered degrees inject into compositions of $D$. These counts, $e+h=j+b$ and the retained factorial weight give: if the index type has size $2n$, $n>0$, $M\ge1$, and the actual covariance and mean have finite weighted coefficient norms at most $M/n$ at radius $\rho\ge0$, then every $j\ge1$ satisfies
$$
 \|C_j\|_\rho\le\left(\frac{A(M)j}{n}\right)^j,
 \qquad A(M)=2^{15}\,6^3\exp(1)M^3.
$$
The activity is summable in this norm. The bound $j^b/b!\le\exp(j)$ supplies the power $j^j$; repeated labels and loops are retained.

For the chosen-enumeration graph family at positive depth $d$, take $M=(1025/2)(2^d+1)$ and radius $9/8$. The activity bound holds for every $j\ge1$ under the graph hypotheses above, without external score, spectral, inverse or analyticity assumptions.

For the actual ratio $\rho(n,k)=n^k/(n)_k$, $n>0$, $k\le n$, the order-$p$ geometric-product remainder is nonnegative and at most $\rho(n,k)(k^2/n)^{p+1}$. The completed build supplies spare-radius recovery bounds for individual activities. The zero error for the bare activity $C_0=1$ does not apply after multiplication by the core.

Positive radial-phase factorial moments, permanent polarization and AM--GM give the spectral inequality
$$
 |\operatorname{per}A|\le(n!/n^n)h_n(s_1,\ldots,s_n)\qquad(n>0),
$$
for every complex $n\times n$ matrix $A$, including singular matrices; $s_i$ are its singular values. The positive auxiliary measure is separate from the indefinite formal covariance. For the chosen-enumeration graph family, this yields a genuine circle estimate at radius $5/4$ and hence
$$
 D_n^{-1}\sum_{k>\lfloor\delta n\rfloor}
 |[z^k]\operatorname{per}(J/n+zM)|
 \le B_{d,\delta,p}n^{-p},\qquad D_n=n!/n^n.
$$
Here $\delta>0$, $p\in\mathbb N$, $n\ge24$, the depth $d$ is positive and fixed, the coarse matrix is real skew with entries bounded by one, the enumeration and relabeling are specified, and $v$ is real with $|v|\le1$. The constants are explicit and uniform over this graph class: the circle inputs are $K=2^d+1$, entry constant one and operator bound $3/4$, all derived from the graph hypotheses. This verified tail is unweighted and concerns the actual permanent, not its Gaussian core.

For a complex $n\times n$ matrix $M$, the verified exact coefficient bridge concerns
$$
 \begin{aligned}
 f_M(z)&=\frac{n^n}{n!}\operatorname{per}(J/n+zM)
       =\frac{\operatorname{per}(J+nzM)}{n!},\\
 [z^k]f_M&=\rho(n,k)F_k(M)\qquad(0\le k\le n, n>0).
 \end{aligned}
$$
The $F_k$ retain their earlier subset-pairing definition. The proof counts $(n-k)!$ completions of a selected minor and checks the row--column indexing. Above degree $n$, both the actual coefficient and $F_k$ vanish separately; the empty-matrix polynomial is one. Writing $G_M$ for the actual core, the finite projection identifies $F_k(M)$ with $[z^k]\sum_{j=0}^{m}G_MC_j$ whenever $k\le m$; terms with $j>k$ vanish. The same normalized polynomial is explicitly identified with the object in the unweighted graph-tail theorem. No infinite activity sum is used.

For this endpoint write the fixed positive construction depth as $d+1$, $d\in\mathbb N$, retaining the graph hypotheses above. The original core satisfies
$$
 \|G_M\|_{9/8}\le\exp\!\left(\frac{1025}{2}(2^{d+1}+2)\right),
$$
with finite weighted coefficient norm, uniformly in the coarse matrix, enumerations, $n$ and real $|v|\le1$. No zero-diamond or external core-norm premise is used. The term $G_MC_0=G_M$ retains its multiplier error.

For fixed-order recovery, put
$$
 \begin{aligned}
 D_d&=2^{15}6^3e\left(\frac{1025}{2}(2^{d+1}+1)\right)^3,\\
 \alpha_d&=\min\!\left\{\frac12\log\frac{17}{16},\frac1{4eD_d}\right\},
 \qquad m=\lfloor\alpha_dn\rfloor.
 \end{aligned}
$$
For fixed natural $p,\ell$ with $p\le m$, define the untruncated formal series $U$ by
$$
 U_k=[z^k]U=\sum_{j=0}^{p}\sum_{a=0}^{p-j}
 \frac{H(k,a)}{n^a}[z^k](G_MC_j),\qquad k\ge0.
$$
Here $H(k,a)$ are the actual geometric-product coefficients of the factorial multiplier. Only the coefficient cutoff is removed; the sums over $j,a$ remain finite. The previously verified finite approximation is $A(z)=\sum_{k=0}^{m}U_kz^k$, with its actual-permanent value bound on $|z|\le1$.

Writing $P_k=[z^k]f_M$, the weighted endpoint proves summability and
$$
 \sum_{k=0}^{\infty}k^\ell\lvert P_k-U_k\rvert
 \le E_{d,p,\ell}n^{-p-1}.
$$
The sum covers every $k$, not only the finite window. For $\ell=0$ the weight is one also at $k=0$. Every fixed moment $\sum_k k^\ell|U_k|$ is separately proved finite. The explicit constant depends only on fixed $d,p,\ell$, not on $n$, the coarse matrix, enumerations or $v$ in the stated graph class. Besides $n\ge24$ and $p\le m$, no $\ell$-dependent dimension condition is added. No uniformity in growing depth or order is asserted.

The proof retains the zeroth-core multiplier error and the true $\rho(n,k)$-weighted high-activity sum. Beyond $m$, the actual permanent's degree bound converts its higher-order unweighted tail into a weighted one; a separate moment estimate controls the untruncated approximant tail. Both tails are included in $E_{d,p,\ell}$, and the argument proves summability rather than treating a divergent sum as a norm.

For the falling factorial $(k)_\ell=k(k-1)\cdots(k-\ell+1)$, with $(k)_0=1$, the coefficient interface also proves
$$
 \left|\sum_{k=0}^{\infty}(k)_\ell P_k
       -\sum_{k=0}^{\infty}(k)_\ell U_k\right|
 \le E_{d,p,\ell}n^{-p-1},
$$
including summability of the approximant terms.

The analytic derivative bridge is also verified. It concerns the same untruncated series, whose evaluation function is
$$
 \mathcal U(z)=\sum_{k=0}^{\infty}U_kz^k.
$$
The actual coefficient norm at radius $17/16$ is finite. This follows from the established $9/8$ norms of $G_MC_j$, the bound $0\le H(k,a)\le k^{2a}$ and a spare-radius moment with ratio $17/18$. It uses only finite sums over $j,a$, not infinite activity convergence or unit-radius moments in place of a positive radius gap.

Termwise differentiation on an open neighborhood of $1$ gives, for every fixed natural $\ell$,
$$
 \mathcal U^{(\ell)}(1)=\sum_{k=0}^{\infty}(k)_\ell U_k,
 \qquad f_M^{(\ell)}(1)=\sum_{k=0}^{\infty}(k)_\ell P_k.
$$
The polynomial's series evaluation is proved equal to its ordinary evaluation, and the normalized polynomial is globally identified with the literal function $\operatorname{per}(J+nzM)/n!$ before differentiation. Neither analytic identification remains a caller premise. The outer-radius and derivative identities hold without the order-window condition; the error theorem retains $p\le m$ and gives
$$
 \left|f_M^{(\ell)}(1)-\mathcal U^{(\ell)}(1)\right|
 \le E_{d,p,\ell}n^{-p-1}.
$$
The constant is exactly the earlier weighted-error constant. The actual graph hypotheses and $n\ge24$ remain unchanged, with no additional $\ell$-dependent dimension threshold. These are analytic `iteratedDeriv` identities at $z=1$, not a formal differentiation of an error symbol.

The canonical numerical identification is now proved. Increasing binary labels use the newest bit as the least significant bit, and the old recursive sign is exactly $(-1)^{\operatorname{popcount}(i)}$ on $0\le i<2^r$. The entire tensor, including its inter-coarse-block term, agrees with the existing iterated doubling family. Its internal enumeration is reversed to match the old order kernel, while physical labels are increasing. The depth-one block remains $J_0=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$. Under the ordinary labels $i_{\rm fine}+2^r i_{\rm coarse}$, this is an exact matrix equality, not a caller-supplied relabeling or switching equivalence.

Consequently, the same recovery results hold for the canonical numerical family with real skew coarse matrix $B$, $|B_{ij}|\le1$, fixed depth $d+1$, real $|v|\le1$ and $n=q2^{d+1}\ge24$, where $q$ is the coarse order. The radius and derivative identities hold for every $p$; the error interfaces retain $p\le\lfloor\alpha_dn\rfloor$ and the same $E_{d,p,\ell}$, with no additional $\ell$-dependent threshold. No new core, score, inverse or analytic-identification premise is introduced. This does not classify extremizers or prove zero diamonds for arbitrary $B$.

A separate finite projection calculation takes a complex $n\times n$ matrix $S$ and independent complex parameters $f,b$. Put $A=fS+bI$, $B=-fS+bI$, $D=(1-b^2)I+f^2S^2$ and $K=D^{-1}$. If $D$ is invertible, then the actual doubled system satisfies
$$
 \mathcal B=\begin{pmatrix}I&A\\B&I\end{pmatrix},\qquad
 \mathcal B^{-1}=\begin{pmatrix}K&-AK\\-BK&K\end{pmatrix}.
$$
For $n>0$, replacing $bI$ by $b\Pi$, $\Pi=I-J/n$, in both off-diagonal blocks gives $\mathcal B_\Pi=\mathcal B+UV$, with an explicit two-color factorization. Put $G=I_2+V\mathcal B^{-1}U$ and $T=\mathcal B^{-1}UG^{-1}V\mathcal B^{-1}$. If also $G$ is invertible, the actual inverse and covariance kernel obey
$$
 \mathcal B_\Pi^{-1}=\mathcal B^{-1}-T,\qquad
 W_\Pi-W=T,\qquad \eta_\Pi-\eta=T\mathbf1.
$$
The existing scalar source difference is exactly $\mathbf1^{\mathsf T}T\mathbf1/2$. At $f=a$, $b=av$, these kernels are identified with the old actual covariances. There is no division by $b$; at $b=0$, $G=I_2$ and $T=0$. The generic identities retain the $D,G$ invertibility assumptions. On a fixed disk these assumptions are now derived: for $n\ge24$, real skew $S$ with $|S_{ij}|\le1$, real $|v|\le1$ and $|z|\le5/4$, take $f=z/n$, $b=zv/n$. The actual raw and projected systems are invertible, with both Euclidean inverse operator norms at most $16$; this also implies that $D$ and $G$ are invertible. For real $|\sigma|\le1$ and complex $|t-1|\le1/8$, the substitution $z=tn/(n+\sigma)$, $f=t/(n+\sigma)$, $b=f\sigma$ lies in that disk and gives the same projected inverse bound. No separate numerical bound for $D^{-1}$ or $G^{-1}$ is asserted. The normalized projected interaction, before multiplication by $z$, has $Q_\Pi\mathbf1=(s/n,-s/n)$, $s=S\mathbf1$: projection removes the constant parameter contribution, not the actual score source. No score hypothesis is needed for this coarse inverse estimate, which does not supply the finer entrywise projection or activity kernel-change errors.

The fixed-depth derivative identification at $1$ is complete, but no new uniform recovery error on a larger disk or arbitrary-matrix, all-radius raw recovery theorem is asserted. Infinite activity convergence, uniformity in growing depth or order, an edit-Lipschitz remainder and a closed Euler-operator polynomial identity remain outside this result. Quantitative projected recovery and structural classification remain outside this result. Separate isolated developments now establish actual maximizer entrance and the sharp bounds of Theorem 4.

Two further modules supply finite inputs to the global entry arguments G1/G2. For any actual tournament with sign matrix $S$, row scores $s_i$, energy $E=\sum_i s_i^2$, and deleted vertex set $D$ of size $k$, let $E_{-D}$ be the squared row-sum energy of the actual principal submatrix on $D^c$. The verified bounds are
$$
 \begin{aligned}
 E-kn^2-2k\sqrt{nE}&\le E_{-D},\\
 E_{-D}&\le2E+2(n-k)k^2.
 \end{aligned}
$$
They hold for every deletion size, including $k$ growing with $n$. If $L\ge0$ and $E\le Ln$, then $E_{-D}\le2(L+1)n(k+1)^2$, without a pointwise bounded-score premise.

The second finite identity concerns prescaling. For real skew $S$, $n\ne1$, $\sum_jS_{ij}=(n-1)a_i$ and $|a_i|<1$, put $v_i=a_i/(1-a_i^2)$, $w_i=a_i^2/(1-a_i^2)$, $V=\sum_iv_i$ and $W=\sum_iw_i$. Write $\mathbf v=(v_i)_i$ and $\mathbf w=(w_i)_i$ for the vectors. The actual normalized mass excess satisfies
$$
 \begin{aligned}
 \mathfrak M&=\frac1{n-1}\sum_{i,j}
 \frac{1-\delta_{ij}+S_{ij}}{(1+a_i)(1-a_j)}-n,\\
 \mathfrak M&=\frac{W^2-V^2+W+2\mathbf w^{\mathsf T}S\mathbf v}{n-1}.
 \end{aligned}
$$
Both the diagonal $+W$ and the ordered cross term $\mathbf w^{\mathsf T}S\mathbf v$ are retained. The actual-tournament specialization uses $a_i=s_i/(n-1)$ and $n\ge2$. For $n\ge2$ and real skew $S$ with $|S_{ij}|\le1$ and the same row-score equation, the quantitative extension assumes $|a_i|\le a_0$ with $0\le a_0<1$. Writing $\tau=\sum_i a_i^2$, it proves
$$
 |\mathfrak M|\le\frac{4}{(1-a_0^2)^2}
 \left(\frac{\tau+\tau^2}{n}+\frac{\tau\sqrt\tau}{\sqrt n}\right).
$$
Here $\mathfrak M$ is total mass minus $n$, not a relative error. For the actual tournament, $\tau=E/(n-1)^2$. No linear-energy or growth-rate hypothesis on $\tau$ is used; the proof derives $\sum_i a_i=0$ and bounds the actual ordered cross term.

Separately, let a real $n\times n$ matrix $Q$ have total mass exactly $n$. Choose arbitrary row and column deletion sets $I,J$ with $|I|=|J|=t<n$; they need not coincide. Set $r_i=\sum_jQ_{ij}-1$, $c_j=\sum_iQ_{ij}-1$, and let $\kappa$ be the mass of $\frac n{n-t}Q[I^c,J^c]$ minus $n-t$. Then
$$
 \kappa=\frac n{n-t}\left(\sum_{i\in I,j\in J}Q_{ij}
       -\sum_{i\in I}r_i-\sum_{j\in J}c_j-\frac{t^2}{n}\right).
$$
For $n>0$, $2t\le n$, $C,\delta\ge0$, $|Q_{ij}|\le C/n$, and all row and column residuals bounded by $\delta$ in absolute value,
$$
 |\kappa|\le4t\delta+\frac{2(C+1)t^2}{n}.
$$
The cross block and $-t^2/n$ are retained; they cancel for $Q_{ij}=1/n$. No probabilistic independence or double stochasticity is assumed. The actual normalization bridge is now proved. For the actual tournament under $n\ge2$ and the same normalized-score cap, put $L_0=(1-a_0)^{-1}$ and let $B_\nu$ denote the displayed bound on $|\mathfrak M|$. The actual nonnegative matrix $C=(J-I+S)/(n-1)$ has mass $n$, and its prescaling $C'_{ij}=C_{ij}/((1+a_i)(1-a_j))$ satisfies $C'_{ij}\ge C_{ij}/4$. Thus $\sum C'=n+\mathfrak M\ge n/4$, and
$$
 f_0=\frac n{n+\mathfrak M},\qquad \widehat C=f_0C',\qquad
 0<f_0\le4,\qquad \sum\widehat C=n
$$
hold without assuming the mass error small. Explicitly, $|f_0-1|\le4B_\nu/n$, $|\widehat C_{ij}|\le16L_0^2/n$, and both marginal residuals are bounded by
$$
 \begin{gathered}
 \widehat\delta=\frac{16L_0^2\sqrt\tau}{\sqrt n}+\frac{4B_\nu}{n},\\
 \|\widehat C-C\|_F^2\le
 \frac{128L_0^4\tau}{n}+\frac{512L_0^4B_\nu^2}{n^2}.
 \end{gathered}
$$
Consequently, for separately chosen $I,J$ of size $t$ with $2t\le n$, the actual normalized deletion mass satisfies $|\kappa|\le4t\widehat\delta+2(16L_0^2+1)t^2/n$. These are derived actual-matrix estimates; exact total mass does not mean exact row or column normalization. The local scaling theorem below is conditional on an actual centered spectral gap. The sharp extension gives actual maximizers $\tau\le D/n$, hence raw score energy $\sum_i s_i^2=O(n)$, in addition to the recovery and eventual fixed-cap entrance estimates. Structural classification and zero-diamond status of arbitrary maximizers remain unproved.

\subsection*{Local scaling with a fixed spectral gap}
Let $M$ be a nonnegative real $m\times m$ matrix, $m\ge1$. Write
$$
 r_i=\sum_jM_{ij}-1,\quad c_j=\sum_iM_{ij}-1,\quad
 E_f=\sum_i r_i^2+\sum_j c_j^2,\quad P=J/m,\quad \Pi=I-P.
$$
Assume $M_{ij}\le C/m$, $|r_i|,|c_j|\le\varepsilon$ and
$\|\Pi M\Pi\|_2\le q$, with $C\ge0$ and $0\le q<1$. All operator norms below are Euclidean. Set
$$
 \begin{gathered}
 \beta=\tfrac32+2(C+4)+\frac{4(C+4)^2}{1-q},\qquad K=2\beta,\\
 \varepsilon_0=\min\{1,(8K)^{-1},(64K^2)^{-1},(1-q)/8\}.
 \end{gathered}
$$
If $0\le\varepsilon\le\varepsilon_0$, there are real vectors $x,y$ with
$\sum_i x_i=\sum_j y_j$ and $|x_i|,|y_j|\le a:=2K\varepsilon$ such that
$N_{ij}=M_{ij}\exp(x_i+y_j)$ is doubly stochastic. Put $g=1-q-4\varepsilon>0$ and $S=1+\varepsilon$. The same vectors satisfy
$$
 \begin{gathered}
 \sum_i x_i^2+\sum_j y_j^2\le \frac{e^{4a}}{g^2}E_f,
 \qquad N_{ij}\le e^{2a}C/m,\\
 \|N-M\|_F^2\le\frac{2CS e^{8a}}{m g^2}E_f,\\
 \|N-M\|_2\le S(e^{2a}-1),\qquad
 \|N-P\|_2\le q+S(e^{2a}-1)\le(1+q)/2<1.
 \end{gathered}
$$
Here $E_f$ is the total residual energy. Coordinate bounds give only $E_f\le2m\varepsilon^2$; thus the displayed squared Frobenius estimate is generally $O(\varepsilon^2)$, not $O(\varepsilon^2/m)$. The latter requires the additional input $E_f=O(\varepsilon^2)$.

*Proof.* First fix the gauge $\sum x_i=\sum y_j$. The actual marginal map $F(x,y)$ consists of the row and column sums of $N$ minus one, and $F(0)=(r,c)$. Its derivative at zero is
$$
 H=\begin{pmatrix}\operatorname{diag}(\operatorname{row}M)&M\\
 M^{\mathsf T}&\operatorname{diag}(\operatorname{col}M)\end{pmatrix}.
$$
Centering separates a model with spectral gap $1-q$ from a symmetric perturbation whose absolute row sums are at most $4\varepsilon$. Adding the signed gauge projection removes the one-dimensional ambiguity $(x,y)\mapsto(x+t,y-t)$. The density and spectral assumptions give a real inverse $L$ with the required uniform row bound; this step does not assume a scaling root.

For $R(z)=F(z)-F(0)-Hz$, the scalar exponential remainder bounds its Lipschitz constant on the infinity ball of radius $a$ by $2S(e^{2a}-1)$. The stated threshold makes $T(z)=-L(F(0)+R(z))$ preserve that ball and makes its contraction constant at most $1/2$. The resulting fixed point satisfies both the actual equations $F(z)=0$ and the gauge condition.

The Euclidean estimate is proved directly for this root, rather than by converting the infinity norm. Multiplying its marginal equations by the corresponding coordinates gives
$$
 -\langle F(0),z\rangle
 =\sum_{i,j}M_{ij}(e^{x_i+y_j}-1)(x_i+y_j).
$$
For $|s|\le2a$, $(e^s-1)s\ge e^{-2a}s^2$. On balanced vectors the model quadratic form is at least $(1-q)\|z\|_2^2$. Symmetry and $2|z_i z_j|\le z_i^2+z_j^2$ bound the perturbation by $4\varepsilon\|z\|_2^2$, with no dimension factor. Therefore the right-hand side is at least $e^{-2a}g\|z\|_2^2$. Cauchy--Schwarz, with $z=0$ treated separately, yields $\|z\|_2\le e^{2a}\|F(0)\|_2/g$.

Finally $M_{ij}^2\le(C/m)M_{ij}$, $|e^s-1|\le e^{2a}|s|$ and $(x_i+y_j)^2\le2(x_i^2+y_j^2)$ give
$\|N-M\|_F^2\le2CS e^{4a}\|z\|_2^2/m$ by finite summation. Substitute the root-energy bound. A finite Schur estimate gives the operator bound from absolute row and column sums. Since $N$ is doubly stochastic, $N-P=\Pi N\Pi$. The threshold gives $KS(e^{2a}-1)\le1/4$, while $K(1-q)\ge128$; hence the spectral increment is at most $(1-q)/512$, which implies the stated fixed gap.

This local matrix theorem retains its stated density, marginal and centered spectral assumptions. The separate actual path-bound route discharges the recovery and entrance inputs needed for its final bounds; structural classification and the actual sequence's F and common all-multiples J remain unproved.

Five abstract analytic modules supply further F/J components. Their F, all-multiples J and periodic-jump predicates are interfaces, not theorems about the extremal sequence. For $b>0$, a $b$-periodic sequence and a primitive root of order $2b$, finite half-period pairing proves the first resonance $-\kappa/(2b)$. Bounded complex coefficients give genuine identities for every real radial derivative inside $0<x<1$. Summable falling-factorial moments give finite derivative limits at $1$; a global positive-index bound $|c_n|\le Cn^{-k-2}$ supplies these moments for $h\le k$ by the majorant $C/n^2$. No unknown function-level remainder is differentiated.

For antiperiodic coefficients $v_{n+b}=-v_n$, $b>0$, the exact identity
$$
 \sum_{n\ge0}v_nz^n=\frac{\sum_{n=0}^{b-1}v_nz^n}{1+z^b},\qquad |z|<1,
$$
gives finite left limits of all actual unweighted radial derivatives through the rational extension at $1$. Dirichlet/Abel separately gives a finite radial limit for $\sum_{n\ge0}v_{n+1}x^n/(n+1)^d$, $d\ge1$; at $d=1$ the argument uses natural-order convergence, not absolute convergence. For every integer $q>0$ the sparse harmonic identity and its real radial regular part are
$$
 \sum_{\substack{n\ge1\\q\mid n}}\frac{z^n}{n}=-\frac{\log(1-z^q)}q,\qquad
 \sum_{\substack{n\ge1\\q\mid n}}\frac{x^n}{n}+\frac{\log(1-x)}q
 \longrightarrow-\frac{\log q}q.
$$
The first identity holds for $|z|<1$ and the limit as $x\uparrow1$. The abstract bridge from F and common all-multiples J to true radial asymptotics is now proved. For $r\ge1$, a primitive $2^{r+1}$-st root $\omega$, a fixed-valuation expansion F and the uniform jump hypothesis J with coefficient $2^{r(r+1)}L$, every derivative of order $h<2r$ has a finite radial limit, while the derivative of order $2r$ minus $L2^{r^2-1}\log(1-x)$ has a finite limit as $x\uparrow1$. J concerns all sufficiently large positive multiples of $2^r$, not just one exact valuation class. The proof includes falling-factorial correction, sparse logarithmic derivatives, Laurent assembly, periodic jumps and finite valuation gluing. This endpoint allows $L=0$; nonzero logarithmic singularity requires the additional input $L\ne0$. The actual extremal sequence's F and common all-multiples J are still unproved, so full Condition R remains open.

\paragraph{Verification of the local extensions.} The local scaling endpoint, abstract radial bridge, actual coarse MainBound and bounded-normalized-energy endpoint are covered by the verified 557-module isolated integration snapshot described above. The additional six-module sharp extension has its own complete independent compilation and audit record; the combined-tree verification status is stated above. PDF acceptance and publication remain separate from Lean verification.

Earlier manuscripts are in `historical/formula-restrictions`. Notes [7] give a route to R; Proposition B.1 distinguishes its verified implication from remaining upstream obligations.

The article byline identifies Xingchen Liu as its author. Repository copyright and attribution are governed by the root LICENSE, which credits Xingchen Liu and Xiangyu Ye. The repository is licensed under Creative Commons Attribution 4.0 International (CC BY 4.0).

## References

[1] Alexander Divoux and Shouda Wang. *The maximum number of Hamiltonian cycles in tournaments*. arXiv:2610.23755v1 [math.CO], 2026, submitted 16 October 2026. Theorem 1.4 is cited here. DOI: 10.48550/arXiv.2610.23755. Full text of the fixed version.

[2] Sever Angel Popescu. *A simple and self-contained proof for the Lindemann-Weierstrass theorem*. arXiv:2306.14352v2 [math.NT], 2023, revised 17 September 2023. Theorem 3.2 is cited here. DOI: 10.48550/arXiv.2306.14352. Full text of the fixed version.

[3] Richard P. Stanley. *Differentiably Finite Power Series*. European Journal of Combinatorics **1**(2) (1980), 175--188. DOI: 10.1016/S0195-6698(80)80051-5. Official paper provided by the author.

[4] Jean-Paul Allouche and Jeffrey Shallit. *The ring of k-regular sequences*. Theoretical Computer Science **98**(2) (1992), 163--197. DOI: 10.1016/0304-3975(92)90001-V. Preprint provided by the authors.

[5] Philippe Flajolet, Stefan Gerhold and Bruno Salvy. *On the non-holonomic character of logarithms, powers, and the $n$th prime function*. Electronic Journal of Combinatorics **11**(2) (2005), A2. arXiv:math/0501379.

[6] Jason P. Bell, Michael Coons and Eric Rowland. *The rational-transcendental dichotomy of Mahler functions*. Journal of Integer Sequences **16** (2013), Article 13.2.10.

[7] Xingchen Liu. *Tournament paths research notes*. Repository snapshot, commit `c049e04062ed122c71f519857d54366d07b7019b`. Relevant notes: `round96core_common_asymptotic_jets.md`, `round98sources_radial_log_singularities.md`, and `round120sources_snapshot_review.md`. <https://github.com/LStar404/tournament-paths-research-notes/tree/c049e04062ed122c71f519857d54366d07b7019b>.
