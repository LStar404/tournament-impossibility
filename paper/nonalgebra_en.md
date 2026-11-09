# Non-algebraicity of the Extremal Hamiltonian Path Sequence and Formula Restrictions

Xingchen Liu

Independent Researcher

`lxc-em5158@outlook.com`

8 November 2026 · Revision v0.4.0

## Abstract
Let $P(n)$ be the maximum number of directed Hamiltonian paths in an $n$-vertex tournament, and put $a_n=2^{n-1}P(n)/n!$. An existing asymptotic theorem gives $a_n\to L=\cosh1/\cos1$. Rationality of the coefficients and transcendence of $L$ imply non-algebraicity of the ordinary, exponential and half-scale remainder generating functions. The same limit also excludes finite-dimensional linear digit representations in every integer base: more generally, a rational-valued $q$-regular sequence with a finite limit after division by an integer power of $n$ has a rational limit. Separately, an explicit radial boundary condition R implies a natural boundary, non-P-recursiveness and necessary cancellation identities for mixed derivative--contraction relations. R is an additional hypothesis for the actual extremal sequence, not a consequence of its asymptotic limit. These results exclude specified classes of formulas, not all closed forms or efficient algorithms.

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
We take this known limit as the starting point and do not reprove it.

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

- **Proved from the cited asymptotic theorem:** the actual $A$, $E$ and $M$ are not algebraic, and $a_n,m_n,P(n)$ are not $q$-regular for any $q\ge2$. This uses the existing asymptotic theorem only and needs no additional classification of extremal tournaments.

- **Conditional on R:** the natural-boundary, non-P-recursiveness and contraction conclusions. The research notes contain a route to R whose upstream structural dependencies are specified in Appendix B; those dependencies are not all reverified here.

- **Still open here:** whether $P(n)$ admits an exact closed form of some other kind, whether an efficient exact algorithm exists, and whether the actual remainder $M$ has a transcendental expression that can be evaluated independently.

No NP-hardness statement or general algorithmic lower bound is obtained. Establishing R for the actual extremal sequence requires additional verified input. The limit and integrality alone do not suffice: for all sufficiently large $n$ set $Q_n=\lfloor L\mu_n\rfloor$ and $b_n=Q_n/\mu_n$, with arbitrary rational initial values. Then $b_n-L=O(2^n/n!)$, so $\sum_{n\ge1}b_nz^n=Lz/(1-z)+H(z)$ with $H$ entire. This is not an extremal tournament construction; it separates the known numerical asymptotic from the missing boundary information.

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

**Relation to the research notes.** The research notes [7], fixed at commit `c049e040`, provide a route for the actual sequence: the common-expansion and resonant-jump statements F/J in `round96core` have $\kappa_r=2^{r(r+1)}L$ for $r\ge4$, and `round98sources` derives the radial condition from those inputs. Thus accepting the stated structural and exact-recovery inputs gives R with $C=L$ and $r_0=4$. The analytic implication F/J $\Rightarrow$ R has been checked for this revision. The upstream path-recovery, uniform-tail, zero-diamond-window and depth-induction arguments have not all been independently reverified here. The notes therefore contain a proof route, rather than no argument, but this manuscript does not present that entire route as an independently certified unconditional theorem. Its applications in Appendices C and D retain R explicitly; Appendix A does not depend on this chain.

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

The checked build record of 9 November 2026, 05:00 UTC, covers 170 Lean modules. In addition to the non-algebraicity conclusions of Appendix A.4, they formalise the non-$q$-regularity of the actual sequences $a_n$ and $m_n$ for every integer $q\ge2$, using the finite-dimensional complex span of the $q$-kernel as the definition. For $P(n)$ they formalise the growth obstruction and exclude fixed finite-alphabet continuous-linear digit transitions with a fixed linear output, including finite-dimensional complex matrix models. The equivalence between this representation and the $q$-kernel definition is not formalised in that application.

The general rational-limit assertion of Theorem A.5 is also formalised in full: for a rational-valued $q$-regular sequence, convergence after division by an integral nonnegative power of the index forces the limit to be rational. The modules `RationalRadial`, `RationalLinearDescent`, `RationalSeriesLimit` and `QRegularRationalLimit` supply the additional bridges and endpoint. The hypotheses `ExtremalAsymptotic` and `FourExponentialIndependence` remain explicit external inputs: the graph-theoretic asymptotic theorem and the required Lindemann--Weierstrass consequence are not proved in Lean here. The growth argument for $P(n)$ needs only the former input. Condition R and the complete arguments of Appendices B--E remain outside the formalisation. Build results and axiom audits are recorded under `lean/verification`; the source files alone do not certify a successful verification run.

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
The score-energy identity and the passage from the Hermitian inner product to this ordinary bilinear source are formalised. Zero-diamond status alone does not imply the energy assumption.

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
The proof constructs a genuine bijection between pairings and the choice of the distinguished point's partner together with a residual pairing, and derives the edge-weight factorization. Odd-cardinality moments vanish; the empty moment equals one. These are finite algebraic results. Formal linear/quadratic exponential identities and their resummation, general factorial moment counting, analytic tail estimates and permanent recovery remain unformalised, as do projection, activity comparisons and full Condition R.

The formal covariance $zQ_v$ is generally indefinite; it is not used as the covariance of a positive Gaussian measure.

Earlier manuscripts remain in `historical/formula-restrictions` for comparison. The pinned research notes [7] supply a route to R; the dependency discussion after Proposition B.1 distinguishes its verified analytic implication from the upstream arguments not fully rechecked in this revision.

© 2026 Xingchen Liu. Text and source files are licensed under Creative Commons Attribution 4.0 International (CC BY 4.0).

## References

[1] Alexander Divoux and Shouda Wang. *The maximum number of Hamiltonian cycles in tournaments*. arXiv:2610.23755v1 [math.CO], 2026, submitted 16 October 2026. Theorem 1.4 is cited here. DOI: 10.48550/arXiv.2610.23755. Full text of the fixed version.

[2] Sever Angel Popescu. *A simple and self-contained proof for the Lindemann-Weierstrass theorem*. arXiv:2306.14352v2 [math.NT], 2023, revised 17 September 2023. Theorem 3.2 is cited here. DOI: 10.48550/arXiv.2306.14352. Full text of the fixed version.

[3] Richard P. Stanley. *Differentiably Finite Power Series*. European Journal of Combinatorics **1**(2) (1980), 175--188. DOI: 10.1016/S0195-6698(80)80051-5. Official paper provided by the author.

[4] Jean-Paul Allouche and Jeffrey Shallit. *The ring of k-regular sequences*. Theoretical Computer Science **98**(2) (1992), 163--197. DOI: 10.1016/0304-3975(92)90001-V. Preprint provided by the authors.

[5] Philippe Flajolet, Stefan Gerhold and Bruno Salvy. *On the non-holonomic character of logarithms, powers, and the $n$th prime function*. Electronic Journal of Combinatorics **11**(2) (2005), A2. arXiv:math/0501379.

[6] Jason P. Bell, Michael Coons and Eric Rowland. *The rational-transcendental dichotomy of Mahler functions*. Journal of Integer Sequences **16** (2013), Article 13.2.10.

[7] Xingchen Liu. *Tournament paths research notes*. Repository snapshot, commit `c049e04062ed122c71f519857d54366d07b7019b`. Relevant notes: `round96core_common_asymptotic_jets.md`, `round98sources_radial_log_singularities.md`, and `round120sources_snapshot_review.md`. <https://github.com/LStar404/tournament-paths-research-notes/tree/c049e04062ed122c71f519857d54366d07b7019b>.
