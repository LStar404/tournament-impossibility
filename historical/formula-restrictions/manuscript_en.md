# Restrictions on formulas for tournament Hamiltonian path maxima

Xingchen Liu and Xiangyu Ye

Independent Researchers

lxc-em5158@outlook.com

2 November 2026 · Draft v0.1

## Abstract

How many Hamiltonian paths can a tournament have? Let $P(n)$ denote the largest possible count. This paper identifies several classes of formulas that can be rigorously excluded. Using a known asymptotic theorem, we prove that three generating functions associated with $P(n)$ are not algebraic. Stronger exclusions, including certain linear recurrences and dilation formulas, require an additional condition stated explicitly here. We do not prove that the actual extremal sequence satisfies it. The main text explains the conclusions and their proof ideas; the appendices contain complete proofs. These results restrict particular forms of expression. They do not prove that $P(n)$ has no general closed form, or that computing it is hard.

Keywords: tournaments; Hamiltonian paths; extremal counting; generating functions; restrictions on formulas.

## 1. Which kinds of formulas are we trying to exclude?

A tournament is a directed graph with exactly one directed edge between each pair of vertices. A directed Hamiltonian path follows the edges and visits every vertex once. Let $H(T)$ count the vertex permutations that form such paths in a tournament $T$, and define

$$
P(n)=\max_{|V(T)|=n}H(T).
$$

The goal remains to find an exact formula for $P(n)$. This paper addresses a narrower question first: which classes of formulas can already be ruled out?

The count $P(n)$ grows on a factorial scale. A natural benchmark is the average number of paths in a uniformly random tournament,

$$
\mu_n=\frac{n!}{2^{n-1}}.
$$

There are $n!$ vertex permutations. For each permutation, its $n-1$ consecutive edges have the required directions with probability $2^{-(n-1)}$. We therefore study

$$
a_n=\frac{P(n)}{\mu_n}.
$$

Thus $a_n$ measures how many times the average the maximum can be. The asymptotic theorem of Divoux and Wang [1, Theorem 1.4] gives

$$
a_n\longrightarrow L=\frac{\cosh1}{\cos1}.
$$

We use this established result without reproving it.

To study the whole sequence together, we put its terms into a power series:

$$
A(z)=a_1z+a_2z^2+\cdots=\sum_{n\ge1}a_nz^n.
$$

This is the *generating function* of $(a_n)$. For some classes of formulas, it is easier to study this function than individual terms. A restriction on the generating function, however, does not automatically rule out a simple formula for those terms.

## 2. An unconditional restriction: three generating functions are not algebraic

Here *algebraic function* has a precise meaning: a function $G(z)$ satisfying some nonzero polynomial equation $F(z,G(z))=0$. Rational functions belong to this class, as do algebraic expressions such as square roots.

**Conclusion 1.** $A(z)$ is not algebraic. The exponential generating function of the original maximum counts,

$$
E(z)=\sum_{n\ge1}\frac{P(n)}{n!}z^n=2A(z/2),
$$

is not algebraic either. Both conclusions hold even if the polynomial equation is allowed arbitrary complex coefficients.

The proof rests on two facts. First, $L=\cosh1/\cos1$ is transcendental: it is not a root of any nonzero polynomial with rational coefficients. Second, all $a_n$ are rational. For an algebraic generating function with rational Taylor coefficients, the following limit, if finite, must be an algebraic number:

$$
\lim_{z\to1^-}(1-z)A(z).
$$

In this case the limit equals $L$, giving a contradiction. Appendix A supplies the full argument.

Next consider a possible way of computing the sequence: reduce an even size $n$ to size $n/2$, then add a remainder. For the actual sequence $(a_n)$, define that remainder $m_n$ at even indices by

$$
n^2a_n=2a_{n/2}+m_n.
$$

At odd indices, simply set $m_n=n^2a_n$. Collect the remainders into another generating function,

$$
M(z)=\sum_{n\ge1}m_nz^n.
$$

**Conclusion 2.** $M(z)$ is not algebraic. Thus the remainder in this particular halving recurrence cannot have a rational or algebraic generating function.

The reason is the same as for Conclusion 1, with a different limit:

$$
\lim_{z\to1^-}(1-z)^3M(z)=2L.
$$

This gives a concrete test for proposed formulas. Within the exact recurrence displayed above, a candidate remainder with a rational or algebraic generating function cannot recover the actual $P(n)$. Other forms of remainder remain possible; the recurrence itself has not been ruled out.

## 3. Stronger exclusions require an additional condition

A finer analysis concerns the behavior of $A(z)$ at the unit circle. We call the required condition R. At specified points forming an increasingly dense set on that circle, a prescribed derivative is the first to exhibit logarithmic divergence, with a prescribed coefficient. Appendix B gives the exact points, coefficients, and a sufficient condition.

**Every conclusion in this section assumes that the actual $A(z)$ satisfies R. This paper does not prove that assumption.**

If R holds, the unit circle is a *natural boundary* for $A$. This means that the analytic function inside the disk cannot be continued through any point of its boundary. Such behavior restricts the finite equations the function can satisfy.

Using the more precise boundary behavior specified by R, we obtain three kinds of exclusion:

- **Linear recurrences of fixed order with polynomial coefficients.** $P(n)$ cannot eventually satisfy a nontrivial relation $\sum_{j=0}^{d}p_j(n)P(n+j)=0$, with fixed order $d$ and polynomial coefficients $p_j$. Other kinds of recurrence are not excluded.
- **Certain dilation formulas.** These are finite linear relations involving functions such as $A(z)$, $A(z^2)$, and $A(z^3)$. Relations without derivatives are excluded when their coefficients are rational functions and, after denominators are cleared, the right-hand side extends analytically through every point of the unit circle except finitely many. With derivatives allowed, an entire class of relations in integer bases other than powers of two is still excluded; binary dilation remains possible. Appendix C gives the exact scope.
- **Linear digit models of fixed size.** Such a model stores a fixed number of values. Each input digit updates them using a fixed matrix assigned to that digit; a fixed weighted sum gives the final output. No such model can evaluate $a_n$ exactly, in any fixed integer base. This restricts a particular computational model, not all algorithms. Appendix D contains the definition and proof.

The first conclusion concerns a uniform linear rule using a fixed number of neighboring terms and polynomial coefficients. The other two concern restricted representations based on fixed dilations or digit-by-digit processing.

## 4. What do these results leave open?

A non-algebraic generating function does not mean that its coefficients lack a simple formula. For example, the sequence $1/n$ has a very simple formula, but its generating function $-\log(1-z)$ is not algebraic.

Even a natural boundary can coexist with a short recurrence. Appendix E constructs a sequence different from the actual tournament maxima. It is zero at odd indices and satisfies, at even indices,

$$
s_n=-\frac1n+\frac{2}{n^2}s_{n/2}.
$$

Its generating function has a natural boundary. Yet, given $n$, repeated halving evaluates $s_n$ exactly. Complicated analytic boundary behavior and a short evaluation rule can therefore occur together.

The conclusions separate into three levels:

- **Proved here:** the actual functions $A,E,M$ are not algebraic. This uses the known asymptotic theorem and requires no additional classification of extremal tournaments.
- **Proved under the added condition:** the recurrence, dilation, and digit-model restrictions in the preceding section. Whether the actual sequence satisfies R still requires verification.
- **Not resolved in this paper:** whether $P(n)$ has an exact formula of another kind, whether it has an efficient exact algorithm, and whether the actual remainder $M$ admits a transcendental expression that can be evaluated independently.

We obtain neither NP-hardness nor a general algorithmic lower bound. The next steps are to verify the actual inputs needed for R and to investigate formulas that these results do not exclude.


## Appendix A. Proof of the unconditional result

We use the Euler differential operator $\Theta=z\,d/dz$.

**Lemma A.1.** $L=\cosh1/\cos1$ is transcendental.

**Proof.** If $L$ were algebraic, then

$$
e+e^{-1}-Le^i-Le^{-i}=0
$$

would contradict Lindemann–Weierstrass [2, Theorem 3.2]: $1,-1,i,-i$ are distinct algebraic exponents and $1,1,-L,-L$ are algebraic coefficients not all zero. Also $\cos1\ne0$. $\square$

**Lemma A.2 (descent).** If $B(z)\in\mathbb Q[[z]]$ is algebraic over $\mathbb C(z)$, it is algebraic over $\mathbb Q(z)$.

**Proof.** Clear denominators in a nonzero relation $H(z,B(z))=0$. Choose a $\mathbb Q$-basis $\beta_1,\ldots,\beta_s$ for the space spanned by the finitely many complex coefficients of $H$. Write

$$
H(z,Y)=\sum_{j=1}^s\beta_jH_j(z,Y),\qquad H_j\in\mathbb Q[z,Y].
$$

Every coefficient of $H_j(z,B(z))$ is rational. Coefficient comparison and $\mathbb Q$-linear independence give $H_j(z,B(z))=0$ for every $j$. At least one $H_j$ is nonzero. $\square$

**Lemma A.3 (finite radial limit).** Suppose $B\in\mathbb Q[[z]]$ is analytic in the unit disk and algebraic over $\mathbb C(z)$. If $(1-\rho)^dB(\rho)\to c$ as $\rho\uparrow1$ for an integer $d\ge0$, then $c$ is algebraic.

**Proof.** By Lemma A.2, $C(z)=(1-z)^dB(z)$ satisfies a nonzero relation $R(z,C(z))=0$ over $\mathbb Q$. Divide out the largest power of $z-1$ common to all coefficients of $R$ as a polynomial in its second variable. Then $R(1,Y)\not\equiv0$. Taking the radial limit gives $R(1,c)=0$. A nonzero constant specialization would already be a contradiction. $\square$

**Theorem A.4.** $A$, $E$, and

$$
M(z)=\Theta^2A(z)-2A(z^2)
$$

are transcendental over $\mathbb C(z)$.

**Proof.** The rational coefficients $a_n\to L$ give $(1-\rho)A(\rho)\to L$. To verify this limit, split $a_n-L$ into a finite prefix and a tail bounded by $\varepsilon$; after multiplication by $1-\rho$, the prefix vanishes and the tail is bounded by $\varepsilon$. Lemmas A.1 and A.3 exclude algebraicity of $A$, and scaling excludes algebraicity of $E$.

Writing $M(z)=\sum_{n\ge1}m_nz^n$, we have

$$
m_n=n^2a_n-2\mathbf1_{\{2\mid n\}}a_{n/2}\in\mathbb Q,\qquad
\frac{m_n}{n^2}\longrightarrow L.
$$

The indicated second term is absent when $n$ is odd. Since

$$
\sum_{n\ge1}n^2\rho^n=\frac{\rho(1+\rho)}{(1-\rho)^3},
$$

the same prefix–tail argument yields $(1-\rho)^3M(\rho)\to2L$: the scaled error tail has limit superior at most $2\varepsilon$. Lemma A.3 again contradicts transcendence of $L$. $\square$

Thus the specific equation $\Theta^2A-2A(z^2)=F$ cannot have an algebraic right-hand side, even over arbitrary complex constants. Multiplication of $M$ by a nonzero rational function, or addition of an algebraic function, cannot remove this obstruction. This does not exclude a transcendental D-finite defect: $e^z/(1-z)^3$ has rational Taylor coefficients, is D-finite, and has normalized radial limit $e$.

## Appendix B. The radial hypothesis

For a positive integer $n$, $\nu_2(n)$ is the largest nonnegative integer $r$ such that $2^r$ divides $n$.

Let $G$ be analytic in the unit disk and $C\ne0$ a fixed complex number.

**Hypothesis R.** There is an integer $r_0\ge1$ such that, for each fixed $r\ge r_0$ and every primitive $2^{r+1}$-st root $\omega$, all derivatives of $G(\omega x)$ of order below $2r$ have finite limits as $x\uparrow1$, and

$$
\frac{d^{2r}}{dx^{2r}}G(\omega x)
=C\,2^{r^2-1}\log(1-x)+O_{r,\omega}(1).
$$

This concerns actual derivatives. Formally differentiating an uncontrolled remainder does not establish it. Each depth is fixed before taking the radial limit; no estimate uniform in growing depth is assumed.

**Proposition B.1 (periodic asymptotic criterion).** Suppose $G(z)=\sum_{n\ge1}b_nz^n$, with bounded coefficients. The following conditions imply R.

- For every fixed $s\ge0$ and $J$, on integers with $\nu_2(n)=s$ there is an expansion $b_n=\sum_{j=0}^J\alpha_{s,j}n^{-j}+O_{s,J}(n^{-J-1})$ with constant coefficients.
- For every fixed $r\ge r_0$, some $B_r$ analytic at zero satisfies, uniformly over sufficiently large multiples of $2^r$,

$$
b_n=B_r(1/n)-\kappa_r\mathbf1_{\{2^{r+1}\mid n\}}n^{-2r-1}
       +O_r(n^{-2r-2}),\qquad
\kappa_r=C\,2^{r(r+1)}.
$$

**Proof.** Fix $r$, put $q=2^{r+1}$ and $d=2r+1$. Combine the finitely many classes $s<r$ with the second condition to obtain

$$
b_n=\sum_{j=0}^{d}c_j(n)n^{-j}+O_r(n^{-d-1}).
$$

For $j<d$, the periodic coefficient $c_j$ has period dividing $2^r$. Moreover $c_d(n)=u(n)-\kappa_r\mathbf1_{\{q\mid n\}}$, with $u$ also $2^r$-periodic. With the convention

$$
\widehat c_j(\omega)=\frac1q\sum_{t=1}^q c_j(t)\omega^t,
$$

every primitive $q$-th root therefore has $\widehat c_j(\omega)=0$ for $j<d$ and $\widehat c_d(\omega)=-\kappa_r/q$.

Finite Fourier decomposition expresses the explicit terms through $\operatorname{Li}_j(z/\zeta)$; nonpositive indices are interpreted using geometric-series derivatives. The only first resonant term at $\omega$ is $-(\kappa_r/q)\operatorname{Li}_{2r+1}(z/\omega)$. All other terms extend analytically near $\omega$. The remainder has coefficients $O_r(n^{-2r-2})$, so its $2r$-th derivative has absolutely summable coefficients.

Finally, $\Theta^{2r}\operatorname{Li}_{2r+1}(x)=-\log(1-x)$. The triangular relation between Euler and ordinary derivatives gives the same leading logarithm for the $2r$-th ordinary derivative, while lower derivatives have finite limits. Its coefficient is $\kappa_r/q=C2^{r^2-1}$, as required. Finite prefixes add only polynomials. $\square$

For the actual extremal sequence, one would take $b_n=a_n$ and $C=L$. Proposition B.1 states the required input precisely; its tournament-theoretic hypotheses are not proved here. All ensuing applications to $P(n)$ remain conditional on R.

## Appendix C. Proofs for dilation relations

A function is *D-finite* if it satisfies a nonzero linear differential equation with polynomial coefficients. This is the analytic counterpart of a fixed-order polynomial-coefficient recurrence for its Taylor coefficients [3].

**Theorem C.1.** Under R, the unit circle is a natural boundary for $G$, and $G$ is not D-finite.

**Proof.** At each specified dyadic root a finite-order derivative diverges, preventing analytic continuation there. Such roots are dense on the circle, preventing continuation through any arc. A polynomial-coefficient linear differential equation permits finite-plane singularities only at the finitely many zeros of its leading coefficient. $\square$

For right-hand sides below we use the following **finite-boundary condition**: after clearing the rational coefficient denominators, the selected disk branch extends analytically through every boundary point except finitely many. A D-finite right-hand side satisfies this condition whenever the proposed identity holds: the cleared left side is analytic in the disk, and ordinary points of the differential equation admit analytic continuation.

**Theorem C.2 (necessary highest-order symbol).** Suppose R holds and

$$
\sum_{m\in\mathcal M}Q_m(z,\Theta)[G(z^m)]=F(z),
$$

$$
Q_m(z,\Theta)=\sum_{j=0}^{d_m}p_{m,j}(z)\Theta^j,
$$

where $\mathcal M$ is a finite set of distinct positive integers, the coefficients are rational functions, $p_{m,d_m}\ne0$, and $F$ satisfies the finite-boundary condition. Coefficients are on the left; derivatives act on the entire composite. Write

$$
m=2^{s_m}t_m,\qquad t_m\ \mathrm{odd},\qquad
w=\max_m(d_m+2s_m),
$$

and let $I_t=\{m:d_m+2s_m=w,\ t_m=t\}$. Then, for each odd $t$,

$$
\sum_{m\in I_t}2^{-s_m^2}t^{-2s_m}p_{m,d_m}(z)=0.
$$

**Proof.** Clear denominators, leaving polynomial coefficients and finitely many boundary exceptions. Fix $r$ sufficiently large that $r-s_m\ge r_0$ and $K=2r-w\ge0$. At a primitive $2^{r+1}$-st root $\omega$, the first unbounded derivative of $G(\omega^m y)$ has order $k_m=2(r-s_m)$.

Along $z=\omega x$, $\Theta=x\,d/dx$. Differentiate the identity $K$ more times with respect to $x$. Only the highest terms with $d_m+2s_m=w$ reach derivative order $k_m$; every other contribution involves lower derivatives with finite limits. Writing $f(y)=G(\omega^m y)$, the unique highest term is

$$
p_{m,d_m}(\omega x)x^{d_m}(mx^{m-1})^{k_m}f^{(k_m)}(x^m).
$$

The product and chain rules therefore give logarithmic coefficient

$$
C\,2^{(r-s_m)^2-1}m^{2(r-s_m)}p_{m,d_m}(\omega)
=C\,2^{r^2-1}t_m^{2r}2^{-s_m^2}t_m^{-2s_m}p_{m,d_m}(\omega).
$$

Replacing endpoint multipliers by their limits costs only $O((1-x)\log(1-x))$. Away from the finite exceptional set, the right-hand derivative has a finite limit, so these coefficients sum to zero.

For fixed $r$, this is a polynomial identity evaluated at all but finitely many primitive $2^{r+1}$-st roots. Its degree is bounded independently of $r$, whereas there are $2^r$ such roots; thus it is identically zero for all sufficiently large $r$. Grouping by odd parts gives $\sum_t t^{2r}T_t(z)=0$, where $T_t$ is the asserted sum. Taking as many consecutive $r$ as there are odd parts produces an invertible Vandermonde matrix in the distinct numbers $t^2$. Hence every $T_t=0$. All analytic limits were taken at fixed $r$; only exact algebraic identities were subsequently compared. $\square$

**Corollary C.3.** Under R there is no nontrivial finite undifferentiated relation $\sum_m p_m(z)G(z^m)=F(z)$ with rational coefficients and the stated right-hand condition.

**Proof.** All $d_m=0$. Terms of maximal weight have the same $s_m$, and distinct such terms have distinct odd parts. Every nonempty $I_t$ is a singleton, contradicting Theorem C.2. $\square$

**Corollary C.4.** If no quotient of distinct dilation factors is an integer power of two, no relation in Theorem C.2 exists. In particular, for an integer $b\ge2$ not a power of two, there is no such finite differential–Mahler relation among $G(z^{b^j})$.

**Proof.** Distinct factors have distinct odd parts, again giving singletons. If $b=2^hu$ with odd $u>1$, the odd parts of $b^j$ are the distinct $u^j$. $\square$

Any surviving maximal-weight odd-part group must contain at least two terms, whose highest derivative orders differ by $2(s_2-s_1)$. Thus a spread of at most one among all highest orders is impossible. For $p(z,\Theta)G(z)-q(z,\Theta)[G(z^2)]=F(z)$, the necessary conditions are $\deg_\Theta p=\deg_\Theta q+2$ and $q_{\mathrm{top}}=2p_{\mathrm{top}}$. These conditions are not sufficient.

## Appendix D. Linear digit representations and recurrences

For a fixed integer base $q\ge2$, a sequence $(b_n)_{n\ge0}$ is called $q$-regular over $\mathbb C$ if the span of all subsequences $n\mapsto b_{q^en+t}$, where $e\ge0$ and $0\le t<q^e$, is finite-dimensional [4].

**Theorem D.1.** If $G(z)=\sum_{n\ge0}b_nz^n$ satisfies R, its coefficients are not regular in any fixed integer base. Finite coefficient changes cannot avoid the conclusion.

**Proof.** Suppose the kernel space has dimension $D$. A basis vector $v(n)$ and its section maps give constant matrices $M_j$ and a row $\ell$ such that $v(qn+j)=M_jv(n)$ and $b_n=\ell v(n)$. Consequently,

$$
V(z)=\left(\sum_{j=0}^{q-1}z^jM_j\right)V(z^q),\qquad G(z)=\ell V(z).
$$

Expand $G(z),G(z^q),\ldots,G(z^{q^D})$ to the common vector $V(z^{q^D})$. Their $D+1$ rows in $\mathbb C(z)^D$ are dependent, producing a nontrivial undifferentiated dilation relation, contrary to Corollary C.3. No matrix is inverted.

A canonical-digit model initialized at its first nonzero digit instead adds a fixed polynomial vector to this equation. Adjoining one constant coordinate makes the equation homogeneous, and the same elimination applies. Fixed affine updates are handled similarly. A finite coefficient change adds a polynomial, leaving R unchanged. $\square$

Thus fixed-dimensional constant-matrix updates and fixed linear readouts are excluded. Nonlinear updates, input-dependent matrices, growing dimension, and computations over a fixed finite ring are not covered.

A sequence is *P-recursive* if it eventually satisfies a nontrivial linear recurrence of fixed finite order with polynomial coefficients. Its ordinary generating function is D-finite exactly when the sequence is P-recursive [3]; finite initial exceptions are allowed.

**Conditional Corollary D.2.** If the actual $A$ satisfies R with $C=L$, then $A$ has the unit circle as a natural boundary, $E$ has the circle of radius two as a natural boundary, and $P(n)$ is not P-recursive. The dilation restrictions and Theorem D.1 apply to $(a_n)$.

Indeed, a polynomial-coefficient recurrence for $P(n)$ becomes one for $a_n$ after substitution: a shift-$j$ coefficient acquires the polynomial factor $2^{-j}(n+1)\cdots(n+j)$. It would make $A$ D-finite [3], contradicting Theorem C.1. Nonregularity follows separately from Theorem D.1. The digit exclusion addresses the bounded normalized sequence; factorial growth alone already excludes fixed constant-matrix models for the unnormalized counts.

Even a relation satisfying the necessary highest-order cancellation still needs an independently determined right-hand side. If the actual defect coefficients could be computed without invoking unknown values of $P$, then, with $r=\nu_2(n)$,

$$
a_n=\sum_{j=0}^{r}\frac{2^{j(j+2)}}{n^{2j+2}}m_{n/2^j}
$$

would recover the sequence exactly. Presently this is only a reconstruction identity: defining $m_n$ by differences of unknown $a_n$ and substituting back is circular. Whether the actual $M$ is D-finite, or admits another effectively evaluable transcendental expression, remains unresolved here.

## Appendix E. A short formula with a natural boundary

The example in the main text uses $C=1$. Here we retain an arbitrary nonzero constant.

Fix $C\ne0$, and define

$$
s_n=-C\sum_{j=0}^{\nu_2(n)-1}2^{j(j+1)}n^{-2j-1},\qquad
S(z)=\sum_{n\ge1}s_nz^n.
$$

The empty sum for odd $n$ is zero. Splitting off the first term for even $n$ gives $s_n=-C/n+2s_{n/2}/n^2$, hence exactly

$$
\Theta^2S(z)-2S(z^2)=-\frac{2Cz^2}{(1-z^2)^2}.
$$

Successive existing summands have ratio at most $1/4$, so $|s_n|\le4|C|/(3n)$. Fix $r$ and split the sum below, at, and above level $r$. The upper tail is $O_r(n^{-2r-3})$. At a primitive root of order $q=2^{r+1}$, lower levels are analytic polylogarithmic terms. The resonant term is

$$
-\frac{\kappa_r}{q^{2r+1}}\operatorname{Li}_{2r+1}(z^q),
\qquad \kappa_r=C2^{r(r+1)}.
$$

The leading chain-rule factor in its $2r$-th radial derivative is $q^{2r}$, giving logarithmic coefficient $\kappa_r/q=C2^{r^2-1}$. The differentiated tail is absolutely summable and all lower derivatives have finite limits. Thus R holds and $S$ has a natural boundary.

Nevertheless, $-s_n/C$ is an explicit rational sum of at most $\nu_2(n)$ terms. For positive valuation, a common denominator is $n^{2\nu_2(n)-1}$; numerator and denominator have $O((\log n)^2)$ bits. Ordinary integer arithmetic therefore evaluates it exactly in polynomial time in the binary input length. Odd inputs give zero directly. For general $C$, this is exact evaluation of the rational multiplier, not a finite binary encoding of an arbitrary complex constant.

The model tends to zero, whereas the actual $a_n$ tends to $L>0$. Its rational forcing must not be transferred to the actual defect of Theorem A.4.

For completeness, $-\log(1-z)$, used in Section 4, is also non-algebraic: continuation around $1$ produces infinitely many distinct values, whereas an algebraic function has only finitely many branches.

## Research status and license

This is a research draft for review. AI tools assisted with derivation organization, translation, typesetting, and internal consistency checks. The results stated here have not undergone external peer review or formal verification within the scope of this manuscript. Formalization of earlier work must not be taken to cover this paper automatically. The authors remain responsible for reviewing and revising the final content.

© 2026 Xingchen Liu and Xiangyu Ye. The text and source files are licensed under Creative Commons Attribution 4.0 International (CC BY 4.0).

## References

[1] Alexander Divoux and Shouda Wang. *The maximum number of Hamiltonian cycles in tournaments*. arXiv:2610.23755v1, 2026. Theorem 1.4. https://arxiv.org/abs/2610.23755v1

[2] Sever Angel Popescu. *A simple and self-contained proof for the Lindemann-Weierstrass theorem*. arXiv:2306.14352v2, 2023. Theorem 3.2. https://arxiv.org/abs/2306.14352v2

[3] Richard P. Stanley. *Differentiably Finite Power Series*. European Journal of Combinatorics **1**(2) (1980), 175–188. https://doi.org/10.1016/S0195-6698%2880%2980051-5

[4] Jean-Paul Allouche and Jeffrey Shallit. *The ring of k-regular sequences*. Theoretical Computer Science **98**(2) (1992), 163–197. https://doi.org/10.1016/0304-3975%2892%2990001-V
