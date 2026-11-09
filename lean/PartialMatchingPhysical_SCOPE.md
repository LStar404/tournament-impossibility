# Genuine partial matchings, affine Wick and actual physical residual coefficients

Six candidates after frozen 259. These establish real finite combinatorial
identities; they do not complete global C_j regrouping or asymptotic estimates.

AffineWickWord defines the actual polynomial product of (Xi+C eta_i) over a
word. It proves its derivative by deletion of each occurrence, then derives
its true full-Wick recurrence from polynomial IBP and linearity. The coefficient
ring is an arbitrary commutative semiring, so PowerSeries S is allowed without
pretending it is a field. No multiplicativity of Wick is assumed.

PartialMatchingAffine defines partial pairings as Sigma(s:Finset V), Pairing s,
where Pairing s is the existing actual fixed-point-free involution. Its weight
is the product of means on the complement times the existing unordered Sym2
edge weight on s. It proves the weighted sum equals Wick of the actual affine
finite product by finite subset expansion, scalar linearity and the real
assignment-fibre occurrence equivalence. Numerical labels may repeat and pairs
with equal labels are retained; unordered edges are counted exactly once.

PhysicalPartialMatching proves true covariance symmetry via expand_2 and the
previous actual covariance theorem, then identifies affine Wick with the old
physical moment by the proved common recurrence and length induction. The final
endpoint equates each actual physical word moment with the genuine partial
pairing sum on its occurrence positions.

PartialMatchingInvolution constructs the actual permutation fixing the
complement and pairing the subset, proves involutivity and its exact moved set,
and constructs the inverse restriction. It proves both inverse identities and
a full equivalence with involutions permitting fixed points. Singletons are
therefore genuinely fixed points, not an informal interpretation.

StructuralPartialMatchingCounts derives even paired cardinality from the actual
pairing theorem; defines e=paired-cardinality/2, h=complement cardinality and
proves total occurrence count D=2e+h. For positions Sigma(v:Fin b),Fin(d_v) with
d_v>=3 it proves b<=2j, D<=6j and e+h=j+b for j=e+h-b, with subtraction justified.
For b>0 it proves j+1<=e+h. This is a genuine counting bound. The separate
identification e=card(Sym2 edges) and vanishing of weight coefficients below e+h
are still to be proved; the arithmetic bound is not presented as that order
statement or a weighted estimate.

ResidualPartialMatchingExpansion connects the actual residual coefficients from
253/248 to the explicit finite degree-assignment and actual partial-matching
sum. This closes actual normalized insertion → physical moment → real partial
matching, with fixed points, repeated numerical labels and internal pairs/loops
preserved. Finset antidiagonal instance independence is proved by membership
rather than assuming concrete Fin-sum DecidableEq instances are definitionally
equal. Empty occurrence/index sets remain included.

Remaining: full polynomial-valued logarithmic exponential and global ordered
structural-label expansion; exact C_j finite regrouping/multiplicities; edge
cardinality and coefficient-order theorem; uniform activity bounds and
truncated sums; independent true permanent tails; falling-factorial restoration;
fixed-depth projection/commonness and complete R. Neither the finite identities
nor earlier degree-0..2 cancellation establish any higher-tail estimate. No
indefinite zQ probability measure or core-tail substitution is used.
