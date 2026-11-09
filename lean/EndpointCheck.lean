import RepeatedLabelPairing
import FullFourthMoment
import SymmetricPairingTransport
import PairingRepresentativeBridge
import OccurrenceWickPolynomial
import SubsetPairingScaling
import FrozenPartialPairingPolynomial
import ShiftedProductSubsetExpansion
import SquarefreePairingContraction
import FrozenPairingEndpoints
import RectangularPairing
import FinitePairingTransport
import FinitePairingPermanent
import SubsetPairingPermanent
import BipartitePairingPermanent
import WickPairingZero
import WickBipartiteEquiv
import WickPairingPermanent
import ComplexSkewSourceIdentity
import BlockGaussianDeterminant
import BlockGaussianSourceElimination
import RawBlockSourceIdentity
import RawGaussianSourceScalar
import ActualBlockGaussianSource
import GaussianParameterBranch
import GaussianSourceExponent
import ComplexResolventAnalytic
import ComplexCauchyErrorTransfer
import GaussianScalarFactor
import ActualGaussianSourceExponent
import GaussianDeterminantBranch
import GaussianSourceProduct
import GaussianSourceAnalytic
import GaussianSourceDerivative
import TransitiveKernelInverse
import MatrixEuclideanEntryBound
import TransitiveKernelInverseBounds
import DiamondFreeKernelInverseTransfer
import DiamondFreeKernelOperatorBound
import ComplexKernelDiskLower
import DiamondFreeDiskResolvent
import ActualComplexScoreSource
import ComplexBinomialRate
import ComplexOperatorResolventBound
import DiamondFreeKernelLimit
import DiamondFreeKernelUniform
import DiamondFreeComplexResolvent
import DiamondFreeKernelDeterminant
import ActualSmallDiamondSixth
import SmallDiamondGraphEndpoint
import DiamondFreePathAverage
import GlobalSixthDeficitEndpoint
import ActualPathConvolution
import OrdinalSixthMatrixEndpoint
import OrdinalSixthPolynomialEndpoint
import SourceResolventEndpoint
import OnesEnergyEndpoint
import ReferenceMomentEndpoint
import VectorMajorizationEndpoint
import MajorizationCone
import SelectedWeight
import BalancedSignCounts
import SelectedSignPairs
import SelectedRowOptimization
import VectorWeakMajorization
import ZeroDiamondRepair
import FiniteGraphEditTransport
import DiamondFreeRepresentation
import TournamentColorEnumeration
import ColorCutNormalization
import ColorTargetModels
import ColorGraphRepair
import ColorTransportExact
import DiamondGap
import ColorTransport
import ColorEnergy
import OrderedCancellation
import QRegularApplications
import PathCountGrowth
import QRegularRationalLimit

/-! Independent endpoint checks. These examples pin the public statements to
actual tournament quantities and to the full q-kernel, not a substituted
matrix-representation predicate or a presumed obstruction. -/
open Filter Topology
namespace NonAlgebraicity.EndpointCheck

example (q : ℕ) (a : ℕ → ℂ) :
    IsQRegular q a ↔ FiniteDimensional ℂ
      (Submodule.span ℂ {f : ℕ → ℂ | ∃ e r : ℕ,
        r < q ^ e ∧ f = fun n => a (q ^ e * n + r)}) := Iff.rfl

example (q : ℕ) (hq : 2 ≤ q) (a : ℕ → ℚ) (L : ℂ)
    (hlim : Tendsto (fun n => (a n : ℂ)) atTop (𝓝 L))
    (hL : Transcendental ℚ L) :
    ¬ IsQRegular q (fun n => (a n : ℂ)) :=
  not_qRegular_of_transcendental_limit q hq a L hlim hL

example (q : ℕ) (hq : 2 ≤ q) (a : ℕ → ℚ) (k : ℕ) (L : ℂ)
    (hlim : Tendsto (fun n => ((a n / (n : ℚ)^k : ℚ) : ℂ)) atTop (𝓝 L))
    (hL : Transcendental ℚ L) :
    ¬ IsQRegular q (fun n => (a n : ℂ)) :=
  not_qRegular_of_scaled_transcendental_limit q hq a k L hlim hL

example (q : ℕ) (hq : 2 ≤ q)
    (asymptotic : ExtremalAsymptotic) (lw : FourExponentialIndependence) :
    ¬ IsQRegular q (fun n => (normalizedCoefficient n : ℂ)) :=
  normalizedCoefficient_not_qRegular q hq asymptotic lw

example (q : ℕ) (hq : 2 ≤ q)
    (asymptotic : ExtremalAsymptotic) (lw : FourExponentialIndependence) :
    ¬ IsQRegular q (fun n => (halfScaleRemainder n : ℂ)) :=
  halfScaleRemainder_not_qRegular q hq asymptotic lw

example (asymptotic : ExtremalAsymptotic) :
    ¬ ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ n, (maximalPathCount n : ℝ) ≤ C * D^n :=
  maximalPathCount_not_exponentially_bounded asymptotic

example (asymptotic : ExtremalAsymptotic)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (q : ℕ) (hq : 2 ≤ q) (A : Fin q → E →L[ℂ] E)
    (V : ℕ → E) (f : E →L[ℂ] ℂ)
    (hV : ∀ n, n ≠ 0 → V n = A ⟨n % q, Nat.mod_lt n (by omega)⟩ (V (n / q)))
    (hout : ∀ n, (maximalPathCount n : ℂ) = f (V n)) : False :=
  maximalPathCount_no_linear_digit_representation asymptotic q hq A V f hV hout

/-- Full Appendix A.5, directly stated using the entire q-kernel span.
No graph asymptotic, transcendence input, or rationality premise is required. -/
example (q : ℕ) (hq : 2 ≤ q) (a : ℕ → ℚ) (k : ℕ) (L : ℂ)
    (ha : FiniteDimensional ℂ
      (Submodule.span ℂ {f : ℕ → ℂ | ∃ e r : ℕ,
        r < q ^ e ∧ f = fun n => (a (q ^ e * n + r) : ℂ)}))
    (hlim : Tendsto (fun n => ((a n / (n : ℚ)^k : ℚ) : ℂ)) atTop (𝓝 L)) :
    ∃ r : ℚ, (r : ℂ) = L :=
  qRegular_scaled_limit_rational q hq a k L ha hlim

example (q : ℕ) (hq : 2 ≤ q) (a : ℕ → ℚ) (L : ℂ)
    (ha : IsQRegular q (fun n => (a n : ℂ)))
    (hlim : Tendsto (fun n => (a n : ℂ)) atTop (𝓝 L)) :
    ∃ r : ℚ, (r : ℂ) = L :=
  qRegular_limit_rational q hq a L ha hlim

end NonAlgebraicity.EndpointCheck

#print axioms NonAlgebraicity.qRegular_power_representation
#print axioms NonAlgebraicity.matrix_output_series_relation
#print axioms NonAlgebraicity.not_qRegular_of_transcendental_limit
#print axioms NonAlgebraicity.not_qRegular_of_scaled_transcendental_limit
#print axioms NonAlgebraicity.normalizedCoefficient_not_qRegular
#print axioms NonAlgebraicity.halfScaleRemainder_not_qRegular
#print axioms NonAlgebraicity.digit_recursion_exponential_bound
#print axioms NonAlgebraicity.maximalPathCount_not_exponentially_bounded
#print axioms NonAlgebraicity.maximalPathCount_no_linear_digit_representation

#print axioms NonAlgebraicity.qRegular_scaled_limit_rational
#print axioms NonAlgebraicity.qRegular_limit_rational

/-! Local packet endpoint: finite low-position packets of length 2^q,
remaining recursion depth r-q. No assertion about tournament kernels or R. -/
example {R : Type*} [Ring R] (F : OrderedCancellation.Filtration R)
    (p m : List R) (hp : ∀ x ∈ p, F.mem 1 (x - 1))
    (hm : ∀ x ∈ m, F.mem 1 (x - 1)) (hz : F.mem 1 0)
    (r q : ℕ) (hq : q ≤ r) (lp : p.length = 2 ^ q) (lm : m.length = 2 ^ q) :
    F.mem (r - q + 1)
      ((OrderedCancellation.expandPackets p m (OrderedCancellation.words (r - q)).1).prod -
       (OrderedCancellation.expandPackets p m (OrderedCancellation.words (r - q)).2).prod) :=
  OrderedCancellation.packet_difference_order F p m hp hm hz r q hq lp lm

#print axioms OrderedCancellation.difference_order
#print axioms OrderedCancellation.evaluate_words
#print axioms OrderedCancellation.blocks_add
#print axioms OrderedCancellation.packet_length
#print axioms OrderedCancellation.packet_difference_order

/-! Finite prefix-energy endpoint only. No graph realization, attainable swap
sequence, or graph-edit upper bound follows from this example alone. -/
example (n : ℕ) (P c : ℕ → ℝ) (h0 : P 0 = 0) (hfinal : P n = 1)
    (hstep : ∀ i < n, P (i + 1) = P i + c i)
    (hcolor : ∀ i < n, (c i)^2 = 1) :
    ColorEnergy.energy n 1 P c = 4 * ∑ i ∈ Finset.range n, P i * (P i - 1) :=
  ColorEnergy.odd_energy n P c h0 hfinal hstep hcolor

#print axioms ColorEnergy.energy_telescope
#print axioms ColorEnergy.energy_identity
#print axioms ColorEnergy.even_energy
#print axioms ColorEnergy.odd_energy
#print axioms ColorEnergy.summed_repair_budget
#print axioms ColorEnergy.odd_prefix_transport_budget

/-! Actual adjacent unlike-color swap reachability and only a lower bound on
minimum distance. No equality or graph-edit upper bound is asserted. -/
example (u v : List Bool) (hlen : u.length = v.length)
    (hc : ColorTransport.charge u = ColorTransport.charge v) :
    ∃ n, ColorTransport.Swaps n u v ∧
      (∀ m, ColorTransport.Swaps m u v → n ≤ m) ∧
      ColorTransport.area u v ≤ (n : ℤ) :=
  ColorTransport.minimum_swaps_exists hlen hc

#print axioms ColorTransport.equal_total_reachable
#print axioms ColorTransport.reaches_paired
#print axioms ColorTransport.reaches_alternatingOdd
#print axioms ColorTransport.area_le_swaps
#print axioms ColorTransport.minimum_swaps_exists

/-! Finite tournament combinatorics only: the count is of unordered four-sets.
This endpoint supplies no asymptotic recovery or Condition R implication. -/
example {V : Type*} [DecidableEq V] [Fintype V]
    (T : DiamondGap.Tournament V) :
    T.diamonds.card = 0 ∨ Fintype.card V ≤ 4 * T.diamonds.card :=
  T.zero_or_gap

#print axioms DiamondGap.Tournament.quad_iff_pattern
#print axioms DiamondGap.Tournament.diamond_covers
#print axioms DiamondGap.Tournament.positive_gap
#print axioms DiamondGap.Tournament.zero_or_gap

/-! Attained color-word repair bounds; matrix identification and conversion
of a word swap into a graph edge reversal remain separate obligations. -/
example (w : List Bool) (k : ℕ) (hl : w.length = 2*k+1)
    (hc : ColorTransport.charge w = 1) :
    ∃ n, ColorTransport.Swaps n w (ColorTransport.alternatingOdd k) ∧
      (n : ℝ) ≤ ColorTransport.wordEnergy w / 8 :=
  ColorTransport.odd_energy_repair w k hl hc

example (w : List Bool) (k : ℕ) (hl : w.length = 2*k)
    (hc : ColorTransport.charge w = 0) :
    ∃ n, ColorTransport.Swaps n w
      (ColorTransport.paired (ColorTransport.repairOrient w k)) ∧
      (n : ℝ) ≤ (ColorTransport.wordEnergy w - w.length) / 16 :=
  ColorTransport.even_energy_repair w k hl hc

#print axioms ColorTransport.area_descent
#print axioms ColorTransport.exact_swaps
#print axioms ColorTransport.exact_minimum
#print axioms ColorTransport.prefix_area_identity
#print axioms ColorTransport.prefix_exact_minimum
#print axioms ColorTransport.odd_energy_repair
#print axioms ColorTransport.even_energy_repair

/-! Actual finite differing-edge cardinality for normalized color-word tournaments.
No general tournament normalization, named-target identification, or R follows. -/
example (w : List Bool) (k : ℕ) (hl : w.length = 2*k+1)
    (hc : ColorTransport.charge w = 1) :
    ∃ e : Equiv ℕ ℕ, (∀ i, e i < w.length ↔ i < w.length) ∧
      ((ColorTransport.mismatchEdges w.length (ColorTransport.colorGraph w)
        (ColorTransport.colorGraph (ColorTransport.alternatingOdd k)) e).card : ℝ) ≤
        ColorTransport.graphEnergy w.length (ColorTransport.colorGraph w) / 8 :=
  ColorTransport.odd_edit_card_bound w k hl hc

example (w : List Bool) (k : ℕ) (hl : w.length = 2*k)
    (hc : ColorTransport.charge w = 0) :
    ∃ e : Equiv ℕ ℕ, (∀ i, e i < w.length ↔ i < w.length) ∧
      ((ColorTransport.mismatchEdges w.length (ColorTransport.colorGraph w)
        (ColorTransport.colorGraph (ColorTransport.paired (ColorTransport.repairOrient w k)))
        e).card : ℝ) ≤
        (ColorTransport.graphEnergy w.length (ColorTransport.colorGraph w) - w.length) / 16 :=
  ColorTransport.even_edit_card_bound w k hl hc

#print axioms ColorTransport.colorGraph_row_sum
#print axioms ColorTransport.graphEnergy_eq_wordEnergy
#print axioms ColorTransport.adjacent_matrix_flip_changes
#print axioms ColorTransport.graph_edits_certificate
#print axioms ColorTransport.mismatch_card_le
#print axioms ColorTransport.odd_edit_card_bound
#print axioms ColorTransport.even_edit_card_bound

/-! Arbitrary color words, not arbitrary tournaments. No charge hypothesis
is present here; no diamond-free representation theorem is assumed or proved. -/
example (w : List Bool) (k : ℕ) (hl : w.length = 2*k+1) :
    ∃ e : Equiv ℕ ℕ, (∀ i, e i < w.length ↔ i < w.length) ∧
      ((ColorTransport.mismatchEdges w.length (ColorTransport.colorGraph w)
        (ColorTransport.colorGraph (ColorTransport.alternatingOdd k)) e).card : ℝ) ≤
        ColorTransport.graphEnergy w.length (ColorTransport.colorGraph w) / 8 :=
  ColorTransport.arbitrary_odd_word_repair w k hl

example (w : List Bool) (k : ℕ) (hl : w.length = 2*k) :
    ∃ (orient : List Bool) (e : Equiv ℕ ℕ), orient.length = k ∧
      (∀ i, e i < w.length ↔ i < w.length) ∧
      ((ColorTransport.mismatchEdges w.length (ColorTransport.colorGraph w)
        (ColorTransport.colorGraph (ColorTransport.paired orient)) e).card : ℝ) ≤
        (ColorTransport.graphEnergy w.length (ColorTransport.colorGraph w) - w.length) / 16 :=
  ColorTransport.arbitrary_even_word_repair w k hl

example (w : List Bool) (p q : Fin w.length × Bool) :
    ColorTransport.colorGraph (ColorTransport.paired w)
      (ColorTransport.pairLabelEquiv w.length p) (ColorTransport.pairLabelEquiv w.length q) =
    ColorTransport.doublingMatrix (ColorTransport.colorGraph w) p.1 p.2 q.1 q.2 :=
  ColorTransport.paired_doubling_isomorphism w p q

example (k : ℕ) (i j : Fin (2*k+1)) :
    ColorTransport.colorGraph (ColorTransport.alternatingOdd k)
      (ColorTransport.carouselLabelEquiv k i) (ColorTransport.carouselLabelEquiv k j) =
    ColorTransport.carouselMatrix k i j :=
  ColorTransport.alternating_carousel_isomorphism k i j

#print axioms ColorTransport.arbitrary_odd_word_repair
#print axioms ColorTransport.arbitrary_even_word_repair
#print axioms ColorTransport.normalized_graph_exists
#print axioms ColorTransport.graphEnergy_isomorphism
#print axioms ColorTransport.paired_doubling_isomorphism
#print axioms ColorTransport.alternating_carousel_isomorphism
#print axioms ColorTransport.carousel_forward_distance
#print axioms ColorTransport.carouselIndex_eq_mod

/-! Actual zero-diamond representation of the ORIGINAL tournament matrix.
No arbitrary-tournament representation, positive-diamond repair, or R claim. -/
example {V : Type*} [Fintype V] [DecidableEq V] (T : DiamondGap.Tournament V)
    (hT : T.diamonds.card = 0) :
    ∃ (w : List Bool) (e : Fin (Fintype.card V) ≃ V),
      w.length = Fintype.card V ∧
      ∀ i j, (T.S (e i) (e j) : ℝ) = ColorTransport.colorGraph w i j :=
  DiamondFreeRepresentation.zero_diamonds_color_representation T hT

#print axioms ColorTransport.transitive_tournament_enumeration
#print axioms ColorTransport.representation_of_transitive_switch
#print axioms DiamondFreeRepresentation.switched_quad_sq
#print axioms DiamondFreeRepresentation.switched_diamondFree
#print axioms DiamondFreeRepresentation.source_transitive
#print axioms DiamondFreeRepresentation.exists_transitive_switch
#print axioms DiamondFreeRepresentation.diamondFree_color_representation
#print axioms DiamondFreeRepresentation.zero_diamonds_color_representation

/-! Original-tournament D=0 edit endpoints: actual finite mismatch count and
original squared row-sum energy, with no residual word/target premise. -/
example {V : Type*} [Fintype V] [DecidableEq V] (T : DiamondGap.Tournament V)
    (hD : T.diamonds.card = 0) (k : ℕ) (hN : Fintype.card V = 2*k+1) :
    ∃ e : Fin (2*k+1) ≃ V,
      ((ColorTransport.finiteMismatch (2*k+1) (fun i j => (T.S (e i) (e j) : ℝ))
        (fun i j => ColorTransport.carouselMatrix k i j)).card : ℝ) ≤
        ZeroDiamondRepair.tournamentEnergy T / 8 :=
  ZeroDiamondRepair.zero_diamond_odd_repair T hD k hN

example {V : Type*} [Fintype V] [DecidableEq V] (T : DiamondGap.Tournament V)
    (hD : T.diamonds.card = 0) (k : ℕ) (hN : Fintype.card V = 2*k) :
    ∃ (baseWord : List Bool) (e : Fin (2*k) ≃ V), baseWord.length = k ∧
      ((ColorTransport.finiteMismatch (2*k) (fun i j => (T.S (e i) (e j) : ℝ))
        (ZeroDiamondRepair.flatDoubling k (ColorTransport.colorGraph baseWord))).card : ℝ) ≤
        (ZeroDiamondRepair.tournamentEnergy T - Fintype.card V) / 16 :=
  ZeroDiamondRepair.zero_diamond_even_repair T hD k hN

#print axioms ColorTransport.finiteMismatch_reindex_card
#print axioms ColorTransport.finiteMismatch_nat_restriction
#print axioms ZeroDiamondRepair.represented_energy
#print axioms ZeroDiamondRepair.flatDoubling_eq_paired
#print axioms ZeroDiamondRepair.zero_diamond_odd_repair
#print axioms ZeroDiamondRepair.zero_diamond_even_repair

/-! Foundational finite inequalities only, not optimized tournament majorization.
The descending vector convention includes the endpoint coordinate n. -/
example (n : ℕ) (x y : ℕ → ℝ)
    (h : ∀ k ≤ n, (∑ i ∈ Finset.range k, x i) ≤ ∑ i ∈ Finset.range k, y i)
    (hx : VectorWeakMajorization.DescendingNonnegative n x)
    (hy : VectorWeakMajorization.DescendingNonnegative n y) :
    (∑ i ∈ Finset.range n, (x i)^2) ≤ ∑ i ∈ Finset.range n, (y i)^2 :=
  VectorWeakMajorization.sum_sq_le n x y h hx hy

example (n : ℕ) (B : VectorWeakMajorization.Tournament n) (x y : Fin n → ℝ) :
    2 * (∑ i, y i * (∑ j, B.entry i j * x j)) ≤
      ∑ i, ∑ j, |y i * x j - y j * x i| :=
  B.signed_sum_bound x y

#print axioms VectorWeakMajorization.abel
#print axioms VectorWeakMajorization.weighted_le
#print axioms VectorWeakMajorization.sum_sq_le
#print axioms VectorWeakMajorization.Tournament.signed_sum_identity
#print axioms VectorWeakMajorization.Tournament.signed_sum_bound

/-! Explicit K and optimized finite envelope, not an actual Bx majorization
endpoint. The matrix-to-selected-envelope bridge remains unproved here. -/
example (n : ℕ) (x : ℕ → ℝ)
    (hx : VectorWeakMajorization.DescendingNonnegative n x) (hz : x n = 0) :
    VectorWeakMajorization.DescendingNonnegative n (MajorizationCone.K n x) :=
  MajorizationCone.K_preserves_cone n x hx hz

example (n : ℕ) (x y : ℕ → ℝ)
    (h : VectorWeakMajorization.WeakMajorized n x y) :
    VectorWeakMajorization.WeakMajorized n (MajorizationCone.K n x) (MajorizationCone.K n y) :=
  MajorizationCone.K_preserves_prefix_order n x y h

example (n k : ℕ) (hk : k ≤ n) (f : ℕ → ℕ)
    (hf : ∀ i, i+1 < k → f i < f (i+1)) (hr : ∀ i < k, f i < n)
    (x b : ℕ → ℝ) (s : ℕ → Bool)
    (hx : ∀ a c, a ≤ c → c < n → x c ≤ x a)
    (hb : VectorWeakMajorization.DescendingNonnegative k b)
    (hd : ∀ i j, i<j → j<k → b j ≤ b i)
    (hselected : ∀ j<k, b j = x (f j)) :
    (k : ℝ) * ((∑ i ∈ Finset.range n, x i) - (∑ j ∈ Finset.range k, b j)) +
      SelectedSignPairs.pairCost s b k ≤ MajorizationCone.P n k x :=
  SelectedRowOptimization.envelope_le_P n k hk f hf hr x b s hx hb hd hselected

#print axioms MajorizationCone.K_preserves_cone
#print axioms MajorizationCone.K_preserves_prefix_order
#print axioms MajorizationCone.P_tail_formula
#print axioms SelectedWeight.selected_weight_ge
#print axioms BalancedSignCounts.baseline_le_pairs
#print axioms BalancedSignCounts.penalty_le
#print axioms SelectedSignPairs.pairCost_identity
#print axioms SelectedSignPairs.pairCost_le
#print axioms SelectedRowOptimization.envelope_le_P

/-! Complete actual finite tournament vector-prefix bound. This closes the
matrix/envelope/sorting interfaces, but not reference K-orbit or moment claims. -/
example (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hskew : ∀ i j, A i j = - A j i)
    (hunit : ∀ i j, i ≠ j → A i j = 1 ∨ A i j = -1)
    (x : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    (∑ i ∈ Finset.range k, TournamentSwitching.sortedPad (fun a => ∑ b, A a b * x b) i) ≤
      (k : ℝ) * (∑ i ∈ Finset.range n, TournamentSwitching.sortedPad x i) -
      ∑ j ∈ Finset.range k, (MajorizationCone.penalty j : ℝ) *
        TournamentSwitching.sortedPad x (n-k+j) :=
  actual_matrix_prefix_endpoint n A hskew hunit x k hk

#print axioms SelectedTournamentMajorization.tournament_vector_majorization
#print axioms SelectedTournamentMajorization.tournament_prefix_bound
#print axioms actual_matrix_prefix_endpoint

/-! Raw actual matrices, genuine matrix powers, all NONNEGATIVE integer exponents.
Not a claim about negative powers, an all-ones orbit, small defects, or R. -/
example (n r : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A i j = -A j i)
    (hunit : ∀ i j, i ≠ j → A i j = 1 ∨ A i j = -1) :
    (∑ i : Fin n, ∑ j : Fin n, ((A^r) i j)^2) ≤
      ∑ i : Fin n, ∑ j : Fin n, ((TransitiveOrbit.T n ^ r) i j)^2 :=
  actual_all_integer_moments n r A hskew hunit

#print axioms SignedReferenceConjugacy.concrete_square_conjugacy
#print axioms ReferenceMomentComparison.reference_column_norm
#print axioms ReferenceMomentComparison.frobenius_all_powers
#print axioms actual_all_integer_moments

/-! Raw entries and explicit natural q, with convergence proved, not assumed. -/
example (n : ℕ) (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A i j = -A j i)
    (hunit : ∀ i j, i ≠ j → A i j = 1 ∨ A i j = -1) :
    (∑' r : ℕ, (1/(n : ℝ)^2)^r*(∑ i, ((A^(r+1)).mulVec (fun _ => (1:ℝ)) i)^2)) ≤
      ∑' r : ℕ, (1/(n : ℝ)^2)^r*(∑ i, ((TransitiveOrbit.T n ^ (r+1)).mulVec (fun _ => (1:ℝ)) i)^2) :=
  actual_source_series_natural n hn A hskew hunit
#print axioms actual_source_power_energy
#print axioms actual_source_series_natural
#print axioms TournamentEnergyRowDomain.source_summable
#print axioms TournamentEnergyRowDomain.source_series_le

/-! Genuine inverse and raw-matrix resolvent comparison on the sufficient row domain. -/
example (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A i j = -A j i)
    (hunit : ∀ i j, i ≠ j → A i j = 1 ∨ A i j = -1)
    (q : ℝ) (hq : 0 ≤ q) (hsmall : q*(((n-1 : ℕ) : ℝ)^2) < 1) :
    dotProduct (A.mulVec (fun _ => (1:ℝ)))
      ((1+q • (A^2))⁻¹.mulVec (A.mulVec (fun _ => (1:ℝ)))) ≤
    dotProduct ((TransitiveOrbit.T n).mulVec (fun _ => (1:ℝ)))
      ((1+q • ((TransitiveOrbit.T n)^2))⁻¹.mulVec
        ((TransitiveOrbit.T n).mulVec (fun _ => (1:ℝ)))) :=
  actual_source_resolvent_comparison n A hskew hunit q hq hsmall
#print axioms actual_source_resolvent_comparison
#print axioms TournamentSourceResolvent.inverse_left_right
#print axioms TournamentSourceResolvent.resolvent_eq_series
#print axioms TournamentSourceResolvent.source_resolvent_natural

/-! Polynomial-only sixth coefficient: actual matrix identification is NOT asserted. -/
#print axioms finite_sixth_polynomial_endpoint
#print axioms OrdinalSixthPolynomial.small_deficit_transfer

/-! Actual skew block matrices, not a postulated coefficient formula. -/
#print axioms actual_ordinal_sixth_expanded
#print axioms OrdinalSixthMatrixBridge.actual_sixth_coefficient
#print axioms TwoBlockSixthMoment.third_join

/-! Actual path count, exact S1 normalization. No zero-diamond averaging claim. -/
#print axioms NonAlgebraicity.hamiltonianPathCount_convolution
#print axioms TournamentHamiltonian.actual_path_convolution_even_subsets
#print axioms NonAlgebraicity.pathCount_asPathTournament

/-! Actual global-reference sixth deficit; diamond/count hypotheses remain explicit. -/
#print axioms global_sixth_deficit_expanded
#print axioms OrdinalGlobalSixthDeficit.conditional_small
#print axioms TournamentSourceEnergy.first_eq_reference_sub
#print axioms TransitiveFirstEnergy.first_closed_form

/-! Literal zero diamond count, original path function, exact finite normalization. -/
example {n : ℕ} (o : NonAlgebraicity.Orientation (n+1))
    (h : (TournamentHamiltonian.asDiamondTournament (NonAlgebraicity.asPathTournament o)).diamonds.card = 0) :
    ((2 : ℝ)^n * (NonAlgebraicity.hamiltonianPathCount o : ℝ)) / ((n+1).factorial : ℝ) =
      (((TournamentHamiltonian.pathWeightMatrix (NonAlgebraicity.asPathTournament o))+1).permanent +
        ((TournamentHamiltonian.pathWeightMatrix (NonAlgebraicity.asPathTournament o))-1).permanent) /
        (2*((n+1).factorial : ℝ)) :=
  NonAlgebraicity.zero_diamonds_hamiltonianPathCount_two_permanents o h
#print axioms NonAlgebraicity.zero_diamonds_hamiltonianPathCount_two_permanents
#print axioms TournamentHamiltonian.diamondFree_sign_principal_det

/-! Actual graph count and actual SCCs after a proved source switch. -/
#print axioms actual_small_diamond_component_bound
#print axioms DiamondTriangleIncidence.diamonds_le_triangles
#print axioms TriangleCountBridge.ordered_eq_three_unordered
#print axioms TournamentComponentBlocks.induced_strong
#print axioms PivotMomentInvariant.sixth_eq

#print axioms ActualSmallDiamondSixth.actual_small
#print axioms TournamentOrdinalReconstruction.cycleCount_sum

#print axioms DiamondFreeKernelDeterminant.zero_diamonds_kernel_det
#print axioms DiamondFreeKernelDeterminant.zero_diamonds_normalized_det

#print axioms DiamondFreeKernelLimit.actual_imaginary_inverse
#print axioms DiamondFreeKernelUniform.actual_imaginary_uniformlyOn_compact
#print axioms DiamondFreeKernelUniform.inverse_uniformlyOn_compact
#print axioms DiamondFreeComplexResolvent.eventually_inverse

#print axioms ComplexBinomialRate.actual_imaginary_error
#print axioms ComplexOperatorResolventBound.normalized_source_bound

#print axioms TransitiveKernelInverse.inverse_formula
#print axioms MatrixEuclideanEntryBound.scalar_identity_add_error
#print axioms TransitiveKernelInverseBounds.inverse_operator
#print axioms DiamondFreeKernelInverseTransfer.inverse_entry_representation
#print axioms DiamondFreeKernelOperatorBound.actual_operator_bound
#print axioms ComplexKernelDiskLower.eventually_thresholds
#print axioms DiamondFreeDiskResolvent.eventually_uniform_source
#print axioms ActualComplexScoreSource.inner_eq_bilinear
#print axioms ActualComplexScoreSource.norm_score_sq
#print axioms ActualComplexScoreSource.eventually_uniform_actual_source

#print axioms GaussianParameterBranch.root_identity
#print axioms GaussianParameterBranch.parameter_error
#print axioms GaussianParameterBranch.prefactor_error
#print axioms GaussianParameterBranch.differentiableOn_parameter
#print axioms GaussianParameterBranch.differentiableOn_prefactor
#print axioms GaussianSourceExponent.denominator_bound
#print axioms GaussianSourceExponent.exponent_error
#print axioms GaussianSourceExponent.exp_exponent_error
#print axioms ComplexResolventAnalytic.eventually_analytic_disk
#print axioms ComplexCauchyErrorTransfer.derivative_error_full_gap
#print axioms ComplexCauchyErrorTransfer.derivative_difference_half_gap
#print axioms GaussianScalarFactor.gaussian_error
#print axioms GaussianScalarFactor.eventually_uniform_gaussian_error
#print axioms ActualGaussianSourceExponent.eventually_uniform_error
#print axioms ActualGaussianSourceExponent.exists_uniform_constant
#print axioms GaussianDeterminantBranch.gaussian_branch_square
#print axioms GaussianSourceProduct.eventually_uniform_error
#print axioms GaussianSourceProduct.exists_uniform_constant
#print axioms GaussianSourceAnalytic.eventually_differentiable_disk
#print axioms GaussianSourceDerivative.eventually_uniform_derivative
#print axioms GaussianSourceDerivative.exists_uniform_derivative_constant

#print axioms ComplexSkewSourceIdentity.bilinear_source
#print axioms ComplexSkewSourceIdentity.ones_source

#print axioms BlockGaussianDeterminant.determinant
#print axioms BlockGaussianDeterminant.inverse_left_right

#print axioms BlockGaussianSourceElimination.eliminate_block

#print axioms RawBlockSourceIdentity.source_eq_reduced

#print axioms RawGaussianSourceScalar.reducedSource_eq_exponent
#print axioms RawGaussianSourceScalar.reducedSource_eq_actualExponent

#print axioms ActualBlockGaussianSource.rawSource_eq_actualExponent
#print axioms ActualBlockGaussianSource.branch_square
#print axioms ActualBlockGaussianSource.factor_eq_product

#print axioms BipartitePairingPermanent.pairingSum_eq_permanent

#print axioms WickPairingZero.nonbipartite_weight_eq_zero
#print axioms WickPairingZero.sum_eq_bipartite_filter

#print axioms WickBipartiteEquiv.pairingEquiv

#print axioms WickPairingPermanent.all_pairings_eq_permanent

#print axioms RectangularPairing.unequal_sum_zero

#print axioms FinitePairingTransport.sum_transport

#print axioms FinitePairingPermanent.unequal_sum_zero
#print axioms FinitePairingPermanent.equal_sum_permanent

#print axioms SubsetPairingPermanent.unequal_subsets_zero
#print axioms SubsetPairingPermanent.equal_subsets_permanent

#print axioms SubsetPairingScaling.smul

#print axioms FrozenPartialPairingPolynomial.global_smul
#print axioms FrozenPartialPairingPolynomial.eval_frozenPolynomial

#print axioms ShiftedProductSubsetExpansion.polynomial_expansion

#print axioms SquarefreePairingContraction.contraction_shifted_product
#print axioms SquarefreePairingContraction.contraction_scaled_product

#print axioms FrozenPairingEndpoints.F0
#print axioms FrozenPairingEndpoints.degree_le

#print axioms RepeatedLabelPairing.repeated_four
#print axioms RepeatedLabelPairing.color_permutation_invariant

#print axioms FullFourthMoment.fourth
#print axioms FullFourthMoment.repeated_xxyy

#print axioms SymmetricPairingTransport.moment_transport

#print axioms PairingRepresentativeBridge.occurrence_moment_eq
#print axioms PairingRepresentativeBridge.arbitrary_reordering

#print axioms OccurrenceWickPolynomial.wick_monomial
#print axioms OccurrenceWickPolynomial.monomialMoment_enumeration
