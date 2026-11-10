import TournamentHamiltonian.NormalizedConvolution

namespace TournamentHamiltonian
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

noncomputable def shortPrincipalMass {n : ℕ} (T : Tournament n) (K : ℕ) : ℝ :=
  ∑ U : Finset (Fin n), if U.card<K then (2/(n : ℝ))^U.card*(principalWeightMatrix T U).det else 0

noncomputable def shortPrincipalErrorMoment {n : ℕ} (T : Tournament n) (K : ℕ) : ℝ :=
  ∑ U : Finset (Fin n), if U.card<K then
    (2/(n : ℝ))^U.card*(principalWeightMatrix T U).det*((U.card : ℝ)+2)^2 else 0

end TournamentHamiltonian

namespace TournamentHamiltonian
end TournamentHamiltonian
