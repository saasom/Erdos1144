import Erdos.Problem1144.HarperCandidateEnergyFatou
import Erdos.Problem1144.HarperCandidateFiniteSpectralMoment

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos.Problem1144

/-- Uniform fractional moments of the actual damped complete log process.
The proof combines the proved finite Euler frequency-band estimate with
actual prime-Euler/Fourier convergence, full zeta factorization, Parseval,
and two applications of Fatou. There is no weighted pathwise premise. -/
theorem candidate_exists_dampedCompleteEnergy_uniform_eighth_moment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Ioc (0 : ℝ) (1 / 8),
      Integrable (fun ω => candidateDampedCompleteEnergy σ ω ^ (1 / 8 : ℝ)) mu ∧
      (∫ ω, candidateDampedCompleteEnergy σ ω ^ (1 / 8 : ℝ) ∂mu) ≤ C := by
  obtain ⟨C, hC, hb⟩ := candidate_exists_finiteSpectralEnergy_uniform_eighth_moment
  refine ⟨C, hC, fun σ hσ => ?_⟩
  exact candidate_dampedEnergy_moment_le_of_finiteSpectral
    ⟨hσ.1, hσ.2.trans (by norm_num)⟩ (by norm_num) (hb σ hσ)

end Erdos.Problem1144
