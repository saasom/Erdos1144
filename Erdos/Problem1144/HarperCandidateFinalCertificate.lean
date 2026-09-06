import Erdos.Problem1144.HarperCandidateScheduledCompleteWhite
import Erdos.Problem1144.HarperCandidateScheduledWhiteAssembly

namespace Erdos.Problem1144

/-- An instantiated robust Gaussian certificate for the actual complete
fresh-prime field. The fixed window lies in (1,4/3), its retained fraction
is 1/2, and the stationary extension has (alpha-1)*kappa=3>2. -/
theorem candidate_scheduledGaussianRobustCrossing_certificate :
    ∃ p : ℝ, 0 < p ∧
      CandidateScheduledGaussianRobustCrossingStatement (7 / 6) (5 / 4) 18 (1 / 2) p := by
  obtain ⟨p, hp, hwhite⟩ := candidate_exists_scheduled_completeWhite_crossing
  refine ⟨p, hp, ?_⟩
  apply candidateScheduledGaussianRobustCrossing_of_completeWhite
    (by norm_num : (7 : ℝ) / 6 ≤ 5 / 4) (by norm_num : (1 : ℝ) ≤ 5 / 4)
    (by norm_num : (0 : ℝ) < 18)
  exact hwhite (7 / 6) (5 / 4) 18 (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end Erdos.Problem1144
