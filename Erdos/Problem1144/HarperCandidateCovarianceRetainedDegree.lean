import Erdos.Problem1144.HarperCandidateCovarianceScreenDegree
import Erdos.Problem1144.HarperCandidateCovarianceRetainedDeletion

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144

/-- The actual retained kernel family satisfies the common bad-degree
bound. Its inclusive screens, symmetry, annulus, and finite frequency
window are all derived from the retained-set definition. -/
theorem candidate_retainedWhiteKernel_bad_degree_le_of_control
    (start stop a depth M : ℕ) (W d : ℝ) {T B θ b : ℝ}
    (hT : 0 < T) (hTB : T ≤ B) (hθ : 0 < θ) (Ngrid k : ℕ)
    {ω : Problem520.Omega}
    (hω : ω ∈ candidateCovarianceDegreeControlEvent start stop a W
      ((1 / 2 : ℝ) ^ (depth + 1)) M T B d k Ngrid ((2 * Real.pi) ^ 2 * θ) b)
    (u v : ℝ) :
    (((range Ngrid).filter fun j : ℕ => θ ≤ |∫ r,
      candidateEulerScreenWhiteKernel (Problem520.harperBlockEndpoint stop) ω
        (candidateCovarianceRetainedFrequencySet start (stop - start) depth M W
          (Finset.Icc (a - start) (stop - start)) ω) T B u r *
      candidateEulerScreenWhiteKernel (Problem520.harperBlockEndpoint stop) ω
        (candidateCovarianceRetainedFrequencySet start (stop - start) depth M W
          (Finset.Icc (a - start) (stop - start)) ω) T B
        (v + j * (2 * Real.pi)) r|).card : ℝ) ≤ b := by
  apply candidate_screenWhiteKernel_bad_degree_le_of_control
    start stop a W ((1 / 2 : ℝ) ^ (depth + 1)) M d hT hTB hθ Ngrid k hω u v
    (candidate_measurableSet_retainedFrequencySet start (stop - start) depth M W
      (Finset.Icc (a - start) (stop - start)) ω)
  · intro t
    exact (candidate_mem_retainedFrequencySet_neg start (stop - start) depth M W
      (Finset.Icc (a - start) (stop - start)) ω t).symm
  · intro t ht
    exact ht.2
  · intro t ht
    exact ht.1.1.le

end Erdos.Problem1144
