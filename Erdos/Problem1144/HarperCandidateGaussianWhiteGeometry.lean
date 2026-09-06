import Erdos.Problem1144.HarperCandidateGaussianVarianceLower
import Erdos.Problem1144.HarperCandidateGaussianSelectedLower
import Erdos.Problem1144.HarperCandidateTranslationWhiteKernel

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

local instance candidateWhiteGeometryMatrixMeasurableSpace {ι : Type*} :
    MeasurableSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → ι → ℝ))

/-- The squarefree kernel Gram is exactly the reciprocal-time covariance
used by the coefficient-prefix variance theorem. -/
theorem candidate_squarefreeWhiteKernel_gram_eq_whiteCovariance
    {ι : Type*} (ω : Omega) (u : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    candidateWeightedGram volume (fun i => candidateSquarefreeWhiteKernel ω (u i) T)
      (fun _ => 1) =
      candidateWhiteCovariance (harperCandidateSquarefreeLogProcess ω) u T := by
  ext i j
  unfold candidateWhiteCovariance candidateWeightedGram
  rw [integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    by_cases hx : T < x
    · simp only [candidateSquarefreeWhiteKernel,
        indicator_of_mem (show x ∈ Ioi T from hx), one_mul]
      calc
        _ = (harperCandidateSquarefreeLogProcess ω (u i - x) *
            harperCandidateSquarefreeLogProcess ω (u j - x)) / (Real.sqrt x) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt (hT.trans hx).le]; ring
    · simp [candidateSquarefreeWhiteKernel, hx]

/-- The literal white covariance is a measurable matrix family. -/
theorem candidate_measurable_squarefreeWhiteCovariance
    {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    Measurable (fun ω => candidateWhiteCovariance (harperCandidateSquarefreeLogProcess ω) u T) := by
  simp_rw [← candidate_squarefreeWhiteKernel_gram_eq_whiteCovariance _ u hT]
  exact candidate_measurable_random_gram volume
    (fun i ω => candidateSquarefreeWhiteKernel ω (u i) T)
    (fun i => measurable_candidateSquarefreeWhiteKernel (u i) T)

/-- Positive semidefiniteness of the actual finite white covariance, with
integrability supplied by the literal squarefree kernels. -/
theorem candidate_squarefreeWhiteCovariance_posSemidef
    {ι : Type*} [Finite ι] (ω : Omega) (u : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    (candidateWhiteCovariance (harperCandidateSquarefreeLogProcess ω) u T).PosSemidef := by
  rw [← candidate_squarefreeWhiteKernel_gram_eq_whiteCovariance ω u hT]
  apply candidateWeightedGram_posSemidef volume
    (fun i => candidateSquarefreeWhiteKernel ω (u i) T) (fun _ => 1)
  · intro i j
    simpa only [one_mul] using
      (candidate_memLp_squarefreeWhiteKernel ω (u i) hT).integrable_mul
        (candidate_memLp_squarefreeWhiteKernel ω (u j) hT)
  · exact ae_of_all _ fun _ => Or.inl zero_le_one

/-- The simultaneous variance-floor event used on a finite grid is
measurable under the original sign law and every fixed cylinder. -/
theorem candidate_measurableSet_squarefreeWhiteVariance_floor
    {N : ℕ} (u : Fin N → ℝ) {T : ℝ} (hT : 0 < T) (v : ℝ) :
    MeasurableSet {ω | ∀ i, v ≤
      candidateWhiteCovariance (harperCandidateSquarefreeLogProcess ω) u T i i} := by
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le measurable_const
    ((measurable_pi_apply i).comp ((measurable_pi_apply i).comp
      (candidate_measurable_squarefreeWhiteCovariance u hT)))

end Erdos.Problem1144
