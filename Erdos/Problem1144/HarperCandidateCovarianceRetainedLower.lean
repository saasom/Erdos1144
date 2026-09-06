import Erdos.Problem1144.HarperCandidateCovarianceRetainedCrossing
import Erdos.Problem1144.HarperCandidateCovarianceRetainedVarianceLower
import Erdos.Problem1144.HarperCandidateCovarianceDegreeMeasurability

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- Actual retained Gaussian crossings are bounded below using the proved
white variance event, the common deletion/Perron budgets, and one common
near/far control failure. There is no covariance, variance, or kernel-error
assumption: the remaining hypothesis is the numerical Gaussian size test. -/
theorem candidate_retainedEuler_crossing_ge_white_variance_budget
    (q : Finset ℕ) (η : q → Bool) (start stop a depth M : ℕ) (hst : start ≤ stop)
    (W d : ℝ) {T B H θ b v K : ℝ}
    (hT : 0 < T) (hTB : T ≤ B) (hH : (M : ℝ) ≤ H) (hH0 : 0 < H)
    (hθ : 0 < θ) (hv : 0 < v) (hθv : θ ≤ v / 8) (hK : 0 ≤ K)
    (Ngrid k degree : ℕ) (hb : b ≤ degree) (origin : ℝ)
    (hu : ∀ i : Fin Ngrid, origin + i * (2 * Real.pi) ≤ B)
    (hy : ∀ i : Fin Ngrid, ⌊Real.exp (origin + i * (2 * Real.pi) - T)⌋₊ ≤
      Problem520.harperBlockEndpoint stop)
    (J : Omega → Finset (Fin Ngrid)) (hJ : ∀ i, MeasurableSet {ω | i ∈ J ω})
    (hsize : ∀ ω, Real.log 2 ≤ ((J ω).card : ℝ) / (degree + 1) *
      gaussianPDFReal 0 1 (Real.sqrt 2 * (K / Real.sqrt (v / 4)) + 1)) :
    let u := fun i : Fin Ngrid => origin + i * (2 * Real.pi)
    let s := Finset.Icc (a - start) (stop - start)
    let D := candidateCovarianceDegreeControlEvent start stop a W
      ((1 / 2 : ℝ) ^ (depth + 1)) M T B d k Ngrid ((2 * Real.pi) ^ 2 * θ) b
    ((candidateCylinderLaw q η).real
        {ω | ∀ i, v ≤ candidateWhiteCovariance (harperCandidateSquarefreeLogProcess ω) u T i i} -
      (candidateCylinderLaw q η).real
        (candidateCovarianceCommonMeshEvent start (stop - start) M W)ᶜ -
      (8 / v) *
        ((∫ ω, candidateCovarianceRetainedError (Problem520.harperBlockEndpoint stop)
          start (stop - start) depth M W T s ω ∂mu) +
          ∫ ω, candidateEulerBandWhiteTotalError (Problem520.harperBlockEndpoint stop)
            u H T B ω ∂mu) / mu.real (candidateCylinder q η) -
      (candidateCylinderLaw q η).real Dᶜ) / 4 ≤
        ∫ ω, candidateRetainedEulerWhiteCrossing (Problem520.harperBlockEndpoint stop)
          start (stop - start) depth M W s u T B J K ω ∂candidateCylinderLaw q η := by
  let Q := candidateCylinderLaw q η
  let u := fun i : Fin Ngrid => origin + i * (2 * Real.pi)
  let s := Finset.Icc (a - start) (stop - start)
  let D := candidateCovarianceDegreeControlEvent start stop a W
    ((1 / 2 : ℝ) ^ (depth + 1)) M T B d k Ngrid ((2 * Real.pi) ^ 2 * θ) b
  let R := candidateRetainedWhiteVarianceFloor (Problem520.harperBlockEndpoint stop)
    start (stop - start) depth M W s u T B (v / 4)
  have hD : MeasurableSet D := candidate_measurableSet_degreeControlEvent start stop a hst W
    ((1 / 2 : ℝ) ^ (depth + 1)) M T B d k Ngrid ((2 * Real.pi) ^ 2 * θ) b
  have hR : MeasurableSet R := candidate_measurableSet_retainedWhiteVarianceFloor
    (Problem520.harperBlockEndpoint stop) start (stop - start) depth M W s u T B (v / 4)
  have hp := candidate_retainedWhiteVariance_probability_ge q η
    (Problem520.harperBlockEndpoint stop) start (stop - start) depth M W s u hH hH0 hT B hu hy hv
  have hsplit := measureReal_inter_add_diff (μ := Q) (s := R) hD
  have hdiff : Q.real (R \ D) ≤ Q.real Dᶜ :=
    measureReal_mono (fun _ h => h.2)
  have hcross := candidate_retainedEuler_crossing_ge_quarter_of_control Q start stop a depth M W d
    hT hTB hθ (by positivity : 0 < v / 4) (by linarith : θ ≤ (v / 4) / 2)
    hK Ngrid k degree hb origin J hJ (R ∩ D) (hR.inter hD)
    (fun _ h => h.2) (fun ω hω i _ => by
      have hi := hω.1 i
      simpa only [candidateWeightedGram, one_mul, ← sq] using hi)
    (fun ω _ => hsize ω)
  dsimp only
  change _ ≤ ∫ ω, candidateRetainedEulerWhiteCrossing (Problem520.harperBlockEndpoint stop)
    start (stop - start) depth M W s u T B J K ω ∂Q
  change _ ≤ Q.real R at hp
  linarith

end
end Erdos.Problem1144
