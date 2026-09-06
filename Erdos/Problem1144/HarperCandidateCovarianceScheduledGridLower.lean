import Erdos.Problem1144.HarperCandidateCovarianceScheduledGridDegree
import Erdos.Problem1144.HarperCandidateCovarianceScheduledRetained
import Erdos.Problem1144.HarperCandidateCovarianceRetainedCrossing
import Erdos.Problem1144.HarperCandidateCovarianceCrossingThreshold
import Erdos.Problem1144.HarperCandidateGaussianScheduledSize

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- Polynomial selected cardinality supplies the Gaussian size inequality
independently of the schedule used to construct those selected points. The
exponent 9/10 is the sum of the proved degree exponent 4/5 and size exponent 1/10. -/
theorem candidate_eventually_grid_gaussian_size {v : ℝ} (hv : 0 < v)
    (A : ℝ) (ℓ : ℕ) :
    ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, 2 * T ^ ((9 : ℝ) / 10) ≤ c →
      Real.log 2 ≤ c / (⌊T ^ ((4 : ℝ) / 5)⌋₊ + 1 : ℝ) *
        gaussianPDFReal 0 1 (Real.sqrt 2 *
          ((A * Real.log (1 + Real.log T) ^ ℓ) /
            Real.sqrt ((v * (1 + Real.log T) ^ (-(1 : ℝ) / 2)) / 4)) + 1) := by
  have hg := (candidate_tendsto_polynomialSize_gaussianPDF_loglog_threshold
    (v := v / 4) (γ := (1 : ℝ) / 10) (by positivity) (by norm_num) A ℓ).eventually_ge_atTop
      (Real.log 2)
  filter_upwards [hg, eventually_ge_atTop (1 : ℝ)] with T hg hT1
  intro c hc
  have hT : 0 < T := by linarith
  have hf := Nat.floor_le (Real.rpow_nonneg hT.le ((4 : ℝ) / 5))
  have hp : 1 ≤ T ^ ((4 : ℝ) / 5) := Real.one_le_rpow hT1 (by norm_num)
  have hd : (⌊T ^ ((4 : ℝ) / 5)⌋₊ : ℝ) + 1 ≤ 2 * T ^ ((4 : ℝ) / 5) := by linarith
  have hsize : T ^ ((1 : ℝ) / 10) ≤ c / (⌊T ^ ((4 : ℝ) / 5)⌋₊ + 1 : ℝ) := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ T ^ ((1 : ℝ) / 10) * (2 * T ^ ((4 : ℝ) / 5)) :=
        mul_le_mul_of_nonneg_left hd (Real.rpow_nonneg hT.le _)
      _ = 2 * T ^ ((9 : ℝ) / 10) := by
        rw [show (9 : ℝ) / 10 = 1 / 10 + 4 / 5 by norm_num, Real.rpow_add hT]
        ring
      _ ≤ c := hc
  have hh := hg.trans (mul_le_mul_of_nonneg_right hsize (gaussianPDFReal_nonneg _ _ _))
  simpa only [show v / 4 * (1 + Real.log T) ^ (-(1 : ℝ) / 2) =
    (v * (1 + Real.log T) ^ (-(1 : ℝ) / 2)) / 4 by ring] using hh

/-- On the literal rounded screen, the crossing lower bound is one quarter
of the retained variance probability, with the common degree failure removed.
The affine grid and measurable selector are independent of any outer schedule. -/
theorem candidate_scheduledGrid_retained_crossing_lower
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (J : ℕ) (β T : ℝ) (n : ℕ) (origin : ℝ)
    (selector : Omega → Finset (Fin n))
    (hselector : ∀ i, MeasurableSet {ω | i ∈ selector ω})
    {v K : ℝ} (hT : 1 < T) (hβ : 1 ≤ β) (hv : 0 < v) (hK : 0 ≤ K)
    (horder : candidateCovarianceScheduleStart J T ≤ candidateEulerTopIndex T)
    (hθ : Real.log T ^ (-(3 : ℝ) / 5) ≤ v / 2)
    (hdegree : T ^ ((4 : ℝ) / 5) / 2 ≤ (⌊T ^ ((4 : ℝ) / 5)⌋₊ : ℝ))
    (hsize : ∀ ω, Real.log 2 ≤ (selector ω).card /
      (⌊T ^ ((4 : ℝ) / 5)⌋₊ + 1 : ℝ) *
        gaussianPDFReal 0 1 (Real.sqrt 2 * (K / Real.sqrt v) + 1)) :
    let u := fun i : Fin n => origin + i * (2 * Real.pi)
    (Q.real (candidateCovarianceScheduledRetainedVarianceFloor J β u T v) -
      Q.real (candidateCovarianceScheduledGridDegreeControl J β T n)ᶜ) / 4 ≤
      ∫ ω, candidateCovarianceScheduledRetainedCrossing J β u T selector K ω ∂Q := by
  let u := fun i : Fin n => origin + i * (2 * Real.pi)
  let V := candidateCovarianceScheduledRetainedVarianceFloor J β u T v
  let D := candidateCovarianceScheduledGridDegreeControl J β T n
  have hV : MeasurableSet V := candidate_measurableSet_retainedWhiteVarianceFloor
    _ _ _ _ _ _ _ _ _ _ _
  have hD : MeasurableSet D := candidate_measurableSet_scheduledGridDegreeControl
    J β T n horder
  have hp : Q.real V ≤ Q.real (V ∩ D) + Q.real Dᶜ := by
    apply (measureReal_mono (μ := Q) (show V ⊆ (V ∩ D) ∪ Dᶜ from ?_)).trans
      (measureReal_union_le _ _)
    intro ω hω
    by_cases h : ω ∈ D
    · exact Or.inl ⟨hω, h⟩
    · exact Or.inr h
  have hTp : 0 < T := by linarith
  have hTB : T ≤ β * T := by nlinarith [mul_le_mul_of_nonneg_right hβ hTp.le]
  have hq : 0 < Real.log T := Real.log_pos hT
  have hh := candidate_retainedEuler_crossing_ge_quarter_of_control Q
    (candidateCovarianceScheduleStart J T) (candidateEulerTopIndex T)
    (candidateCovarianceScheduleStrong J T) (candidateCovarianceScheduleDepth T)
    (candidateCovarianceScheduleHeight T) (Real.log T) (candidateCovarianceScheduleWidth T)
    hTp hTB (by positivity : 0 < Real.log T ^ (-(3 : ℝ) / 5)) hv hθ hK
    n (candidateCovarianceScheduleOrder T) ⌊T ^ ((4 : ℝ) / 5)⌋₊ hdegree origin
    selector hselector (V ∩ D) (hV.inter hD)
    (fun _ h => h.2) (fun ω hω i _ => by
      have hi := hω.1 i
      simpa only [V, candidateCovarianceScheduledRetainedVarianceFloor,
        candidateRetainedWhiteVarianceFloor, candidateWeightedGram, one_mul, ← sq,
        candidateEulerTopCutoff, candidateCovarianceScheduleSelected,
        candidateCovarianceScheduleStrong, Nat.add_sub_cancel_left,
        candidateCovarianceScheduleLength, u] using hi) (fun ω _ => hsize ω)
  have hh' : Q.real (V ∩ D) / 4 ≤
        ∫ ω, candidateCovarianceScheduledRetainedCrossing J β u T selector K ω ∂Q := by
    simpa only [candidateCovarianceScheduledRetainedCrossing,
      candidateEulerTopCutoff, candidateCovarianceScheduleSelected,
      candidateCovarianceScheduleStrong, Nat.add_sub_cancel_left,
      candidateCovarianceScheduleLength, u] using hh
  change (Q.real V - Q.real Dᶜ) / 4 ≤ _
  linarith

end
end Erdos.Problem1144
