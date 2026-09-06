import Erdos.Problem1144.HarperCandidateCovarianceRetainedDeletion
import Erdos.Problem1144.HarperCandidateCovarianceScreenMeasurability
import Erdos.Problem1144.HarperCandidateGaussianGramMaxima
import Erdos.Problem1144.HarperCandidateCovariancePerronComparison

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- Selected maxima of the actual annulus-screened Euler white process. -/
def candidateRetainedEulerWhiteCrossing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y start N d M : ℕ) (W : ℝ) (s : Finset ℕ) (u : ι → ℝ)
    (T B : ℝ) (J : Omega → Finset ι) (K : ℝ) (ω : Omega) : ℝ :=
  (multivariateGaussian (0 : EuclideanSpace ℝ ι)
    (candidateWeightedGram volume
      (fun i => candidateEulerScreenWhiteKernel y ω
        (candidateCovarianceRetainedFrequencySet start N d M W s ω) T B (u i))
      (fun _ => 1))).real {x | ∃ i ∈ J ω, K < |x i|}

/-- The actual retained Fourier process transfers to the full Euler band.
The cost is one common mesh failure, a logarithmic multiple of the proved
common coefficient error, and the Gaussian tail. No Gaussian-law, screen-loss,
or regularity premise is left to the caller. -/
theorem candidate_retainedEuler_band_selected_crossing_le
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (q : Finset ℕ) (η : q → Bool) (y start N d M : ℕ) (W : ℝ) (s : Finset ℕ)
    (u : ι → ℝ) {H T : ℝ} (hH : (M : ℝ) ≤ H) (hT : 0 < T) (B : ℝ)
    (J : Omega → Finset ι) (hJ : ∀ i, MeasurableSet {ω | i ∈ J ω})
    (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ ω, candidateRetainedEulerWhiteCrossing y start N d M W s u T B J (K + ε) ω
      ∂candidateCylinderLaw q η) ≤
    (∫ ω, candidateEulerBandWhiteCrossing y u H T B J K ω ∂candidateCylinderLaw q η) +
      (candidateCylinderLaw q η).real (candidateCovarianceCommonMeshEvent start N M W)ᶜ +
      4 * Real.log (2 * Fintype.card ι) *
        (∫ ω, candidateCovarianceRetainedError y start N d M W T s ω ∂mu) /
          (mu.real (candidateCylinder q η) * ε ^ 2) + 1 / (2 * Fintype.card ι) := by
  let S := candidateCovarianceRetainedFrequencySet start N d M W s
  have hS := candidate_measurableSet_retainedFrequencyGraph start N d M W s
  have hc := candidateCylinderLaw_integral_nonneg_le q η
    (candidate_integrable_retainedError y start N d M W T s)
    (candidate_retainedError_nonneg y start N d M W hT.le s)
  have h := candidate_integral_gaussian_gram_selected_crossing_log_variance_on_le
    (candidateCylinderLaw q η) volume
    (fun i ω => candidateEulerBandWhiteKernel y ω H T B (u i))
    (fun i ω => candidateEulerScreenWhiteKernel y ω (S ω) T B (u i))
    (fun i => candidate_measurable_eulerBandWhiteKernel y H T B (u i))
    (fun i => candidate_measurable_eulerScreenWhiteKernel_joint y S hS T B (u i))
    (fun ω i => candidate_memLp_eulerBandWhiteKernel y ω H B (u i) hT)
    (fun ω i => candidate_memLp_eulerScreenWhiteKernel y ω
      (candidate_measurableSet_retainedFrequencySet start N d M W s ω) H
      (candidate_retainedFrequencySet_subset_band start N d M W s ω hH) B (u i) hT)
    J hJ (candidateCovarianceCommonMeshEvent start N M W)
    (candidate_measurableSet_covarianceCommonMesh start N M W)
    (candidateCovarianceRetainedError y start N d M W T s) hc.1
    (candidate_retainedError_nonneg y start N d M W hT.le s)
    (fun ω hω i => by simpa only [sub_sq_comm] using
      candidate_retainedWhiteKernel_distance_le y start N d M W s hω hH hT B (u i)) K hε
  have hlog : 0 ≤ Real.log (2 * Fintype.card ι) := Real.log_nonneg (by
    have hn : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
    linarith)
  have he := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc.2 (by positivity : 0 ≤ 4 * Real.log (2 * Fintype.card ι)))
    (sq_nonneg ε)
  have he' : 4 * Real.log (2 * Fintype.card ι) *
      (∫ ω, candidateCovarianceRetainedError y start N d M W T s ω ∂candidateCylinderLaw q η) / ε ^ 2 ≤
      4 * Real.log (2 * Fintype.card ι) *
        (∫ ω, candidateCovarianceRetainedError y start N d M W T s ω ∂mu) /
          (mu.real (candidateCylinder q η) * ε ^ 2) := by
    simpa only [← mul_div_assoc, div_div] using he
  dsimp only [candidateRetainedEulerWhiteCrossing, candidateEulerBandWhiteCrossing]
  dsimp only [S] at h
  linarith

/-- Composition with the already proved Perron comparison reaches the
squarefree white process used by the final Gaussian crossing endpoint. The
two threshold margins pay separately for screen deletion and Fourier truncation. -/
theorem candidate_retainedEuler_white_selected_crossing_le
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (q : Finset ℕ) (η : q → Bool) (y start N d M : ℕ) (W : ℝ) (s : Finset ℕ)
    (u : ι → ℝ) {H T : ℝ} (hH : (M : ℝ) ≤ H) (hH0 : 0 < H) (hT : 0 < T) (B : ℝ)
    (hu : ∀ i, u i ≤ B) (hy : ∀ i, ⌊Real.exp (u i - T)⌋₊ ≤ y)
    (J : Omega → Finset ι) (hJ : ∀ i, MeasurableSet {ω | i ∈ J ω})
    (K : ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    (∫ ω, candidateRetainedEulerWhiteCrossing y start N d M W s u T B J (K + ε + δ) ω
      ∂candidateCylinderLaw q η) ≤
    (∫ ω, candidateComparisonWhiteCrossing true u T J K ω ∂candidateCylinderLaw q η) +
      (candidateCylinderLaw q η).real (candidateCovarianceCommonMeshEvent start N M W)ᶜ +
      4 * Real.log (2 * Fintype.card ι) *
        (∫ ω, candidateCovarianceRetainedError y start N d M W T s ω ∂mu) /
          (mu.real (candidateCylinder q η) * ε ^ 2) + 1 / (2 * Fintype.card ι) +
      (∫ ω, candidateEulerBandWhiteTotalError y u H T B ω ∂mu) /
        (mu.real (candidateCylinder q η) * δ ^ 2) := by
  have hr := candidate_retainedEuler_band_selected_crossing_le q η y start N d M W s u
    hH hT B J hJ (K + δ) hε
  have hp := candidate_eulerBand_white_selected_crossing_le q η y u hH0 hT B hu hy J hJ K hδ
  rw [show K + δ + ε = K + ε + δ by ring] at hr
  linarith

end
end Erdos.Problem1144
