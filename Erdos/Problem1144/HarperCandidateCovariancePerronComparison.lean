import Erdos.Problem1144.HarperCandidateCovariancePerronErrorWhite
import Erdos.Problem1144.HarperCandidatePrimeWhiteComparisonCrossing

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- The literal real Euler-band Gaussian law tested on the retained coordinates. -/
def candidateEulerBandWhiteCrossing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : ℕ) (u : ι → ℝ) (H T B : ℝ) (J : Omega → Finset ι) (K : ℝ) (ω : Omega) : ℝ :=
  (multivariateGaussian (0 : EuclideanSpace ℝ ι)
    (candidateWeightedGram volume (fun i => candidateEulerBandWhiteKernel Y ω H T B (u i))
      (fun _ => 1))).real {x | ∃ i ∈ J ω, K < |x i|}

/-- The error budget is the actual sum of real Gaussian kernel distances. -/
def candidateEulerBandWhiteTotalError {ι : Type*} [Fintype ι]
    (Y : ℕ) (u : ι → ℝ) (H T B : ℝ) (ω : Omega) : ℝ :=
  ∑ i, ∫ r, (candidateEulerBandWhiteKernel Y ω H T B (u i) r -
    candidateSquarefreeWhiteKernel ω (u i) T r) ^ 2

theorem candidate_eulerBandWhiteTotalError_nonneg {ι : Type*} [Fintype ι]
    (Y : ℕ) (u : ι → ℝ) (H T B : ℝ) (ω : Omega) :
    0 ≤ candidateEulerBandWhiteTotalError Y u H T B ω :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _

theorem candidate_integrable_eulerBandWhiteTotalError {ι : Type*} [Fintype ι]
    (Y : ℕ) (u : ι → ℝ) {H T : ℝ} (hH : 0 < H) (hT : 0 < T) (B : ℝ)
    (hu : ∀ i, u i ≤ B) (hY : ∀ i, ⌊Real.exp (u i - T)⌋₊ ≤ Y) :
    Integrable (candidateEulerBandWhiteTotalError Y u H T B) mu := by
  exact integrable_finset_sum _ fun i _ =>
    candidate_integrable_eulerBandWhiteKernel_error Y hH hT B (u i) (hu i) (hY i)

/-- One actual Gram coupling transfers selected crossings from the real
Euler-band law to the already used squarefree white law, under every fixed
cylinder. No Gaussian-law or error premise remains. -/
theorem candidate_eulerBand_white_selected_crossing_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ℕ) (η : s → Bool) (Y : ℕ) (u : ι → ℝ)
    {H T : ℝ} (hH : 0 < H) (hT : 0 < T) (B : ℝ)
    (hu : ∀ i, u i ≤ B) (hY : ∀ i, ⌊Real.exp (u i - T)⌋₊ ≤ Y)
    (J : Omega → Finset ι) (hJ : ∀ i, MeasurableSet {ω | i ∈ J ω})
    (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ ω, candidateEulerBandWhiteCrossing Y u H T B J (K + ε) ω
      ∂candidateCylinderLaw s η) ≤
    (∫ ω, candidateComparisonWhiteCrossing true u T J K ω ∂candidateCylinderLaw s η) +
      (∫ ω, candidateEulerBandWhiteTotalError Y u H T B ω ∂mu) /
        (mu.real (candidateCylinder s η) * ε ^ 2) := by
  have hc := candidateCylinderLaw_integral_nonneg_le s η
    (candidate_integrable_eulerBandWhiteTotalError Y u hH hT B hu hY)
    (candidate_eulerBandWhiteTotalError_nonneg Y u H T B)
  have h := candidate_integral_gaussian_gram_selected_crossing_le
    (candidateCylinderLaw s η) volume
    (fun i ω => candidateSquarefreeWhiteKernel ω (u i) T)
    (fun i ω => candidateEulerBandWhiteKernel Y ω H T B (u i))
    (fun i => measurable_candidateSquarefreeWhiteKernel (u i) T)
    (fun i => candidate_measurable_eulerBandWhiteKernel Y H T B (u i))
    (fun ω i => candidate_memLp_squarefreeWhiteKernel ω (u i) hT)
    (fun ω i => candidate_memLp_eulerBandWhiteKernel Y ω H B (u i) hT)
    J hJ (by simpa only [sub_sq_comm] using hc.1) K hε
  have he := div_le_div_of_nonneg_right hc.2 (sq_nonneg ε)
  rw [div_div] at he
  simp only [sub_sq_comm] at h
  change (∫ ω, candidateEulerBandWhiteCrossing Y u H T B J (K + ε) ω
    ∂candidateCylinderLaw s η) ≤
    (∫ ω, candidateComparisonWhiteCrossing true u T J K ω ∂candidateCylinderLaw s η) +
      (∫ ω, candidateEulerBandWhiteTotalError Y u H T B ω ∂candidateCylinderLaw s η) / ε ^ 2 at h
  exact h.trans (add_le_add_right he _)

/-- Uniform total distance at the literal exponential prime cutoff. -/
theorem candidate_exists_eulerBandWhiteTotalError_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] (u : ι → ℝ) (T H B : ℝ),
      Real.log 2 ≤ T → 0 < H → (∀ i, u i ≤ 2 * T) → (∀ i, u i ≤ B) →
      (∫ ω, candidateEulerBandWhiteTotalError ⌊Real.exp T⌋₊ u H T B ω ∂mu) ≤
        C * Fintype.card ι / H := by
  obtain ⟨C, hC, hb⟩ := candidate_exists_eulerBandWhiteKernel_error_bound
  refine ⟨C, hC, ?_⟩
  intro ι _ u T H B hTlog hH hu huB
  have hT : 0 < T := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hTlog
  have hY (i : ι) : ⌊Real.exp (u i - T)⌋₊ ≤ ⌊Real.exp T⌋₊ :=
    Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith [hu i]))
  unfold candidateEulerBandWhiteTotalError
  rw [integral_finset_sum _ (fun i _ =>
    candidate_integrable_eulerBandWhiteKernel_error _ hH hT B (u i) (huB i) (hY i))]
  calc
    _ ≤ ∑ i : ι, C / H := Finset.sum_le_sum fun i _ => hb T H B (u i) hTlog hH (hu i) (huB i)
    _ = _ := by simp; ring

/-- The explicit finite-grid loss is `C card/(H ε²)` times the fixed
conditioning factor. The frequency cutoff `H` is an independent auxiliary
parameter and is not identified with a stationary spectral cutoff. -/
theorem candidate_exists_eulerBand_white_selected_crossing_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (s : Finset ℕ) (η : s → Bool) (u : ι → ℝ) (T H B : ℝ),
      Real.log 2 ≤ T → 0 < H → (∀ i, u i ≤ 2 * T) → (∀ i, u i ≤ B) →
      ∀ (J : Omega → Finset ι), (∀ i, MeasurableSet {ω | i ∈ J ω}) →
      ∀ K ε : ℝ, 0 < ε →
      (∫ ω, candidateEulerBandWhiteCrossing ⌊Real.exp T⌋₊ u H T B J (K + ε) ω
        ∂candidateCylinderLaw s η) ≤
      (∫ ω, candidateComparisonWhiteCrossing true u T J K ω ∂candidateCylinderLaw s η) +
        C * Fintype.card ι / (H * mu.real (candidateCylinder s η) * ε ^ 2) := by
  obtain ⟨C, hC, hb⟩ := candidate_exists_eulerBandWhiteTotalError_bound
  refine ⟨C, hC, ?_⟩
  intro ι _ _ s η u T H B hTlog hH hu huB J hJ K ε hε
  have hT : 0 < T := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hTlog
  have hY (i : ι) : ⌊Real.exp (u i - T)⌋₊ ≤ ⌊Real.exp T⌋₊ :=
    Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith [hu i]))
  refine (candidate_eulerBand_white_selected_crossing_le s η _ u hH hT B huB hY J hJ K hε).trans ?_
  apply add_le_add_right
  have he := div_le_div_of_nonneg_right (hb u T H B hTlog hH hu huB)
    (show 0 ≤ mu.real (candidateCylinder s η) * ε ^ 2 by positivity)
  simpa only [div_div, mul_assoc] using he

end
end Erdos.Problem1144
