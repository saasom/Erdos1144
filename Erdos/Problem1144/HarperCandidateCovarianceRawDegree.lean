import Erdos.Problem1144.HarperCandidateCovarianceNearRowControl
import Erdos.Problem1144.HarperCandidateCovarianceFarMoment

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- The literal angular Fourier covariance integrand, before `(2π)⁻²`. -/
def candidateEulerBandCovarianceIntegrand (Y : ℕ) (ω : Problem520.Omega)
    (T B u v : ℝ) (z : ℝ × ℝ) : ℂ :=
  candidateEulerAngularApprox Y 0 ω z.1 *
    starRingEnd ℂ (candidateEulerAngularApprox Y 0 ω z.2) *
    candidateCovariancePhase (u * z.1 - v * z.2) *
    candidateCovarianceWhiteKernel T B (z.1 - z.2)

/-- The actual raw covariance on an arbitrary retained scalar frequency set. -/
def candidateEulerBandRawCovariance (Y : ℕ) (ω : Problem520.Omega)
    (T B u v : ℝ) (S : Set ℝ) : ℂ :=
  ∫ z in S ×ˢ S, candidateEulerBandCovarianceIntegrand Y ω T B u v z ∂volume.prod volume

theorem candidate_covarianceIntegrand_norm (Y : ℕ) (ω : Problem520.Omega)
    (T B u v : ℝ) (z : ℝ × ℝ) :
    ‖candidateEulerBandCovarianceIntegrand Y ω T B u v z‖ =
      candidateEulerBandRowWeight Y ω T B z := by
  simp only [candidateEulerBandCovarianceIntegrand, norm_mul, Complex.norm_conj,
    candidateCovariancePhase, Complex.norm_exp_ofReal_mul_I, mul_one, candidateEulerBandRowWeight]

/-- An additional subset restriction removes the redundant finite window
from the exact product measure, without altering the retained integral. -/
theorem candidate_restrict_pair_window_eq (M : ℝ) {E : Set (ℝ × ℝ)}
    (hE : MeasurableSet E) (hbox : E ⊆ Icc (-M) M ×ˢ Icc (-M) M) :
    (((volume.restrict (Icc (-M) M)).prod (volume.restrict (Icc (-M) M))).restrict E) =
      (volume.prod volume).restrict E := by
  rw [Measure.prod_restrict, Measure.restrict_restrict hE, inter_eq_left.mpr hbox]

private theorem integrand_integrable (Y : ℕ) (ω : Problem520.Omega) (M u v : ℝ)
    {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) {E : Set (ℝ × ℝ)}
    (hE : MeasurableSet E) (hbox : E ⊆ Icc (-M) M ×ˢ Icc (-M) M) :
    IntegrableOn (candidateEulerBandCovarianceIntegrand Y ω T B u v) E
      (volume.prod volume) := by
  have hw := (candidate_integrable_eulerBandRowAmplitude Y ω M 0 hT hTB E).norm
  simp only [candidate_eulerBandRowAmplitude_norm,
    candidate_restrict_pair_window_eq M hE hbox] at hw
  have hm : Measurable (candidateEulerBandCovarianceIntegrand Y ω T B u v) := by
    have hA := (candidate_continuous_criticalEulerAngularApprox Y ω).measurable
    have hK := candidate_measurable_whiteKernel T B
    unfold candidateEulerBandCovarianceIntegrand candidateCovariancePhase
    fun_prop
  exact hw.mono' hm.aestronglyMeasurable (ae_of_all _ fun z => by
    rw [candidate_covarianceIntegrand_norm])

/-- Exact near/far splitting of the literal retained covariance. The far
region is the strict complement of the closed near-diagonal strip. -/
theorem candidate_rawCovariance_eq_near_add_far (Y : ℕ) (ω : Problem520.Omega)
    (M d u v : ℝ) {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B)
    {S : Set ℝ} (hS : MeasurableSet S) (hSM : ∀ t ∈ S, |t| ≤ M) :
    candidateEulerBandRawCovariance Y ω T B u v S =
      (∫ z in candidateRowPairDomain S d,
        candidateEulerBandCovarianceIntegrand Y ω T B u v z ∂volume.prod volume) +
      (∫ z in (S ×ˢ S) \ candidateRowPairDomain S d,
        candidateEulerBandCovarianceIntegrand Y ω T B u v z ∂volume.prod volume) := by
  have hE := candidate_measurableSet_rowPairDomain hS d
  have hsub : candidateRowPairDomain S d ⊆ S ×ˢ S := fun z hz => ⟨hz.1, hz.2.1⟩
  have hbox : S ×ˢ S ⊆ Icc (-M) M ×ˢ Icc (-M) M :=
    fun z hz => ⟨abs_le.mp (hSM _ hz.1), abs_le.mp (hSM _ hz.2)⟩
  have hi := integrand_integrable Y ω M u v hT hTB (hS.prod hS) hbox
  have h := integral_inter_add_diff hE hi
  rw [inter_eq_right.mpr hsub] at h
  exact h.symm

/-- The common far mass controls every retained covariance remainder,
independently of both time endpoints. -/
theorem candidate_rawCovariance_norm_le_near_add_farMass (Y : ℕ) (ω : Problem520.Omega)
    (h M d u v : ℝ) {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B)
    {S : Set ℝ} (hS : MeasurableSet S)
    (hSM : ∀ t ∈ S, h ≤ |t| ∧ |t| ≤ M) :
    ‖candidateEulerBandRawCovariance Y ω T B u v S‖ ≤
      ‖∫ z in candidateRowPairDomain S d,
        candidateEulerBandCovarianceIntegrand Y ω T B u v z ∂volume.prod volume‖ +
      candidateEulerBandFarMass Y T B h M d ω := by
  rw [candidate_rawCovariance_eq_near_add_far Y ω M d u v hT hTB hS
    (fun t ht => (hSM t ht).2)]
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  apply candidate_restricted_far_covariance_norm_le Y ω hT hTB h M d u v
    ((S ×ˢ S) \ candidateRowPairDomain S d)
    ((hS.prod hS).diff (candidate_measurableSet_rowPairDomain hS d))
  intro z hz
  have hgap : d < |z.1 - z.2| := by
    by_contra hg
    exact hz.2 ⟨hz.1.1, hz.1.2, le_of_not_gt hg⟩
  exact ⟨(hSM _ hz.1.1).1, (hSM _ hz.1.1).2,
    (hSM _ hz.1.2).1, (hSM _ hz.1.2).2, hgap.le⟩

/-- On one common far-mass event, every raw retained covariance row has
at most the near envelope divided by `(τ/2)^(2k)` bad entries. This counts
the actual entries on the grid and introduces no union over row endpoints. -/
theorem candidate_rawCovariance_bad_degree_le
    (start stop a : ℕ) (ω : Problem520.Omega) (W h M d u v : ℝ)
    {T B τ : ℝ} (hT : 0 < T) (hTB : T ≤ B) (hτ : 0 < τ) (N k : ℕ)
    {S : Set ℝ} (hS : MeasurableSet S)
    (hret : S ⊆ candidateCovarianceScreenedHeightSet
      start (stop - start) W M (Finset.Icc (a - start) (stop - start)) ω)
    (hann : ∀ t ∈ S, h ≤ |t|)
    (hfar : candidateEulerBandFarMass (Problem520.harperBlockEndpoint stop) T B h M d ω ≤ τ / 2) :
    (((range N).filter fun j : ℕ => τ ≤ ‖candidateEulerBandRawCovariance
      (Problem520.harperBlockEndpoint stop) ω T B u (v + j * (2 * Real.pi)) S‖).card : ℝ) ≤
      candidateEulerBandNearRowEnvelope start stop a W M T B d k N ω / (τ / 2) ^ (2 * k) := by
  classical
  let Y := Problem520.harperBlockEndpoint stop
  let near (j : ℕ) := ∫ z in candidateRowPairDomain S d,
    candidateEulerBandCovarianceIntegrand Y ω T B u (v + j * (2 * Real.pi)) z
      ∂volume.prod volume
  let bad := (range N).filter fun j : ℕ => τ ≤
    ‖candidateEulerBandRawCovariance Y ω T B u (v + j * (2 * Real.pi)) S‖
  have hSM (t : ℝ) (ht : t ∈ S) : h ≤ |t| ∧ |t| ≤ M :=
    ⟨hann t ht, (hret ht).1⟩
  have hpoint (j : ℕ) (hj : j ∈ bad) : (τ / 2) ^ (2 * k) ≤ ‖near j‖ ^ (2 * k) := by
    have hb := (Finset.mem_filter.mp hj).2
    have hr := candidate_rawCovariance_norm_le_near_add_farMass Y ω h M d u
      (v + j * (2 * Real.pi)) hT hTB hS hSM
    have hn : τ / 2 ≤ ‖near j‖ := by dsimp only [near]; linarith
    exact pow_le_pow_left₀ (by positivity) hn _
  have hsum : (∑ j ∈ range N, ‖near j‖ ^ (2 * k)) ≤
      candidateEulerBandNearRowEnvelope start stop a W M T B d k N ω := by
    have hbox : candidateRowPairDomain S d ⊆ Icc (-M) M ×ˢ Icc (-M) M :=
      fun z hz => ⟨abs_le.mp (hSM _ hz.1).2, abs_le.mp (hSM _ hz.2.1).2⟩
    have hc := candidate_retained_near_row_power_sum_le start stop a ω W M d u v
      hT hTB N k S hret
    rw [candidate_restrict_pair_window_eq M (candidate_measurableSet_rowPairDomain hS d) hbox] at hc
    exact hc
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < τ / 2) _)).mpr
  calc
    (bad.card : ℝ) * (τ / 2) ^ (2 * k) = ∑ _j ∈ bad, (τ / 2) ^ (2 * k) := by simp
    _ ≤ ∑ j ∈ bad, ‖near j‖ ^ (2 * k) := Finset.sum_le_sum fun j hj => hpoint j hj
    _ ≤ ∑ j ∈ range N, ‖near j‖ ^ (2 * k) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => by positivity)
    _ ≤ _ := hsum

end
end Erdos.Problem1144
