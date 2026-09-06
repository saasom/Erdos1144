import Erdos.Problem1144.HarperCandidateCovarianceRawDegree

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- One common near/far event controls all retained rows and all row origins.
The degree budget is a real number, to permit later rounded cardinal bounds. -/
def candidateCovarianceDegreeControlEvent (start stop a : ℕ) (W h M T B d : ℝ)
    (k N : ℕ) (τ b : ℝ) : Set Problem520.Omega :=
  {ω | candidateEulerBandFarMass (Problem520.harperBlockEndpoint stop) T B h M d ω ≤ τ / 2 ∧
    candidateEulerBandNearRowEnvelope start stop a W M T B d k N ω ≤ b * (τ / 2) ^ (2 * k)}

/-- Membership in the same event bounds the actual bad degree simultaneously
for every retained set, row time, and grid origin. -/
theorem candidate_rawCovariance_bad_degree_le_of_control
    (start stop a : ℕ) (W h M d : ℝ) {T B τ b : ℝ}
    (hT : 0 < T) (hTB : T ≤ B) (hτ : 0 < τ) (N k : ℕ)
    {ω : Problem520.Omega}
    (hω : ω ∈ candidateCovarianceDegreeControlEvent start stop a W h M T B d k N τ b)
    (u v : ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    (hret : S ⊆ candidateCovarianceScreenedHeightSet
      start (stop - start) W M (Finset.Icc (a - start) (stop - start)) ω)
    (hann : ∀ t ∈ S, h ≤ |t|) :
    (((range N).filter fun j : ℕ => τ ≤ ‖candidateEulerBandRawCovariance
      (Problem520.harperBlockEndpoint stop) ω T B u (v + j * (2 * Real.pi)) S‖).card : ℝ) ≤ b := by
  exact (candidate_rawCovariance_bad_degree_le start stop a ω W h M d u v hT hTB hτ
    N k hS hret hann hω.1).trans
      ((div_le_iff₀ (pow_pos (by positivity : 0 < τ / 2) _)).mpr hω.2)

/-- The cylinder failure probability pays one near and one far Markov bound,
with no row-count union. Both moments are the actual proved random envelopes. -/
theorem candidate_degreeControl_cylinder_failure_le (s : Finset ℕ) (η : s → Bool)
    (start stop a : ℕ) (hst : start ≤ stop) (W h M d : ℝ)
    {T B τ b : ℝ} (hT : 0 < T) (hTB : T ≤ B) (hτ : 0 < τ) (hb : 0 < b)
    (k N : ℕ) :
    (candidateCylinderLaw s η).real
      (candidateCovarianceDegreeControlEvent start stop a W h M T B d k N τ b)ᶜ ≤
      ((∫ ω, candidateEulerBandNearRowEnvelope start stop a W M T B d k N ω ∂Problem520.μ) /
          (b * (τ / 2) ^ (2 * k)) +
        (∫ ω, candidateEulerBandFarMass (Problem520.harperBlockEndpoint stop)
          T B h M d ω ∂Problem520.μ) / (τ / 2)) /
        Problem520.μ.real (candidateCylinder s η) := by
  let nearBad := {ω | b * (τ / 2) ^ (2 * k) ≤
    candidateEulerBandNearRowEnvelope start stop a W M T B d k N ω}
  let farBad := {ω | τ / 2 ≤
    candidateEulerBandFarMass (Problem520.harperBlockEndpoint stop) T B h M d ω}
  have hsub : (candidateCovarianceDegreeControlEvent
      start stop a W h M T B d k N τ b)ᶜ ⊆ nearBad ∪ farBad := by
    intro ω hω
    change ¬ (_ ∧ _) at hω
    by_cases hf : candidateEulerBandFarMass (Problem520.harperBlockEndpoint stop)
        T B h M d ω ≤ τ / 2
    · exact Or.inl (le_of_lt (lt_of_not_ge fun hn => hω ⟨hf, hn⟩))
    · exact Or.inr (le_of_lt (lt_of_not_ge hf))
  have hN := candidate_nearRowEnvelope_cylinder_markov_le s η start stop a hst
    W M T B d k N (b * (τ / 2) ^ (2 * k))
  have hF := candidate_farMass_cylinder_markov_le s η
    (Problem520.harperBlockEndpoint stop) hT hTB h M d (τ / 2)
  have hNp : 0 < b * (τ / 2) ^ (2 * k) := by positivity
  have hFp : 0 < τ / 2 := by positivity
  have hN' := (le_div_iff₀' hNp).mpr hN
  have hF' := (le_div_iff₀' hFp).mpr hF
  change (candidateCylinderLaw s η).real farBad ≤
    (∫ ω, candidateEulerBandFarMass (Problem520.harperBlockEndpoint stop)
      T B h M d ω ∂Problem520.μ) / Problem520.μ.real (candidateCylinder s η) / (τ / 2) at hF'
  apply (measureReal_mono hsub).trans ((measureReal_union_le nearBad farBad).trans
    ((add_le_add hN' hF').trans_eq ?_))
  ring

/-- Numerical cylinder failure bound after inserting the proved near and far
expectation estimates. No analytic moment hypothesis remains. -/
theorem candidate_exists_degreeControl_cylinder_failure_bound :
    ∃ C D F : ℝ, 0 < C ∧ 0 < D ∧ 0 < F ∧ ∃ J : ℕ,
    ∀ k : ℕ, 1 ≤ k → ∀ start stop a : ℕ, J ≤ start → start < a → a ≤ stop →
    ∀ W : ℝ, 1 ≤ W → ∀ h M : ℝ, 0 < h → 0 ≤ M →
      M ≤ candidateCovarianceHeightWindow start / 2 →
    ∀ T B d : ℝ, 0 < T → T ≤ B → 0 < d → ∀ N : ℕ,
    ∀ τ b : ℝ, 0 < τ → 0 < b → ∀ s : Finset ℕ, ∀ η : s → Bool,
    let A := Real.log (Problem520.harperBlockEndpoint start : ℝ)
    let L := Real.log (Problem520.harperBlockEndpoint stop : ℝ)
    let U := A * (2 * M) + 3 * Real.log (1 + L * (2 * M))
    let nearBudget := (4 * k * M + 2) *
      (2 * (Real.log (B / T) + 2) * Real.log (1 + T * d) / T) ^ (2 * k) *
      (((N : ℝ) + 1) * candidateCovarianceReflectedCellBound C D start stop a k W M (2 * k * d) +
        ((1 + (harmonic N : ℝ)) / 2) *
          (candidateCovarianceReflectedCellBound C D start stop a k W M 1 -
            candidateCovarianceReflectedCellBound C D start stop a k W M 0))
    let farBudget := F * Real.sqrt L * Real.sqrt (max A (1 / h)) * Real.sqrt (A + 2 / d) *
      (2 * (Real.log (B / T) + 2) * Real.log (1 + T * (2 * M)) / T) *
      (Real.sqrt (2 * M) * Real.sqrt U)
    (candidateCylinderLaw s η).real
      (candidateCovarianceDegreeControlEvent start stop a W h M T B d k N τ b)ᶜ ≤
      (nearBudget / (b * (τ / 2) ^ (2 * k)) + farBudget / (τ / 2)) /
        Problem520.μ.real (candidateCylinder s η) := by
  obtain ⟨C, D, hC, hD, JN, hnear⟩ := candidate_exists_nearRowEnvelope_moment_bound
  obtain ⟨F, hF, JF, hfar⟩ := candidate_exists_farMass_expectation_bound
  refine ⟨C, D, F, hC, hD, hF, max JN JF, ?_⟩
  intro k hk start stop a hJ hsa has W hW h M hh hM hwindow T B d hT hTB hd N τ b hτ hb s η
  have hN := hnear k hk start stop a ((le_max_left _ _).trans hJ) hsa has W hW M hM
    hwindow T B d hT hTB hd.le N
  have hF' := hfar start stop ((le_max_right _ _).trans hJ) (by omega) h M d T B
    hh hM hd hT hTB (by linarith)
  apply (candidate_degreeControl_cylinder_failure_le s η start stop a (by omega)
    W h M d hT hTB hτ hb k N).trans
  dsimp only at hN hF' ⊢
  apply div_le_div_of_nonneg_right _ measureReal_nonneg
  apply add_le_add
  · exact div_le_div_of_nonneg_right hN (by positivity)
  · exact div_le_div_of_nonneg_right hF' (by positivity)

end
end Erdos.Problem1144
