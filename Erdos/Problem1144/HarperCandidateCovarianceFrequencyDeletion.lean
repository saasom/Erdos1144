import Erdos.Problem1144.HarperCandidateCovarianceFrequencyMass
import Erdos.Problem1144.HarperCandidateCovarianceMeshDeletion

open Finset MeasureTheory Set
open scoped Topology

namespace Erdos.Problem1144

/-- Frequencies removed from the common upper mesh screen by the two-sided
height screen and the strong interior barrier. -/
def candidateCovarianceFrequencyDeletionGraph (start N : ℕ) (W : ℝ)
    (s : Finset ℕ) : Set (ℝ × Problem520.Omega) :=
  {z | z.2 ∈ candidateCovarianceMeshEvent start N z.1 W \
    (candidateCovarianceDStarEvent start N z.1 W ∩
      candidateCovarianceStrongScreenEvent start z.1 W s)}

theorem candidate_measurableSet_covarianceFrequencyDeletion
    (start N : ℕ) (W : ℝ) (s : Finset ℕ) :
    MeasurableSet (candidateCovarianceFrequencyDeletionGraph start N W s) :=
  (candidate_measurableSet_covarianceMesh_joint start N W).diff
    ((candidate_measurableSet_covarianceDStar_joint start N W).inter
      (candidate_measurableSet_covarianceStrongScreen_joint start W s))

/-- The actual frequency window includes the growing heights and every
central dyadic band down to its displayed lower endpoint. -/
def candidateCovarianceFrequencyWindow (d M : ℕ) : Set ℝ :=
  {t | (1 / 2 : ℝ) ^ (d + 1) < |t| ∧ |t| ≤ (M : ℝ)}

theorem candidate_measurableSet_covarianceFrequencyWindow (d M : ℕ) :
    MeasurableSet (candidateCovarianceFrequencyWindow d M) :=
  (measurableSet_lt measurable_const measurable_id.abs).inter
    (measurableSet_le measurable_id.abs measurable_const)

/-- All numerical losses retained from the literal mesh and ballot
estimates. No asymptotic choice of parameters is built into this budget. -/
noncomputable def candidateCovarianceFrequencyDeletionBudget
    (C W : ℝ) (start N a : ℕ) (s : Finset ℕ) : ℝ :=
  (Real.exp (16 * (1 + (Real.log 4 + 4) / Real.log 2)) + 1) *
      (N + 1 : ℕ) / W ^ 2 +
    (candidateEulerDeletionPrefactor C
      (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 7 * Real.log W)
      (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 1013 * Real.log W) *
      (2 * Real.sqrt (N : ℝ) / (Real.sqrt ((a / 3 : ℕ) : ℝ)) ^ 3) +
      (s.card : ℝ) * (64 * (1 / 2 : ℝ) ^ start))

private theorem prefactor_nonneg {C x r : ℝ} (hC : 0 ≤ C) (hx : 0 ≤ x) (hr : 0 ≤ r) :
    0 ≤ candidateEulerDeletionPrefactor C x r := by
  unfold candidateEulerDeletionPrefactor
  positivity

private theorem prefactor_mono {C D x r : ℝ} (hC : 0 ≤ C) (hCD : C ≤ D)
    (hx : 0 ≤ x) (hr : 0 ≤ r) :
    candidateEulerDeletionPrefactor C x r ≤ candidateEulerDeletionPrefactor D x r := by
  have hD : 0 ≤ D := hC.trans hCD
  unfold candidateEulerDeletionPrefactor
  gcongr <;> positivity

theorem candidate_covarianceFrequencyDeletionBudget_nonneg {C W : ℝ}
    (hC : 0 ≤ C) (hW : 1 ≤ W) (start N a : ℕ) (s : Finset ℕ) :
    0 ≤ candidateCovarianceFrequencyDeletionBudget C W start N a s := by
  have hlogW := Real.log_nonneg hW
  have hlogB := Real.log_nonneg (Problem520.one_le_log_harperBlockEndpoint start)
  have hp := prefactor_nonneg hC (show 0 ≤ Real.log (Real.log
    (Problem520.harperBlockEndpoint start : ℝ)) + 7 * Real.log W by positivity)
    (show 0 ≤ Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) +
      1013 * Real.log W by positivity)
  unfold candidateCovarianceFrequencyDeletionBudget
  positivity

private theorem dyadic_cover (d : ℕ) {x : ℝ}
    (hx : (1 / 2 : ℝ) ^ (d + 1) < x) (hx1 : x ≤ 1) :
    ∃ j ≤ d, (1 / 2 : ℝ) ^ (j + 1) < x ∧ x ≤ (1 / 2 : ℝ) ^ j := by
  induction d with
  | zero => exact ⟨0, le_refl _, hx, by simpa using hx1⟩
  | succ d ih =>
    by_cases h : (1 / 2 : ℝ) ^ (d + 1) < x
    · obtain ⟨j, hj, hlow, hhigh⟩ := ih h
      exact ⟨j, by omega, hlow, hhigh⟩
    · exact ⟨d + 1, le_refl _, hx, le_of_not_gt h⟩

private theorem setIntegral_diff_inter_le (y : ℕ) (t : ℝ)
    {D A B : Set Problem520.Omega} (hD : MeasurableSet D)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫ ω in D \ (A ∩ B), Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
      (∫ ω in D \ A, Problem520.harperEulerDensity y ω t ∂Problem520.μ) +
      (∫ ω in A \ B, Problem520.harperEulerDensity y ω t ∂Problem520.μ) := by
  have hi := Problem520.integrable_harperEulerDensity y t
  rw [← integral_indicator (hD.diff (hA.inter hB)), ← integral_indicator (hD.diff hA),
    ← integral_indicator (hA.diff hB), ← integral_add (hi.indicator (hD.diff hA))
      (hi.indicator (hA.diff hB))]
  apply integral_mono (hi.indicator (hD.diff (hA.inter hB)))
    ((hi.indicator (hD.diff hA)).add (hi.indicator (hA.diff hB)))
  intro ω
  have hn := Problem520.harperEulerDensity_nonneg y ω t
  by_cases hωD : ω ∈ D <;> by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;>
    simp [hωD, hωA, hωB, hn]

/-- Uniform literal weighted deletion throughout the whole frequency
window. Its absolute starting index is independent of the number of bands;
only the displayed band depth must be added to that index. -/
theorem candidate_exists_covarianceFrequencyDeletion_section_le :
    ∃ C ≥ 0, ∃ J : ℕ, ∀ d start M : ℕ, J + d ≤ start →
      (M : ℝ) ≤ candidateCovarianceHeightWindow start →
      ∀ N a : ℕ, 3 ≤ a → ∀ s : Finset ℕ,
      (∀ j ∈ s, a ≤ j ∧ j < N) → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + N) ≤ y →
      ∀ W : ℝ, 1 ≤ W → ∀ t ∈ candidateCovarianceFrequencyWindow d M,
      (∫ ω in {ω | (t, ω) ∈ candidateCovarianceFrequencyDeletionGraph start N W s},
        Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
      Problem520.primeEnergyNormalizer y *
        candidateCovarianceFrequencyDeletionBudget C W start N a s := by
  obtain ⟨Cg, hCg, Jg, hG⟩ := candidate_exists_growingHeight_DStar_deletion_le
  obtain ⟨Cc, hCc, Jc, hK⟩ := candidate_exists_centralBand_DStar_deletion_le
  refine ⟨Cg + Cc, by positivity, max Jg Jc, ?_⟩
  intro d start M hstart hM N a ha s hs y hy W hW t ht
  have hlogW := Real.log_nonneg hW
  have hlogB := Real.log_nonneg (Problem520.one_le_log_harperBlockEndpoint start)
  let x := Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 7 * Real.log W
  let r := Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 1013 * Real.log W
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hmono {c : ℝ} (hc : 0 ≤ c) (hcC : c ≤ Cg + Cc) :
      Problem520.primeEnergyNormalizer y *
        (candidateEulerDeletionPrefactor c x r *
          (2 * Real.sqrt (N : ℝ) / (Real.sqrt ((a / 3 : ℕ) : ℝ)) ^ 3) +
          (s.card : ℝ) * (64 * (1 / 2 : ℝ) ^ start)) ≤
      Problem520.primeEnergyNormalizer y *
        (candidateEulerDeletionPrefactor (Cg + Cc) x r *
          (2 * Real.sqrt (N : ℝ) / (Real.sqrt ((a / 3 : ℕ) : ℝ)) ^ 3) +
          (s.card : ℝ) * (64 * (1 / 2 : ℝ) ^ start)) := by
    apply mul_le_mul_of_nonneg_left _ (Problem520.primeEnergyNormalizer_pos y).le
    exact add_le_add (mul_le_mul_of_nonneg_right (prefactor_mono hc hcC hx hr)
      (by positivity)) (le_refl _)
  have hstrong :
      (∫ ω in candidateCovarianceDStarEvent start N t W \ candidateCovarianceStrongScreenEvent start t W s,
        Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
      Problem520.primeEnergyNormalizer y *
        (candidateEulerDeletionPrefactor (Cg + Cc) x r *
          (2 * Real.sqrt (N : ℝ) / (Real.sqrt ((a / 3 : ℕ) : ℝ)) ^ 3) +
          (s.card : ℝ) * (64 * (1 / 2 : ℝ) ^ start)) := by
    by_cases ht1 : 1 ≤ |t|
    · exact (hG start M (by omega) hM N a ha s hs y hy t ht1 ht.2 W hW).trans
        (hmono hCg (by linarith))
    · obtain ⟨j, hj, hjlo, hjhi⟩ := dyadic_cover d ht.1 (le_of_not_ge ht1)
      exact (hK j start (by omega) N a ha s hs y hy t hjlo hjhi W hW).trans
        (hmono hCc (by linarith))
  have hmesh := candidate_covarianceMesh_DStar_weighted_deletion_le start N y hy t W
    (lt_of_lt_of_le zero_lt_one hW)
  have hp : Measurable (fun ω : Problem520.Omega => (t, ω)) :=
    measurable_const.prodMk measurable_id
  have hm := (candidate_measurableSet_covarianceMesh_joint start N W).preimage hp
  have hd := (candidate_measurableSet_covarianceDStar_joint start N W).preimage hp
  have hb := (candidate_measurableSet_covarianceStrongScreen_joint start W s).preimage hp
  apply (setIntegral_diff_inter_le y t hm hd hb).trans
  have h := add_le_add hmesh hstrong
  convert h using 1 <;> dsimp [candidateCovarianceFrequencyDeletionBudget, x, r] <;> ring

/-- The integrated Euler-frequency loss for the literal mesh-to-strong
screen, with the exact angular Fourier Cauchy weight. -/
theorem candidate_exists_covarianceFrequencyDeletion_integral_le :
    ∃ C ≥ 0, ∃ J : ℕ, ∀ d start M : ℕ, J + d ≤ start →
      (M : ℝ) ≤ candidateCovarianceHeightWindow start →
      ∀ N a : ℕ, 3 ≤ a → ∀ s : Finset ℕ,
      (∀ j ∈ s, a ≤ j ∧ j < N) → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + N) ≤ y →
      ∀ W : ℝ, 1 ≤ W →
      (∫ ω, candidateEulerFrequencyMass y (candidateCovarianceFrequencyWindow d M)
        (candidateCovarianceFrequencyDeletionGraph start N W s) ω ∂Problem520.μ) ≤
      2 * Real.pi * Problem520.primeEnergyNormalizer y *
        candidateCovarianceFrequencyDeletionBudget C W start N a s := by
  obtain ⟨C, hC, J, hJ⟩ := candidate_exists_covarianceFrequencyDeletion_section_le
  refine ⟨C, hC, J, ?_⟩
  intro d start M hstart hM N a ha s hs y hy W hW
  have h := candidate_integral_eulerFrequencyMass_le y
    (candidate_measurableSet_covarianceFrequencyWindow d M)
    (candidate_measurableSet_covarianceFrequencyDeletion start N W s)
    (mul_nonneg (Problem520.primeEnergyNormalizer_pos y).le
      (candidate_covarianceFrequencyDeletionBudget_nonneg hC hW start N a s))
    (hJ d start M hstart hM N a ha s hs y hy W hW)
  convert h using 1 <;> ring

end Erdos.Problem1144
