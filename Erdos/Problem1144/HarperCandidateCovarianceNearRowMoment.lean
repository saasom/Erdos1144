import Erdos.Problem1144.HarperCandidateCovarianceNearSublevel
import Erdos.Problem1144.HarperCandidateCovarianceResonanceLayers

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- The actual common nonnegative Fourier bound for every screened near
covariance row. Neither the row endpoint nor the grid origin occurs here. -/
def candidateEulerBandNearRowEnvelope (start stop a : ℕ) (W M T B d : ℝ)
    (k N : ℕ) (ω : Problem520.Omega) : ℝ :=
  ∫ z, candidateRowProduct (candidateEulerBandRowWeight
      (Problem520.harperBlockEndpoint stop) ω T B) z *
      ‖candidateRowFourierSum N (-(2 * Real.pi)) (candidateRowPowerFrequency Prod.snd z)‖
    ∂candidateRowPowerMeasure
      (((volume.restrict (Icc (-M) M)).prod (volume.restrict (Icc (-M) M))).restrict
        (candidateRowPairDomain (candidateCovarianceScreenedHeightSet
          start (stop - start) W M (Finset.Icc (a - start) (stop - start)) ω) d)) k

theorem candidate_integrable_nearRowEnvelope (start stop a : ℕ) (hst : start ≤ stop)
    (W M T B d : ℝ) (k N : ℕ) :
    Integrable (candidateEulerBandNearRowEnvelope start stop a W M T B d k N) Problem520.μ :=
  candidate_integrable_screened_pairedEuler_frequency_weight start stop a hst W M T B d k
    (fun x => ‖candidateRowFourierSum N (-(2 * Real.pi)) x‖)

theorem candidate_nearRowEnvelope_nonneg (start stop a : ℕ) (W M T B d : ℝ)
    (k N : ℕ) (ω : Problem520.Omega) :
    0 ≤ candidateEulerBandNearRowEnvelope start stop a W M T B d k N ω := by
  apply integral_nonneg
  intro z
  dsimp only [candidateRowProduct, candidateEulerBandRowWeight]
  exact mul_nonneg (mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
    (Finset.prod_nonneg fun _ _ => by positivity)) (norm_nonneg _)

/-- The reflected cell budget is affine in its original resonance width. -/
theorem candidate_reflectedCellBound_affine (C D : ℝ) (start stop a k : ℕ)
    (W M η e : ℝ) :
    candidateCovarianceReflectedCellBound C D start stop a k W M (e + η) =
      candidateCovarianceReflectedCellBound C D start stop a k W M η +
        e * (candidateCovarianceReflectedCellBound C D start stop a k W M 1 -
          candidateCovarianceReflectedCellBound C D start stop a k W M 0) := by
  dsimp only [candidateCovarianceReflectedCellBound]
  ring

/-- Averaging the finite resonance layers proves the high moment of the
literal common near-row envelope. The intercept pays the row length;
the width slope pays only its harmonic sum. No sublevel estimate remains
as a hypothesis. -/
theorem candidate_exists_nearRowEnvelope_moment_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ J : ℕ,
    ∀ k : ℕ, 1 ≤ k → ∀ start stop a : ℕ, J ≤ start → start < a → a ≤ stop →
    ∀ W : ℝ, 1 ≤ W → ∀ M : ℝ, 0 ≤ M →
      M ≤ candidateCovarianceHeightWindow start / 2 →
    ∀ T B d : ℝ, 0 < T → T ≤ B → 0 ≤ d → ∀ N : ℕ,
    (∫ ω, candidateEulerBandNearRowEnvelope start stop a W M T B d k N ω ∂Problem520.μ) ≤
      (4 * k * M + 2) *
        (2 * (Real.log (B / T) + 2) * Real.log (1 + T * d) / T) ^ (2 * k) *
        (((N : ℝ) + 1) * candidateCovarianceReflectedCellBound C D start stop a k W M (2 * k * d) +
          ((1 + (harmonic N : ℝ)) / 2) *
            (candidateCovarianceReflectedCellBound C D start stop a k W M 1 -
              candidateCovarianceReflectedCellBound C D start stop a k W M 0)) := by
  obtain ⟨C, D, hC, hD, J, hmass⟩ := candidate_exists_screened_pairedEuler_nearInteger_bound
  refine ⟨C, D, hC, hD, J, ?_⟩
  intro k hk start stop a hJ hsa has W hW M hM hwindow T B d hT hTB hd N
  let Y := Problem520.harperBlockEndpoint stop
  let s := Finset.Icc (a - start) (stop - start)
  let ν (ω : Problem520.Omega) := candidateRowPowerMeasure
    (((volume.restrict (Icc (-M) M)).prod (volume.restrict (Icc (-M) M))).restrict
      (candidateRowPairDomain (candidateCovarianceScreenedHeightSet
        start (stop - start) W M s ω) d)) k
  let f (ω : Problem520.Omega) := candidateRowProduct (k := k) (candidateEulerBandRowWeight Y ω T B)
  let X := fun z : (Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ) => candidateRowPowerFrequency Prod.snd z
  let mass (e : ℝ) (ω : Problem520.Omega) :=
    ∫ z in {z | candidateIntegerDistance (X z) ≤ e}, f ω z ∂ν ω
  let Q := (4 * k * M + 2) *
    (2 * (Real.log (B / T) + 2) * Real.log (1 + T * d) / T) ^ (2 * k)
  let V := candidateCovarianceReflectedCellBound C D start stop a k W M
  let η := 2 * k * d
  let width := fun j : ℕ => 1 / (2 * ((j + 1 : ℕ) : ℝ))
  have hX : Measurable X := by unfold X candidateRowPowerFrequency; fun_prop
  have hfi (ω : Problem520.Omega) : Integrable (f ω) (ν ω) :=
    candidate_integrable_screened_pairedEuler_rowProduct Y ω start (stop - start) W M s d k hT hTB
  have hf0 (ω : Problem520.Omega) (z) : 0 ≤ f ω z := by
    dsimp only [f, candidateRowProduct, candidateEulerBandRowWeight]
    exact mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
      (Finset.prod_nonneg fun _ _ => by positivity)
  have hmi (e : ℝ) : Integrable (mass e) Problem520.μ :=
    candidate_integrable_screened_pairedEuler_nearInteger_mass start stop a (by omega) W M T B d k e
  have hfull (ω : Problem520.Omega) : (∫ z, f ω z ∂ν ω) = mass (1 / 2) ω := by
    have he : {z | candidateIntegerDistance (X z) ≤ 1 / 2} = Set.univ := by
      ext z
      simp only [mem_setOf_eq, mem_univ, iff_true]
      exact candidateIntegerDistance_le_half (X z)
    dsimp only [mass]
    rw [he, Measure.restrict_univ]
  have hpoint (ω : Problem520.Omega) :
      candidateEulerBandNearRowEnvelope start stop a W M T B d k N ω ≤
        mass (1 / 2) ω + ∑ j ∈ range N, mass (width j) ω := by
    have h := candidate_integral_rowFourierSum_le_resonance_layers
      (ν ω) N X hX (f ω) (hfi ω) (hf0 ω)
    rw [hfull] at h
    exact h
  have havg := integral_mono
    (candidate_integrable_nearRowEnvelope start stop a (by omega) W M T B d k N)
    ((hmi (1 / 2)).add (integrable_finset_sum _ fun j _ => hmi (width j))) hpoint
  simp only [Pi.add_apply] at havg
  rw [integral_add (hmi (1 / 2)) (integrable_finset_sum _ fun j _ => hmi (width j)),
    integral_finset_sum _ (fun j _ => hmi (width j))] at havg
  have hb (e : ℝ) (he : 0 ≤ e) (hehalf : e ≤ 1 / 2) :
      (∫ ω, mass e ω ∂Problem520.μ) ≤ Q * (V η + e * (V 1 - V 0)) := by
    have h := hmass k hk start stop a hJ hsa has W hW M hM hwindow T B d hT hTB hd e he hehalf
    rw [candidate_reflectedCellBound_affine] at h
    exact h
  have hwidth (j : ℕ) : 0 ≤ width j ∧ width j ≤ 1 / 2 := by
    dsimp only [width]
    constructor
    · positivity
    · apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j
      linarith
  have hs := Finset.sum_le_sum (s := range N) (fun j _ => hb (width j) (hwidth j).1 (hwidth j).2)
  apply havg.trans ((add_le_add (hb (1 / 2) (by norm_num) le_rfl) hs).trans_eq ?_)
  change Q * (V η + (1 / 2) * (V 1 - V 0)) +
    (∑ j ∈ range N, Q * (V η + width j * (V 1 - V 0))) =
      Q * (((N : ℝ) + 1) * V η + ((1 + (harmonic N : ℝ)) / 2) * (V 1 - V 0))
  have he (j : ℕ) : Q * (V η + width j * (V 1 - V 0)) =
      Q * V η + (Q * (V 1 - V 0) / 2) * (((j + 1 : ℕ) : ℝ)⁻¹) := by
    dsimp only [width]
    ring
  simp only [he, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  ring

end
end Erdos.Problem1144
