import Erdos.Problem1144.HarperCandidateCovariancePairedCellMoment
import Erdos.Problem1144.HarperCandidateCovarianceResonanceAveraging

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- The full reflected numerical budget is nonnegative on the actual
nonnegative height, width, and screen parameters. -/
theorem candidate_reflectedCellBound_nonneg (C D : ℝ) (start stop a k : ℕ)
    {W M η : ℝ} (hW : 0 ≤ W) (hM : 0 ≤ M) (hη : 0 ≤ η) :
    0 ≤ candidateCovarianceReflectedCellBound C D start stop a k W M η := by
  have hlog (j : ℕ) : 0 ≤ Real.log (Problem520.harperBlockEndpoint j : ℝ) :=
    (Problem520.one_le_log_harperBlockEndpoint j).trans' (by norm_num)
  have hδ : 0 ≤ Problem520.invLog (Problem520.harperBlockEndpoint (a - 1)) :=
    inv_nonneg.mpr (hlog _)
  have hlogU : 0 ≤ Real.log (1 + Real.log
      (Problem520.harperBlockEndpoint stop : ℝ) * M) :=
    Real.log_nonneg (by have := mul_nonneg (hlog stop) hM; linarith)
  have hf := candidate_gapMomentFactor_nonneg C D start (2 * k)
  have hA := hlog start
  have hL := hlog stop
  dsimp only [candidateCovarianceReflectedCellBound]
  positivity

/-- The literal paired row product is integrable for each fixed realization,
including its random screen and near-diagonal pair restriction. -/
theorem candidate_integrable_screened_pairedEuler_rowProduct (Y : ℕ)
    (ω : Problem520.Omega) (start N : ℕ) (W M : ℝ) (s : Finset ℕ)
    (d : ℝ) (k : ℕ) {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) :
    Integrable (candidateRowProduct (candidateEulerBandRowWeight Y ω T B))
      (candidateRowPowerMeasure
        (((volume.restrict (Icc (-M) M)).prod (volume.restrict (Icc (-M) M))).restrict
          (candidateRowPairDomain
            (candidateCovarianceScreenedHeightSet start N W M s ω) d)) k) := by
  let ν := ((volume.restrict (Icc (-M) M)).prod (volume.restrict (Icc (-M) M))).restrict
    (candidateRowPairDomain (candidateCovarianceScreenedHeightSet start N W M s ω) d)
  have hi : Integrable (candidateEulerBandRowWeight Y ω T B) ν := by
    simpa only [candidate_eulerBandRowAmplitude_norm] using
      (candidate_integrable_eulerBandRowAmplitude Y ω M 0 hT hTB
        (candidateRowPairDomain (candidateCovarianceScreenedHeightSet start N W M s ω) d)).norm
  have hp : Integrable (fun z : Fin k → ℝ × ℝ =>
      ∏ i, candidateEulerBandRowWeight Y ω T B (z i)) (Measure.pi fun _ => ν) :=
    Integrable.fintype_prod fun _ => hi
  exact hp.mul_prod hp

/-- Finite-prime dependence also supplies the outer integrability of the
actual nearest-integer sublevel integral. -/
theorem candidate_integrable_screened_pairedEuler_nearInteger_mass
    (start stop a : ℕ) (hst : start ≤ stop) (W M T B d : ℝ) (k : ℕ) (e : ℝ) :
    Integrable (fun ω =>
      ∫ z in {z | candidateIntegerDistance (candidateRowPowerFrequency Prod.snd z) ≤ e},
        candidateRowProduct (candidateEulerBandRowWeight
          (Problem520.harperBlockEndpoint stop) ω T B) z
        ∂candidateRowPowerMeasure
          (((volume.restrict (Icc (-M) M)).prod (volume.restrict (Icc (-M) M))).restrict
            (candidateRowPairDomain
              (candidateCovarianceScreenedHeightSet start (stop - start) W M
                (Finset.Icc (a - start) (stop - start)) ω) d)) k) Problem520.μ := by
  let X := fun z : (Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ) =>
    candidateRowPowerFrequency Prod.snd z
  have hX : Measurable X := by unfold X candidateRowPowerFrequency; fun_prop
  have hE : MeasurableSet {z | candidateIntegerDistance (X z) ≤ e} :=
    measurableSet_le (candidateIntegerDistance_lipschitz.continuous.measurable.comp hX)
      measurable_const
  have hi := candidate_integrable_screened_pairedEuler_frequency_weight
    start stop a hst W M T B d k (fun t => if candidateIntegerDistance t ≤ e then 1 else 0)
  convert hi using 1
  funext ω
  rw [← integral_indicator hE]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    by_cases hz : candidateIntegerDistance (X z) ≤ e
    · rw [indicator_of_mem (show z ∈ {z | candidateIntegerDistance (X z) ≤ e} from hz)]
      simp only [X] at hz
      simp only [if_pos hz, mul_one]
    · rw [indicator_of_notMem (show z ∉ {z | candidateIntegerDistance (X z) ≤ e} from hz)]
      simp only [X] at hz
      simp only [if_neg hz, mul_zero]

/-- The actual screened near-pair nearest-integer sublevel has a numerical
averaged mass bound. Its label count is derived on the original frequency
support before the partner contraction enlarges the cell width. -/
theorem candidate_exists_screened_pairedEuler_nearInteger_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ J : ℕ,
    ∀ k : ℕ, 1 ≤ k → ∀ start stop a : ℕ, J ≤ start → start < a → a ≤ stop →
    ∀ W : ℝ, 1 ≤ W → ∀ M : ℝ, 0 ≤ M →
      M ≤ candidateCovarianceHeightWindow start / 2 →
    ∀ T B d : ℝ, 0 < T → T ≤ B → 0 ≤ d →
    ∀ e : ℝ, 0 ≤ e → e ≤ 1 / 2 →
    (∫ ω, (∫ z in {z | candidateIntegerDistance
        (candidateRowPowerFrequency Prod.snd z) ≤ e},
      candidateRowProduct (candidateEulerBandRowWeight
        (Problem520.harperBlockEndpoint stop) ω T B) z
      ∂candidateRowPowerMeasure
        (((volume.restrict (Icc (-M) M)).prod (volume.restrict (Icc (-M) M))).restrict
          (candidateRowPairDomain
            (candidateCovarianceScreenedHeightSet start (stop - start) W M
              (Finset.Icc (a - start) (stop - start)) ω) d)) k) ∂Problem520.μ) ≤
      (4 * k * M + 2) *
        (2 * (Real.log (B / T) + 2) * Real.log (1 + T * d) / T) ^ (2 * k) *
        candidateCovarianceReflectedCellBound C D start stop a k W M (e + 2 * k * d) := by
  classical
  obtain ⟨C, D, hC, hD, J, hcell⟩ := candidate_exists_screened_pairedEuler_resonance_bound
  refine ⟨C, D, hC, hD, J, ?_⟩
  intro k hk start stop a hJ hsa has W hW M hM hwindow T B d hT hTB hd e he hehalf
  let Y := Problem520.harperBlockEndpoint stop
  let s := Finset.Icc (a - start) (stop - start)
  let ν (ω : Problem520.Omega) := candidateRowPowerMeasure
    (((volume.restrict (Icc (-M) M)).prod (volume.restrict (Icc (-M) M))).restrict
      (candidateRowPairDomain (candidateCovarianceScreenedHeightSet
        start (stop - start) W M s ω) d)) k
  let f (ω : Problem520.Omega) := candidateRowProduct (k := k) (candidateEulerBandRowWeight Y ω T B)
  let X := fun z : (Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ) =>
    candidateRowPowerFrequency Prod.snd z
  let labels := candidateCovarianceResonanceLabels 1 ((2 * k : ℝ) * M) e
  let cell (m : ℤ) (ω : Problem520.Omega) := ∫ z in {z | |X z - m| ≤ e}, f ω z ∂ν ω
  let R := 2 * (Real.log (B / T) + 2) * Real.log (1 + T * d) / T
  let Q := R ^ (2 * k) *
    candidateCovarianceReflectedCellBound C D start stop a k W M (e + 2 * k * d)
  have hX : Measurable X := by unfold X candidateRowPowerFrequency; fun_prop
  have hfi (ω : Problem520.Omega) : Integrable (f ω) (ν ω) :=
    candidate_integrable_screened_pairedEuler_rowProduct Y ω start (stop - start) W M s d k hT hTB
  have hf0 (ω : Problem520.Omega) (z) : 0 ≤ f ω z := by
    dsimp only [f, candidateRowProduct, candidateEulerBandRowWeight]
    exact mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
      (Finset.prod_nonneg fun _ _ => by positivity)
  have hci (m : ℤ) : Integrable (cell m) Problem520.μ :=
    candidate_integrable_screened_pairedEuler_cell start stop a (by omega) W M T B d k m e
  have hpoint (ω : Problem520.Omega) :
      (∫ z in {z | candidateIntegerDistance (X z) ≤ e}, f ω z ∂ν ω) ≤
        ∑ m ∈ labels, cell m ω :=
    candidate_integral_ae_bounded_resonance_le_sum (ν ω) X hX ((2 * k : ℝ) * M) e
      (candidate_ae_screened_pairedEuler_frequency_abs_le
        start (stop - start) W M s ω d k) (f ω) (hfi ω) (hf0 ω)
  have havg := integral_mono
    (candidate_integrable_screened_pairedEuler_nearInteger_mass
      start stop a (by omega) W M T B d k e)
    (integrable_finset_sum labels fun m _ => hci m) hpoint
  have hbound (m : ℤ) : (∫ ω, cell m ω ∂Problem520.μ) ≤ Q :=
    hcell k hk start stop a hJ hsa has W hW M hM hwindow T B d hT hTB hd e he m
  have hR : 0 ≤ R := (candidateCovarianceLocalKernelMass_nonneg T B d).trans
    (candidate_local_whiteKernel_mass_le hT hTB hd)
  have hQ : 0 ≤ Q := mul_nonneg (pow_nonneg hR _)
    (candidate_reflectedCellBound_nonneg C D start stop a k
      (by linarith) hM (by positivity))
  have hcard : (labels.card : ℝ) ≤ 4 * k * M + 2 := by
    have h := candidate_card_resonanceLabels_le 1 ((2 * k : ℝ) * M) e (by positivity) he
    simp only [Nat.cast_one, one_mul] at h
    dsimp only [labels]
    nlinarith
  apply havg.trans
  rw [integral_finset_sum _ (fun m _ => hci m)]
  calc
    _ ≤ ∑ _m ∈ labels, Q := Finset.sum_le_sum fun m _ => hbound m
    _ = (labels.card : ℝ) * Q := by simp
    _ ≤ (4 * k * M + 2) * Q := mul_le_mul_of_nonneg_right hcard hQ
    _ = _ := by dsimp only [Q]; ring

end
end Erdos.Problem1144
