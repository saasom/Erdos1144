import Erdos.Problem1144.HarperCandidateCovarianceOrderedMoment
import Erdos.Problem1144.HarperCandidateCovarianceRowContractionEuler
import Erdos.Problem520.HarperTiltedOmega

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

private theorem integrable_of_prime_agreement (Y : ℕ) (F : Problem520.Omega → ℝ)
    (hF : ∀ ω ω', (∀ p ∈ (Y + 1).primesBelow, ω p = ω' p) → F ω = F ω') :
    Integrable F Problem520.μ := by
  classical
  let extend (η : Problem520.HarperPrimeCube Y) : Problem520.Omega :=
    fun p => if hp : p ∈ (Y + 1).primesBelow then η ⟨p, hp⟩ else false
  have he : F = (fun η => F (extend η)) ∘ Problem520.harperPrimeRestriction Y := by
    funext ω
    apply hF
    intro p hp
    simp only [extend, dif_pos hp, Problem520.harperPrimeRestriction]
  rw [he]
  have hmp : MeasurePreserving (Problem520.harperPrimeRestriction Y) Problem520.μ
      (Problem520.harperFairCubeLaw Y) :=
    ⟨Problem520.measurable_harperPrimeRestriction Y, Problem520.map_harperPrimeRestriction_mu Y⟩
  exact hmp.integrable_comp_of_integrable Integrable.of_finite

private theorem density_eq_of_agreement {Y y : ℕ} (hy : y ≤ Y)
    {ω ω' : Problem520.Omega}
    (h : ∀ p ∈ (Y + 1).primesBelow, ω p = ω' p) (t : ℝ) :
    Problem520.harperEulerDensity y ω t = Problem520.harperEulerDensity y ω' t := by
  apply Problem520.harperEulerDensity_eq_of_eq_on_primesBelow
  intro p hp
  apply h p
  apply Nat.mem_primesBelow.mpr
  exact ⟨by have := Nat.lt_of_mem_primesBelow hp; omega,
    Nat.prime_of_mem_primesBelow hp⟩

private theorem screenedHeightSet_eq_of_agreement {start stop a : ℕ}
    (hst : start ≤ stop) (W M : ℝ) {ω ω' : Problem520.Omega}
    (h : ∀ p ∈ (Problem520.harperBlockEndpoint stop + 1).primesBelow, ω p = ω' p) :
    candidateCovarianceScreenedHeightSet start (stop - start) W M
        (Icc (a - start) (stop - start)) ω =
      candidateCovarianceScreenedHeightSet start (stop - start) W M
        (Icc (a - start) (stop - start)) ω' := by
  have he (j : ℕ) (hj : j ≤ stop - start) (t : ℝ) :
      Problem520.harperEulerDensity (Problem520.harperBlockEndpoint (start + j)) ω t =
        Problem520.harperEulerDensity (Problem520.harperBlockEndpoint (start + j)) ω' t :=
    density_eq_of_agreement (Problem520.monotone_harperBlockEndpoint (by omega)) h t
  have hd (t : ℝ) : ω ∈ candidateCovarianceDStarEvent start (stop - start) t W ↔
      ω' ∈ candidateCovarianceDStarEvent start (stop - start) t W := by
    simp only [candidateCovarianceDStarEvent, mem_setOf_eq]
    apply forall_congr'
    intro j
    rw [he j.val (by have := j.isLt; omega) t]
  have hs (t : ℝ) :
      ω ∈ candidateCovarianceStrongScreenEvent start t W (Icc (a - start) (stop - start)) ↔
      ω' ∈ candidateCovarianceStrongScreenEvent start t W (Icc (a - start) (stop - start)) := by
    simp only [candidateCovarianceStrongScreenEvent, mem_setOf_eq]
    apply forall_congr'
    intro j
    apply forall_congr'
    intro hj
    rw [he j (Finset.mem_Icc.mp hj).2 t]
  ext t
  simp only [candidateCovarianceScreenedHeightSet, mem_setOf_eq, hd, hs]

private theorem squaredWeight_eq_of_agreement {Y : ℕ} {ω ω' : Problem520.Omega}
    (h : ∀ p ∈ (Y + 1).primesBelow, ω p = ω' p) :
    candidateEulerBandSquaredWeight Y ω = candidateEulerBandSquaredWeight Y ω' := by
  funext t
  unfold candidateEulerBandSquaredWeight
  rw [density_eq_of_agreement le_rfl h t]

private theorem rowWeight_eq_of_agreement {Y : ℕ} {ω ω' : Problem520.Omega}
    (h : ∀ p ∈ (Y + 1).primesBelow, ω p = ω' p) (T B : ℝ) :
    candidateEulerBandRowWeight Y ω T B = candidateEulerBandRowWeight Y ω' T B := by
  have hn (t : ℝ) : ‖candidateEulerAngularApprox Y 0 ω t‖ =
      ‖candidateEulerAngularApprox Y 0 ω' t‖ := by
    have he := congrFun (squaredWeight_eq_of_agreement h) t
    rw [candidate_eulerBandSquaredWeight_eq_norm_sq,
      candidate_eulerBandSquaredWeight_eq_norm_sq] at he
    have h₁ := norm_nonneg (candidateEulerAngularApprox Y 0 ω t)
    have h₂ := norm_nonneg (candidateEulerAngularApprox Y 0 ω' t)
    nlinarith
  funext z
  simp only [candidateEulerBandRowWeight, hn]

/-- The actual screened squared-density cell is integrable in the prime signs.
All prefix screens, including the terminal prefix, lie in the same finite cube. -/
theorem candidate_integrable_screened_squaredDensity_cell
    (start stop a : ℕ) (hst : start ≤ stop) (W M : ℝ) (k : ℕ) (m : ℤ) (ε : ℝ) :
    Integrable (fun ω =>
      ∫ x in {x | |candidateRowPowerFrequency id x - m| ≤ ε},
        candidateRowProduct (candidateEulerBandSquaredWeight
          (Problem520.harperBlockEndpoint stop) ω) x
        ∂candidateRowPowerMeasure ((volume.restrict (Icc (-M) M)).restrict
          (candidateCovarianceScreenedHeightSet start (stop - start) W M
            (Finset.Icc (a - start) (stop - start)) ω)) k) Problem520.μ := by
  apply integrable_of_prime_agreement (Problem520.harperBlockEndpoint stop)
  intro ω ω' h
  rw [screenedHeightSet_eq_of_agreement hst W M h, squaredWeight_eq_of_agreement h]

/-- The literal paired Euler cell is an integrable random variable, including
its random near-diagonal restriction and every inclusive prefix screen. -/
theorem candidate_integrable_screened_pairedEuler_cell
    (start stop a : ℕ) (hst : start ≤ stop) (W M T B d : ℝ)
    (k : ℕ) (m : ℤ) (ε : ℝ) :
    Integrable (fun ω =>
      ∫ z in {z | |candidateRowPowerFrequency Prod.snd z - m| ≤ ε},
        candidateRowProduct (candidateEulerBandRowWeight
          (Problem520.harperBlockEndpoint stop) ω T B) z
        ∂candidateRowPowerMeasure
          (((volume.restrict (Icc (-M) M)).prod (volume.restrict (Icc (-M) M))).restrict
            (candidateRowPairDomain
              (candidateCovarianceScreenedHeightSet start (stop - start) W M
                (Finset.Icc (a - start) (stop - start)) ω) d)) k) Problem520.μ := by
  apply integrable_of_prime_agreement (Problem520.harperBlockEndpoint stop)
  intro ω ω' h
  rw [screenedHeightSet_eq_of_agreement hst W M h, rowWeight_eq_of_agreement h T B]

/-- Any real functional of the literal row frequency remains integrable in
ω after the screened paired-height integral. No regularity of the functional
is needed: the entire random observable factors through the finite prime cube. -/
theorem candidate_integrable_screened_pairedEuler_frequency_weight
    (start stop a : ℕ) (hst : start ≤ stop) (W M T B d : ℝ)
    (k : ℕ) (F : ℝ → ℝ) :
    Integrable (fun ω =>
      ∫ z, candidateRowProduct (candidateEulerBandRowWeight
          (Problem520.harperBlockEndpoint stop) ω T B) z *
        F (candidateRowPowerFrequency Prod.snd z)
        ∂candidateRowPowerMeasure
          (((volume.restrict (Icc (-M) M)).prod (volume.restrict (Icc (-M) M))).restrict
            (candidateRowPairDomain
              (candidateCovarianceScreenedHeightSet start (stop - start) W M
                (Finset.Icc (a - start) (stop - start)) ω) d)) k) Problem520.μ := by
  apply integrable_of_prime_agreement (Problem520.harperBlockEndpoint stop)
  intro ω ω' h
  rw [screenedHeightSet_eq_of_agreement hst W M h, rowWeight_eq_of_agreement h T B]

/-- The actual screened near-pair measure, rather than an unrestricted
pointwise domain, confines the row frequency to the original `2k`-height window. -/
theorem candidate_ae_screened_pairedEuler_frequency_abs_le
    (start N : ℕ) (W M : ℝ) (s : Finset ℕ) (ω : Problem520.Omega) (d : ℝ) (k : ℕ) :
    ∀ᵐ z ∂candidateRowPowerMeasure
      (((volume.restrict (Icc (-M) M)).prod (volume.restrict (Icc (-M) M))).restrict
        (candidateRowPairDomain
          (candidateCovarianceScreenedHeightSet start N W M s ω) d)) k,
      |candidateRowPowerFrequency Prod.snd z| ≤ (2 * k : ℝ) * M := by
  let S := candidateCovarianceScreenedHeightSet start N W M s ω
  let E := candidateRowPairDomain S d
  let ν := ((volume.restrict (Icc (-M) M)).prod
    (volume.restrict (Icc (-M) M))).restrict E
  have hS : MeasurableSet S := candidate_measurableSet_screenedHeightSet start N W M s ω
  have hν : ∀ᵐ x ∂ν, x ∈ E :=
    ae_restrict_mem (candidate_measurableSet_rowPairDomain hS d)
  have hπ : ∀ᵐ z : Fin k → ℝ × ℝ ∂Measure.pi (fun _ => ν), ∀ i, z i ∈ E :=
    Filter.eventually_all.mpr fun i => Measure.tendsto_eval_ae_ae.eventually hν
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hπ,
    Measure.quasiMeasurePreserving_snd.ae hπ] with z hz₁ hz₂
  have h₁ (i : Fin k) : |(z.1 i).2| ≤ M := (hz₁ i).2.1.1
  have h₂ (i : Fin k) : |(z.2 i).2| ≤ M := (hz₂ i).2.1.1
  change |(∑ i, (z.1 i).2) - ∑ i, (z.2 i).2| ≤ _
  calc
    _ ≤ |∑ i, (z.1 i).2| + |∑ i, (z.2 i).2| := abs_sub _ _
    _ ≤ (∑ i, |(z.1 i).2|) + ∑ i, |(z.2 i).2| :=
      add_le_add (abs_sum_le_sum_abs _ _) (abs_sum_le_sum_abs _ _)
    _ ≤ (∑ _i : Fin k, M) + ∑ _i : Fin k, M :=
      add_le_add (Finset.sum_le_sum fun i _ => h₁ i) (Finset.sum_le_sum fun i _ => h₂ i)
    _ = (2 * k : ℝ) * M := by simp; ring

end
end Erdos.Problem1144
