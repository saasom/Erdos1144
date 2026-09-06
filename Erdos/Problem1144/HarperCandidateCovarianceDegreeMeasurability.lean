import Erdos.Problem1144.HarperCandidateCovarianceDegreeControl

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

private theorem measurable_of_prime_agreement (Y : ℕ) (F : Problem520.Omega → ℝ)
    (hF : ∀ ω ω', (∀ p ∈ (Y + 1).primesBelow, ω p = ω' p) → F ω = F ω') :
    Measurable F := by
  classical
  let extend (η : Problem520.HarperPrimeCube Y) : Problem520.Omega :=
    fun p => if hp : p ∈ (Y + 1).primesBelow then η ⟨p, hp⟩ else false
  have he : F = (fun η => F (extend η)) ∘ Problem520.harperPrimeRestriction Y := by
    funext ω
    apply hF
    intro p hp
    simp only [extend, dif_pos hp, Problem520.harperPrimeRestriction]
  rw [he]
  exact (measurable_of_finite _).comp (Problem520.measurable_harperPrimeRestriction Y)

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

/-- Every actual finite-prime row-frequency observable is measurable,
including its random screen restriction and arbitrary scalar frequency weight. -/
theorem candidate_measurable_screened_pairedEuler_frequency_weight
    (start stop a : ℕ) (hst : start ≤ stop) (W M T B d : ℝ)
    (k : ℕ) (F : ℝ → ℝ) :
    Measurable (fun ω =>
      ∫ z, candidateRowProduct (candidateEulerBandRowWeight
          (Problem520.harperBlockEndpoint stop) ω T B) z *
        F (candidateRowPowerFrequency Prod.snd z)
        ∂candidateRowPowerMeasure
          (((volume.restrict (Icc (-M) M)).prod (volume.restrict (Icc (-M) M))).restrict
            (candidateRowPairDomain
              (candidateCovarianceScreenedHeightSet start (stop - start) W M
                (Finset.Icc (a - start) (stop - start)) ω) d)) k) := by
  apply measurable_of_prime_agreement (Problem520.harperBlockEndpoint stop)
  intro ω ω' h
  rw [screenedHeightSet_eq_of_agreement hst W M h, rowWeight_eq_of_agreement h T B]

/-- The existing common near-row envelope is an actual measurable function,
not merely an almost-everywhere measurable representative. -/
theorem candidate_measurable_nearRowEnvelope (start stop a : ℕ) (hst : start ≤ stop)
    (W M T B d : ℝ) (k N : ℕ) :
    Measurable (candidateEulerBandNearRowEnvelope start stop a W M T B d k N) :=
  candidate_measurable_screened_pairedEuler_frequency_weight start stop a hst W M T B d k
    (fun x => ‖candidateRowFourierSum N (-(2 * Real.pi)) x‖)

/-- The literal common near/far degree-control event is measurable, so it
can be intersected directly with the actual retained variance event. -/
theorem candidate_measurableSet_degreeControlEvent (start stop a : ℕ) (hst : start ≤ stop)
    (W h M T B d : ℝ) (k N : ℕ) (τ b : ℝ) :
    MeasurableSet (candidateCovarianceDegreeControlEvent start stop a W h M T B d k N τ b) :=
  (measurableSet_le (candidate_measurable_farMass (Problem520.harperBlockEndpoint stop)
    T B h M d) measurable_const).inter
      (measurableSet_le (candidate_measurable_nearRowEnvelope start stop a hst W M T B d k N)
        measurable_const)

end
end Erdos.Problem1144
