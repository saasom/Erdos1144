import Erdos.Problem1144.HarperCandidatePrimeWhiteComparisonRates

open MeasureTheory ProbabilityTheory Set Matrix Filter
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-- The reverse coupling direction transfers a squarefree prime lower
crossing to white noise with the same literal error budget. -/
theorem candidate_white_prime_selected_crossing_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] (sf : Bool)
    (s : Finset ℕ) (η : s → Bool) (t : ι → ℝ) {T h : ℝ} {n : ℕ}
    (hT : 0 < T) (hh : 0 ≤ h) (hcover : ∀ i, t i ≤ T + (n : ℝ) * h)
    (J : Omega → Finset ι) (hJ : ∀ i, MeasurableSet {ω | i ∈ J ω})
    (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ ω, candidateComparisonPrimeCrossing sf t T h n J (K + 3 * ε) ω
      ∂candidateCylinderLaw s η) ≤
    (∫ ω, candidateComparisonWhiteCrossing sf t T J K ω
      ∂candidateCylinderLaw s η) +
    (∫ ω, candidateComparisonTotalError sf t T h n ω ∂mu) /
      (mu.real (candidateCylinder s η) * ε ^ 2) := by
  let Q := candidateCylinderLaw s η
  let P := fun ω ↦ ∑ i, candidateComparisonPrimeEnergy sf ω (t i) T h n
  let M := fun ω ↦ ∑ i, candidateComparisonMassError sf ω (t i) T h n
  let W := fun ω ↦ ∑ i, candidateComparisonWhiteError sf ω (t i) T h n
  have hP : Integrable P mu := integrable_finset_sum _ fun i _ ↦
    candidate_integrable_comparisonPrimeEnergy sf (t i) T h n
  have hM : Integrable M mu := integrable_finset_sum _ fun i _ ↦
    candidate_integrable_comparisonMassError sf (t i) T h n
  have hW : Integrable W mu := integrable_finset_sum _ fun i _ ↦
    candidate_integrable_comparisonWhiteError sf hT hh (hcover i)
  have hcP := candidateCylinderLaw_integral_nonneg_le s η hP
    (fun ω ↦ Finset.sum_nonneg fun i _ ↦ candidate_comparisonPrimeEnergy_nonneg sf ω (t i) T h n)
  have hcM := candidateCylinderLaw_integral_nonneg_le s η hM
    (fun ω ↦ Finset.sum_nonneg fun i _ ↦ candidate_comparisonMassError_nonneg sf ω (t i) T h n)
  have hcW := candidateCylinderLaw_integral_nonneg_le s η hW
    (fun ω ↦ Finset.sum_nonneg fun i _ ↦ candidate_comparisonWhiteError_nonneg sf ω (t i) T h n)
  have hwrev (ω : Omega) (i : ι) :
      (∫ v, (candidateComparisonWhite sf ω (t i) T v -
        candidateComparisonWhiteStep sf ω (t i) T h n v) ^ 2) =
      candidateComparisonWhiteError sf ω (t i) T h n := by
    apply integral_congr_ae
    filter_upwards [] with v
    exact sub_sq_comm _ _
  have h1 := candidate_integral_gaussian_gram_selected_crossing_le Q Measure.count
    (fun i ω ↦ candidateComparisonPrimeStep sf ω (t i) T h n)
    (fun i ω ↦ candidateComparisonPrime sf ω (t i) T h n)
    (fun i ↦ measurable_candidateComparisonPrimeStep sf (t i) T h n)
    (fun i ↦ measurable_candidateComparisonPrime sf (t i) T h n)
    (fun _ _ ↦ candidate_memLp_finite_count _) (fun _ _ ↦ candidate_memLp_finite_count _)
    J hJ (by simpa only [sub_sq_comm, candidate_comparison_prime_error_eq] using hcP.1) (K + ε + ε) hε
  have h2 := candidate_integral_gaussian_gram_selected_crossing_le Q Measure.count
    (fun i ω ↦ candidateComparisonWhiteBin sf ω (t i) T h n)
    (fun i ω ↦ candidateComparisonMassBin sf ω (t i) T h n)
    (fun i ↦ measurable_candidateComparisonWhiteBin sf (t i) T h n)
    (fun i ↦ measurable_candidateComparisonMassBin sf (t i) T h n)
    (fun _ _ ↦ candidate_memLp_finite_count _) (fun _ _ ↦ candidate_memLp_finite_count _)
    J hJ (by simpa only [sub_sq_comm, candidate_comparison_mass_error_eq] using hcM.1) (K + ε) hε
  have h3 := candidate_integral_gaussian_gram_selected_crossing_le Q volume
    (fun i ω ↦ candidateComparisonWhite sf ω (t i) T)
    (fun i ω ↦ candidateComparisonWhiteStep sf ω (t i) T h n)
    (fun i ↦ measurable_candidateComparisonWhite sf (t i) T)
    (fun i ↦ measurable_candidateComparisonWhiteStep sf (t i) T h n)
    (fun ω i ↦ candidate_memLp_comparisonWhite sf ω (t i) hT)
    (fun ω i ↦ candidate_memLp_comparisonWhiteStep sf ω (t i) T hh n)
    J hJ (by simpa only [hwrev] using hcW.1) K hε
  simp_rw [candidate_comparison_primeStep_gram_eq, sub_sq_comm, candidate_comparison_prime_error_eq] at h1
  simp_rw [candidate_comparison_whiteBin_gram_eq sf _ t T hh n,
    sub_sq_comm, candidate_comparison_mass_error_eq] at h2
  simp_rw [hwrev] at h3
  have hsum : (∫ ω, candidateComparisonTotalError sf t T h n ω ∂mu) =
      (∫ ω, P ω ∂mu) + (∫ ω, M ω ∂mu) + (∫ ω, W ω ∂mu) := by
    simp only [candidateComparisonTotalError, Finset.sum_add_distrib]
    change (∫ ω, (P + M) ω + W ω ∂mu) = _
    rw [integral_add (hP.add hM) hW]
    simp only [Pi.add_apply]
    rw [integral_add hP hM]
  have herr : (∫ ω, P ω ∂Q) / ε ^ 2 + (∫ ω, M ω ∂Q) / ε ^ 2 +
      (∫ ω, W ω ∂Q) / ε ^ 2 ≤
        (∫ ω, candidateComparisonTotalError sf t T h n ω ∂mu) /
          (mu.real (candidateCylinder s η) * ε ^ 2) := by
    rw [hsum]
    have hp := div_le_div_of_nonneg_right hcP.2 (sq_nonneg ε)
    have hm := div_le_div_of_nonneg_right hcM.2 (sq_nonneg ε)
    have hw := div_le_div_of_nonneg_right hcW.2 (sq_nonneg ε)
    simpa only [div_div, ← add_div] using add_le_add (add_le_add hp hm) hw
  have hlevel : K + ε + ε + ε = K + 3 * ε := by ring
  rw [hlevel] at h1
  change (∫ ω, candidateComparisonPrimeCrossing sf t T h n J (K + 3 * ε) ω ∂Q) ≤
    _ + (∫ ω, P ω ∂Q) / ε ^ 2 at h1
  change _ ≤ _ + (∫ ω, M ω ∂Q) / ε ^ 2 at h2
  change _ ≤ (∫ ω, candidateComparisonWhiteCrossing sf t T J K ω ∂Q) +
    (∫ ω, W ω ∂Q) / ε ^ 2 at h3
  linarith

/-- The reverse comparison is uniform over every polynomial-size grid and
measurable selection under each fixed cylinder. -/
theorem candidate_eventually_white_prime_selected_crossing_le
    (sf : Bool) (s : Finset ℕ) (η : s → Bool) (D q : ℝ) {ν ε ρ : ℝ}
    (hD : 0 ≤ D) (hν : 0 < ν) (hνPNT : ν < 1 / 10) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ, ∀ t : Fin m → ℝ,
      (m : ℝ) ≤ T ^ q →
      (n : ℝ) * Real.exp (-(T ^ ν)) ≤ D * T →
      (∀ i, t i - T ≤ D * T) →
      (∀ i, t i ≤ T + (n : ℝ) * Real.exp (-(T ^ ν))) →
      ∀ (J : Omega → Finset (Fin m)), (∀ i, MeasurableSet {ω | i ∈ J ω}) → ∀ K : ℝ,
      (∫ ω, candidateComparisonPrimeCrossing sf t T (Real.exp (-(T ^ ν))) n J (K + 3 * ε) ω
        ∂candidateCylinderLaw s η) ≤
      (∫ ω, candidateComparisonWhiteCrossing sf t T J K ω
        ∂candidateCylinderLaw s η) + ρ := by
  have hp : 0 < mu.real (candidateCylinder s η) :=
    ENNReal.toReal_pos (mu_candidateCylinder_ne_zero s η) (measure_ne_top _ _)
  let B := ρ * (mu.real (candidateCylinder s η) * ε ^ 2)
  have hB : 0 < B := by dsimp only [B]; positivity
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    candidate_eventually_scaled_comparison_error_lt sf D q hD hν hνPNT hB] with T hT he
  intro n m t hm hn ht hc J hJ K
  let h := Real.exp (-(T ^ ν))
  have hh : 0 ≤ h := (Real.exp_pos _).le
  have hr : 0 < T ^ q := Real.rpow_pos_of_pos hT q
  have hbound : (∫ ω, candidateComparisonTotalError sf t T h n ω ∂mu) ≤ B := by
    unfold candidateComparisonTotalError
    have hi (i : Fin m) : Integrable (fun ω ↦
        candidateComparisonPrimeEnergy sf ω (t i) T h n +
        candidateComparisonMassError sf ω (t i) T h n +
        candidateComparisonWhiteError sf ω (t i) T h n) mu :=
      ((candidate_integrable_comparisonPrimeEnergy sf (t i) T h n).add
        (candidate_integrable_comparisonMassError sf (t i) T h n)).add
          (candidate_integrable_comparisonWhiteError sf hT hh (hc i))
    rw [integral_finset_sum _ (fun i _ ↦ hi i)]
    calc
      _ ≤ ∑ _i : Fin m, B / T ^ q := by
        apply Finset.sum_le_sum
        intro i _
        exact (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using (he (t i) n (ht i) hn (hc i)).le)
      _ = (m : ℝ) * (B / T ^ q) := by simp
      _ ≤ T ^ q * (B / T ^ q) := mul_le_mul_of_nonneg_right hm (by positivity)
      _ = B := mul_div_cancel₀ _ hr.ne'
  have hb := candidate_white_prime_selected_crossing_le sf s η t hT hh hc J hJ K hε
  apply hb.trans
  apply add_le_add le_rfl
  apply (div_le_iff₀ (mul_pos hp (sq_pos_of_pos hε))).mpr
  exact hbound

/-- The comparison for the literal upward-rounded whole-bin partition of
`[T, β*T]`. Coverage and the final overshooting bin are discharged here. -/
theorem candidate_eventually_white_prime_ceil_selected_crossing_le
    (sf : Bool) (s : Finset ℕ) (η : s → Bool) (β q : ℝ) {ν ε ρ : ℝ}
    (hβ : 1 ≤ β) (hν : 0 < ν) (hνPNT : ν < 1 / 10) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∀ᶠ T : ℝ in atTop, ∀ m : ℕ, ∀ t : Fin m → ℝ,
      (m : ℝ) ≤ T ^ q → (∀ i, t i ≤ β * T) →
      ∀ (J : Omega → Finset (Fin m)), (∀ i, MeasurableSet {ω | i ∈ J ω}) → ∀ K : ℝ,
      (∫ ω, candidateComparisonPrimeCrossing sf t T (Real.exp (-(T ^ ν)))
        ⌈((β - 1) * T) / Real.exp (-(T ^ ν))⌉₊ J (K + 3 * ε) ω
        ∂candidateCylinderLaw s η) ≤
      (∫ ω, candidateComparisonWhiteCrossing sf t T J K ω ∂candidateCylinderLaw s η) + ρ := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    candidate_eventually_white_prime_selected_crossing_le sf s η β q
      (by linarith) hν hνPNT hε hρ] with T hT he
  intro m t hm ht J hJ K
  have hδ : 0 < Real.exp (-(T ^ ν)) := Real.exp_pos _
  have hδ1 : Real.exp (-(T ^ ν)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (by linarith) _))
  have hc := candidate_macroscopic_ceil_bin_coverage hβ hT hδ hδ1
  exact he _ m t hm hc.2 (fun i ↦ by linarith [ht i])
    (fun i ↦ (ht i).trans hc.1) J hJ K

/-- Squarefree prime lower crossings transfer to the actual white covariance,
with all rounding, normalization and kernel errors discharged. -/
theorem candidate_eventually_white_prime_actual_selected_crossing_le
    (sf : Bool) (s : Finset ℕ) (η : s → Bool) (β q : ℝ) {ν ε ρ : ℝ}
    (hβ : 1 ≤ β) (hν : 0 < ν) (hνPNT : ν < 1 / 10) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∀ᶠ T : ℝ in atTop,
      let δ := Real.exp (-(T ^ ν))
      let n := ⌈((β - 1) * T) / δ⌉₊
      ∀ m : ℕ, ∀ t : Fin m → ℝ,
      (m : ℝ) ≤ T ^ q → (∀ i, t i ≤ β * T) →
      ∀ (J : Omega → Finset (Fin m)), (∀ i, MeasurableSet {ω | i ∈ J ω}) → ∀ K : ℝ,
      (∫ ω, (Measure.pi (fun _ : candidatePrimeWhiteIndex T δ n ↦ gaussianReal 0 1)).real
        {g | ∃ i ∈ J ω, K + 3 * ε < |∑ p : candidatePrimeWhiteIndex T δ n,
          (candidateComparisonProcess sf ω (t i - Real.log (p.2.val : ℝ)) /
            Real.sqrt p.2.val) * g p|} ∂candidateCylinderLaw s η) ≤
      (∫ ω, candidateComparisonWhiteCrossing sf t T J K ω
        ∂candidateCylinderLaw s η) + ρ := by
  filter_upwards [candidate_eventually_white_prime_ceil_selected_crossing_le
    sf s η β q hβ hν hνPNT hε hρ] with T he
  dsimp only
  intro m t hm ht J hJ K
  simpa only [candidate_comparison_prime_crossing_eq_pi] using he m t hm ht J hJ K

end Erdos.Problem1144
