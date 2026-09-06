import Erdos.Problem1144.HarperCandidatePrimeWhiteComparisonLaws
import Erdos.Problem1144.HarperCandidatePrimeNormalizationRates

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace Erdos.Problem1144

theorem candidate_eventually_scaled_comparisonPrimeEnergy_lt (sf : Bool)
    (D q : ℝ) {ν ε : ℝ} (hD : 0 ≤ D) (hν : 0 < ν) (hνPNT : ν < 1 / 10)
    (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ t : ℝ, ∀ n : ℕ,
      t - T ≤ D * T → (n : ℝ) * Real.exp (-(T ^ ν)) ≤ D * T →
      T ^ q * (∫ ω, candidateComparisonPrimeEnergy sf ω t T (Real.exp (-(T ^ ν))) n ∂mu) < ε := by
  cases sf
  · exact candidate_eventually_scaled_primeStepEnergy_lt D q hD hν hνPNT hε
  · exact candidate_eventually_scaled_squarefreePrimeStepEnergy_lt D q hD hν hνPNT hε

theorem candidate_eventually_scaled_comparisonWhiteError_lt (sf : Bool)
    (D q : ℝ) {ν ε : ℝ} (hD : 0 ≤ D) (hν : 0 < ν) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ t : ℝ, ∀ n : ℕ,
      t - T ≤ D * T → (n : ℝ) * Real.exp (-(T ^ ν)) ≤ D * T →
      t ≤ T + (n : ℝ) * Real.exp (-(T ^ ν)) →
      T ^ q * (∫ ω, candidateComparisonWhiteError sf ω t T (Real.exp (-(T ^ ν))) n ∂mu) < ε := by
  cases sf
  · filter_upwards [eventually_gt_atTop (0 : ℝ),
      candidate_eventually_scaled_whiteStepSquare_lt D q hD hν hε] with T hT h
    intro t n ht hn hc
    change T ^ q * (∫ ω, (∫ x, (candidateCompleteWhiteStepKernel ω t T
      (Real.exp (-(T ^ ν))) n x - candidateCompleteWhiteKernel ω t T x) ^ 2) ∂mu) < ε
    simp_rw [sub_sq_comm, candidate_completeWhiteKernel_step_error_eq _ hT (Real.exp_pos _).le hc]
    exact h t n ht hn
  · filter_upwards [eventually_gt_atTop (0 : ℝ),
      candidate_eventually_scaled_squarefreeWhiteStepSquare_lt D q hD hν hε] with T hT h
    intro t n ht hn hc
    change T ^ q * (∫ ω, (∫ x, (candidateSquarefreeWhiteStepKernel ω t T
      (Real.exp (-(T ^ ν))) n x - candidateSquarefreeWhiteKernel ω t T x) ^ 2) ∂mu) < ε
    simp_rw [sub_sq_comm, candidate_squarefreeWhiteKernel_step_error_eq _ hT (Real.exp_pos _).le hc]
    exact h t n ht hn

theorem candidate_eventually_scaled_comparisonMassError_lt (sf : Bool)
    (D q : ℝ) {ν ε : ℝ} (hD : 0 ≤ D) (hν : ν < 1 / 10) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ t : ℝ, ∀ n : ℕ,
      t - T ≤ D * T → (n : ℝ) * Real.exp (-(T ^ ν)) ≤ D * T →
      T ^ q * (∫ ω, candidateComparisonMassError sf ω t T (Real.exp (-(T ^ ν))) n ∂mu) < ε := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    candidate_eventually_scaled_prime_normalization_sum_lt D q hD hν hε] with T hT he
  intro t n ht hn
  let h := Real.exp (-(T ^ ν))
  have hh : 0 ≤ h := (Real.exp_pos _).le
  have hL : 0 ≤ D * T + 1 := by positivity
  have hb : (∫ ω, candidateComparisonMassError sf ω t T h n ∂mu) ≤
      ∑ j ∈ Finset.range n, (Real.sqrt (candidateComparisonBinMass T h j) - Real.sqrt h) ^ 2 *
        ((2 + D * T) / T) := by
    unfold candidateComparisonMassError
    rw [integral_finset_sum _ (fun j _ ↦
      (candidate_integrable_comparisonEndpoint_sq sf t T h j).const_mul _)]
    simp_rw [integral_const_mul]
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    convert candidate_integral_comparisonEndpoint_sq_le sf hT hh hL
      (show t - T ≤ D * T + 1 by linarith) j using 1 <;> ring
  apply (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hT.le q)).trans_lt
  exact he n hn

/-- The sum of all three actual approximation losses is superpolynomially
small per coordinate. Both complete and squarefree kernels are covered. -/
theorem candidate_eventually_scaled_comparison_error_lt (sf : Bool)
    (D q : ℝ) {ν ε : ℝ} (hD : 0 ≤ D) (hν : 0 < ν) (hνPNT : ν < 1 / 10)
    (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ t : ℝ, ∀ n : ℕ,
      t - T ≤ D * T → (n : ℝ) * Real.exp (-(T ^ ν)) ≤ D * T →
      t ≤ T + (n : ℝ) * Real.exp (-(T ^ ν)) →
      T ^ q * (∫ ω, (candidateComparisonPrimeEnergy sf ω t T (Real.exp (-(T ^ ν))) n +
        candidateComparisonMassError sf ω t T (Real.exp (-(T ^ ν))) n +
        candidateComparisonWhiteError sf ω t T (Real.exp (-(T ^ ν))) n) ∂mu) < ε := by
  have hε3 : 0 < ε / 3 := by positivity
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    candidate_eventually_scaled_comparisonPrimeEnergy_lt sf D q hD hν hνPNT hε3,
    candidate_eventually_scaled_comparisonMassError_lt sf D q hD hνPNT hε3,
    candidate_eventually_scaled_comparisonWhiteError_lt sf D q hD hν hε3] with T hT hP hM hW
  intro t n ht hn hc
  have hiP := candidate_integrable_comparisonPrimeEnergy sf t T (Real.exp (-(T ^ ν))) n
  have hiM := candidate_integrable_comparisonMassError sf t T (Real.exp (-(T ^ ν))) n
  have hiW := candidate_integrable_comparisonWhiteError sf hT (Real.exp_pos _).le hc
  have h1 := hP t n ht hn
  have h2 := hM t n ht hn
  have h3 := hW t n ht hn hc
  have hiPM : Integrable (fun ω ↦ candidateComparisonPrimeEnergy sf ω t T (Real.exp (-(T ^ ν))) n +
      candidateComparisonMassError sf ω t T (Real.exp (-(T ^ ν))) n) mu := hiP.add hiM
  rw [integral_add hiPM hiW, integral_add hiP hiM]
  nlinarith

/-- On every fixed cylinder, the literal prime Gaussian vector dominates
white selected crossings up to an arbitrary fixed probability error and
three fixed threshold margins. Grid sizes may grow as any prescribed power
of `T`; no unproved coupling, covariance or measurability premise remains. -/
theorem candidate_eventually_prime_white_selected_crossing_le
    (sf : Bool) (s : Finset ℕ) (η : s → Bool) (D q : ℝ) {ν ε ρ : ℝ}
    (hD : 0 ≤ D) (hν : 0 < ν) (hνPNT : ν < 1 / 10) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ, ∀ t : Fin m → ℝ,
      (m : ℝ) ≤ T ^ q →
      (n : ℝ) * Real.exp (-(T ^ ν)) ≤ D * T →
      (∀ i, t i - T ≤ D * T) →
      (∀ i, t i ≤ T + (n : ℝ) * Real.exp (-(T ^ ν))) →
      ∀ (J : Omega → Finset (Fin m)), (∀ i, MeasurableSet {ω | i ∈ J ω}) → ∀ K : ℝ,
      (∫ ω, candidateComparisonWhiteCrossing sf t T J (K + 3 * ε) ω
        ∂candidateCylinderLaw s η) ≤
      (∫ ω, candidateComparisonPrimeCrossing sf t T (Real.exp (-(T ^ ν))) n J K ω
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
  have hb := candidate_prime_white_selected_crossing_le sf s η t hT hh hc J hJ K hε
  apply hb.trans
  apply add_le_add le_rfl
  apply (div_le_iff₀ (mul_pos hp (sq_pos_of_pos hε))).mpr
  exact hbound

/-- The comparison for the literal upward-rounded whole-bin partition of
`[T, β*T]`. Coverage and the final overshooting bin are discharged here. -/
theorem candidate_eventually_prime_white_ceil_selected_crossing_le
    (sf : Bool) (s : Finset ℕ) (η : s → Bool) (β q : ℝ) {ν ε ρ : ℝ}
    (hβ : 1 ≤ β) (hν : 0 < ν) (hνPNT : ν < 1 / 10) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∀ᶠ T : ℝ in atTop, ∀ m : ℕ, ∀ t : Fin m → ℝ,
      (m : ℝ) ≤ T ^ q → (∀ i, t i ≤ β * T) →
      ∀ (J : Omega → Finset (Fin m)), (∀ i, MeasurableSet {ω | i ∈ J ω}) → ∀ K : ℝ,
      (∫ ω, candidateComparisonWhiteCrossing sf t T J (K + 3 * ε) ω
        ∂candidateCylinderLaw s η) ≤
      (∫ ω, candidateComparisonPrimeCrossing sf t T (Real.exp (-(T ^ ν)))
        ⌈((β - 1) * T) / Real.exp (-(T ^ ν))⌉₊ J K ω ∂candidateCylinderLaw s η) + ρ := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    candidate_eventually_prime_white_selected_crossing_le sf s η β q
      (by linarith) hν hνPNT hε hρ] with T hT he
  intro m t hm ht J hJ K
  have hδ : 0 < Real.exp (-(T ^ ν)) := Real.exp_pos _
  have hδ1 : Real.exp (-(T ^ ν)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (by linarith) _))
  have hc := candidate_macroscopic_ceil_bin_coverage hβ hT hδ hδ1
  exact he _ m t hm hc.2 (fun i ↦ by linarith [ht i])
    (fun i ↦ (ht i).trans hc.1) J hJ K

/-- The fully identified form: white-noise Gram crossings are bounded by
crossings of the actual independent-prime standard-normal sum. -/
theorem candidate_eventually_prime_white_actual_selected_crossing_le
    (sf : Bool) (s : Finset ℕ) (η : s → Bool) (β q : ℝ) {ν ε ρ : ℝ}
    (hβ : 1 ≤ β) (hν : 0 < ν) (hνPNT : ν < 1 / 10) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∀ᶠ T : ℝ in atTop,
      let δ := Real.exp (-(T ^ ν))
      let n := ⌈((β - 1) * T) / δ⌉₊
      ∀ m : ℕ, ∀ t : Fin m → ℝ,
      (m : ℝ) ≤ T ^ q → (∀ i, t i ≤ β * T) →
      ∀ (J : Omega → Finset (Fin m)), (∀ i, MeasurableSet {ω | i ∈ J ω}) → ∀ K : ℝ,
      (∫ ω, candidateComparisonWhiteCrossing sf t T J (K + 3 * ε) ω
        ∂candidateCylinderLaw s η) ≤
      (∫ ω, (Measure.pi (fun _ : candidatePrimeWhiteIndex T δ n ↦ gaussianReal 0 1)).real
        {g | ∃ i ∈ J ω, K < |∑ p : candidatePrimeWhiteIndex T δ n,
          (candidateComparisonProcess sf ω (t i - Real.log (p.2.val : ℝ)) /
            Real.sqrt p.2.val) * g p|} ∂candidateCylinderLaw s η) + ρ := by
  filter_upwards [candidate_eventually_prime_white_ceil_selected_crossing_le
    sf s η β q hβ hν hνPNT hε hρ] with T he
  dsimp only
  intro m t hm ht J hJ K
  simpa only [candidate_comparison_prime_crossing_eq_pi] using he m t hm ht J hJ K

end Erdos.Problem1144
