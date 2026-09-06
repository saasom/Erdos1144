import Erdos.Problem1144.HarperThresholdSelector
import Mathlib.Analysis.Convex.Integral

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-- The real-valued number of large-prime threshold exceedances in a block. -/
noncomputable def thresholdExceedanceCountReal
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (j : ℕ) (omega : Omega) : ℝ :=
  ((largePrimeExceedanceSet testSet cut M buffer omega j).card : ℝ)

/-- A second-moment one-sided lower-tail bound.

If a real random variable has mean at least `m > 0`, then the event that it
falls below `m / 2` is controlled by the centered second moment. This is the
Chebyshev step behind the finite exceedance abundance lemma. -/
theorem measure_lt_half_mean_le_centered_second
    (R : Omega → ℝ) (m V : ℝ)
    (hm : 0 < m)
    (hsecond_int :
      Integrable (fun omega => (R omega - ∫ omega, R omega ∂mu) ^ 2) mu)
    (hmean : m ≤ ∫ omega, R omega ∂mu)
    (hsecond :
      (∫ omega, (R omega - ∫ omega, R omega ∂mu) ^ 2 ∂mu) ≤ V) :
    mu {omega | R omega < m / 2} ≤ ENNReal.ofReal (4 * V / m ^ 2) := by
  let E : Set Omega := {omega | R omega < m / 2}
  let T : Set Omega :=
    {omega | (m / 2) ^ 2 ≤ (R omega - ∫ omega, R omega ∂mu) ^ 2}
  have hhalf_pos : 0 < m / 2 := by linarith
  have hsubset : E ⊆ T := by
    intro omega hR
    change R omega < m / 2 at hR
    have hmean_minus : m / 2 ≤ (∫ omega, R omega ∂mu) - R omega := by
      linarith
    have hleabs : m / 2 ≤ |R omega - ∫ omega, R omega ∂mu| := by
      calc
        m / 2 ≤ (∫ omega, R omega ∂mu) - R omega := hmean_minus
        _ ≤ |(∫ omega, R omega ∂mu) - R omega| := le_abs_self _
        _ = |R omega - ∫ omega, R omega ∂mu| := by rw [abs_sub_comm]
    have hpowabs :
        (m / 2) ^ 2 ≤ |R omega - ∫ omega, R omega ∂mu| ^ 2 :=
      pow_le_pow_left₀ hhalf_pos.le hleabs 2
    rw [← abs_pow] at hpowabs
    simpa [T,
      abs_of_nonneg
        (by positivity :
          0 ≤ (R omega - ∫ omega, R omega ∂mu) ^ 2)] using hpowabs
  have hnonneg :
      0 ≤ᵐ[mu] fun omega => (R omega - ∫ omega, R omega ∂mu) ^ 2 :=
    ae_of_all _ fun omega => by positivity
  have hmarkov :=
    mul_meas_ge_le_integral_of_nonneg (μ := mu)
      (f := fun omega => (R omega - ∫ omega, R omega ∂mu) ^ 2)
      hnonneg hsecond_int ((m / 2) ^ 2)
  have hTreal : mu.real T ≤ 4 * V / m ^ 2 := by
    have hmul : (m / 2) ^ 2 * mu.real T ≤ V :=
      le_trans hmarkov hsecond
    have hdiv : mu.real T ≤ V / ((m / 2) ^ 2) := by
      rw [le_div_iff₀ (pow_pos hhalf_pos 2)]
      exact by simpa [mul_comm] using hmul
    have heq : V / ((m / 2) ^ 2) = 4 * V / m ^ 2 := by
      field_simp [hm.ne']
      ring
    simpa [heq] using hdiv
  have hEreal : mu.real E ≤ 4 * V / m ^ 2 :=
    (measureReal_mono hsubset).trans hTreal
  rw [← ofReal_measureReal (μ := mu) (s := E)]
  exact ENNReal.ofReal_le_ofReal hEreal

/-- A moment-abundance certificate for the threshold-selector route.

This replaces the raw `fewExceedances` probability field by a finite
second-moment abundance input for the count of large-prime threshold
exceedances. The remaining analytic work is to prove the mean and centered
second-moment estimates from one- and two-point tail bounds. -/
structure HarperThresholdAbundanceCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  cut : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  testSet : ℕ → Finset ℕ
  good : ℕ → Set Omega
  r : ℕ → ℕ
  failGood : ℕ → ℝ≥0∞
  failOverlap : ℕ → ℝ≥0∞
  countMean : ℕ → ℝ
  countSecond : ℕ → ℝ
  r_pos : ∀ j, 0 < r j
  countMean_pos : ∀ j, 0 < countMean j
  r_le_half_countMean : ∀ j, (r j : ℝ) ≤ countMean j / 2
  testSet_in_block :
    ∀ j N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j)
  testSet_in_range :
    ∀ j N, N ∈ testSet j → N + 1 < (cut j) ^ 2
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  count_centered_second_integrable :
    ∀ j,
      Integrable
        (fun omega =>
          (thresholdExceedanceCountReal testSet cut M buffer j omega -
            ∫ omega',
              thresholdExceedanceCountReal testSet cut M buffer j omega' ∂mu) ^ 2)
        mu
  count_mean_lower :
    ∀ j,
      countMean j ≤
        ∫ omega, thresholdExceedanceCountReal testSet cut M buffer j omega ∂mu
  count_centered_second_upper :
    ∀ j,
      (∫ omega,
          (thresholdExceedanceCountReal testSet cut M buffer j omega -
            ∫ omega',
              thresholdExceedanceCountReal testSet cut M buffer j omega' ∂mu) ^ 2 ∂mu)
        ≤ countSecond j
  fail_summable :
    (∑' j,
      (failGood j +
        ENNReal.ofReal (4 * countSecond j / countMean j ^ 2) +
        failOverlap j)) ≠ ⊤
  prob_good_compl :
    ∀ j, mu (good j)ᶜ ≤ failGood j
  prob_overlap_many :
    ∀ j,
      mu (thresholdSmoothOverlapMany testSet cut M buffer r j) ≤
        failOverlap j

/-- Moment-abundance certificates imply the threshold-selector block
certificate. -/
noncomputable def harperThresholdSelectorBlockCertificate_of_abundance
    (h : HarperThresholdAbundanceCertificate) :
    HarperThresholdSelectorBlockCertificate where
  lo := h.lo
  hi := h.hi
  cut := h.cut
  M := h.M
  buffer := h.buffer
  testSet := h.testSet
  good := h.good
  r := h.r
  failGood := h.failGood
  failFew := fun j =>
    ENNReal.ofReal (4 * h.countSecond j / h.countMean j ^ 2)
  failOverlap := h.failOverlap
  r_pos := h.r_pos
  testSet_in_block := h.testSet_in_block
  testSet_in_range := h.testSet_in_range
  lo_tendsto_atTop := h.lo_tendsto_atTop
  M_tendsto_atTop := h.M_tendsto_atTop
  fail_summable := h.fail_summable
  prob_good_compl := h.prob_good_compl
  prob_few_exceedances := by
    intro j
    let R : Omega → ℝ :=
      thresholdExceedanceCountReal h.testSet h.cut h.M h.buffer j
    let few : Set Omega :=
      thresholdFewExceedances h.testSet h.cut h.M h.buffer h.r j
    have hfew_subset :
        h.good j ∩ few ⊆ {omega | R omega < h.countMean j / 2} := by
      intro omega homega
      rcases homega with ⟨_, hfew⟩
      have hcard_lt :
          ((largePrimeExceedanceSet h.testSet h.cut h.M h.buffer omega j).card : ℝ)
            < (h.r j : ℝ) :=
        Nat.cast_lt.mpr hfew
      have hRdef :
          R omega =
            ((largePrimeExceedanceSet h.testSet h.cut h.M h.buffer omega j).card : ℝ) :=
        rfl
      change R omega < h.countMean j / 2
      rw [hRdef]
      exact lt_of_lt_of_le hcard_lt (h.r_le_half_countMean j)
    calc
      mu (h.good j ∩ few)
          ≤ mu {omega | R omega < h.countMean j / 2} :=
            measure_mono hfew_subset
      _ ≤ ENNReal.ofReal
            (4 * h.countSecond j / h.countMean j ^ 2) := by
            exact measure_lt_half_mean_le_centered_second
              (R := R) (m := h.countMean j) (V := h.countSecond j)
              (h.countMean_pos j)
              (by simpa [R] using h.count_centered_second_integrable j)
              (by simpa [R] using h.count_mean_lower j)
              (by simpa [R] using h.count_centered_second_upper j)
  prob_overlap_many := h.prob_overlap_many

/-- Moment-abundance certificates imply the active positive-block
certificate. -/
noncomputable def positiveBlockOmega_of_harperThresholdAbundanceCertificate
    (h : HarperThresholdAbundanceCertificate) :
    PositiveBlockOmega :=
  positiveBlockOmega_of_harperThresholdSelectorBlockCertificate
    (harperThresholdSelectorBlockCertificate_of_abundance h)

/-- Direct closure from the moment-abundance threshold-selector certificate. -/
theorem erdos1144_of_harperThresholdAbundanceCertificate
    (h : HarperThresholdAbundanceCertificate) :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    (positiveBlockOmega_of_harperThresholdAbundanceCertificate h)

end Problem1144
end Erdos
