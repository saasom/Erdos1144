import Erdos.Problem1144.HarperCandidateEnergyHalfMoment
import Erdos.Problem1144.HarperCandidateEnergyCylinder

open MeasureTheory Set

namespace Erdos.Problem1144

/-! An unconditional lower event for the literal squarefree prefix energy,
including every fixed cylinder. The constants come from the proved ballot
half moment; the normalization and finite-coordinate losses are explicit. -/

/-- Removing the half-moment and `2*pi/log y` normalizations gives the exact
raw prefix-energy threshold with coefficient `c^2/(8*pi)`. -/
theorem candidate_halfMomentLargeEvent_subset_prefixEnergy
    {y : ℕ} (hy : 4 ≤ y) {c : ℝ} (hc : 0 ≤ c) :
    halfMomentLargeEvent (harperSquarefreeCoefficientNormalizedEnergy y)
      (c * harperInitialCriticalScale y ^ ((1 : ℝ) / 2)) ⊆
        {ω | (c ^ 2 / (8 * Real.pi)) * Real.log (y : ℝ) *
          harperInitialCriticalScale y ≤ harperSquarefreeCoefficientPrefixEnergy y ω} := by
  intro ω hω
  let K := harperInitialCriticalScale y
  let E := harperSquarefreeCoefficientPrefixEnergy y ω
  let Z := harperSquarefreeCoefficientNormalizedEnergy y ω
  have hK : 0 ≤ K := (harperInitialCriticalScale_pos hy).le
  have hZ : 0 ≤ Z := harperSquarefreeCoefficientNormalizedEnergy_nonneg (by omega) ω
  change c * K ^ ((1 : ℝ) / 2) / 2 ≤ Z ^ ((1 : ℝ) / 2) at hω
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hω
  have hs : (c * Real.sqrt K / 2) ^ 2 ≤ (Real.sqrt Z) ^ 2 :=
    (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg Z)).mpr hω
  rw [div_pow, mul_pow, Real.sq_sqrt hK, Real.sq_sqrt hZ] at hs
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  change c ^ 2 * K / (2 : ℝ) ^ 2 ≤ (2 * Real.pi) * E / Real.log (y : ℝ) at hs
  have hm := (le_div_iff₀ hlog).mp hs
  have hraw : (c ^ 2 * K / (2 : ℝ) ^ 2 * Real.log (y : ℝ)) / (2 * Real.pi) ≤ E :=
    (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)).mpr
      (by simpa only [mul_comm E] using hm)
  change (c ^ 2 / (8 * Real.pi)) * Real.log (y : ℝ) * K ≤ E
  convert hraw using 1 <;> ring

/-- With absolute positive probability, the actual squarefree prefix energy
is at least an absolute positive multiple of `log y * criticalScale y`. -/
theorem candidate_exists_squarefree_prefix_energy_lower_probability :
    ∃ delta : ℝ, 0 < delta ∧ ∃ d : ℝ, 0 < d ∧ ∃ Y : ℕ, 4 ≤ Y ∧
      ∀ y : ℕ, Y ≤ y → delta ≤ mu.real
        {ω | d * Real.log (y : ℝ) * harperInitialCriticalScale y ≤
          harperSquarefreeCoefficientPrefixEnergy y ω} := by
  obtain ⟨delta, hdelta, c, hc, Y, hY⟩ :=
    candidate_exists_squarefreeCoefficientCriticalEnergy_fixedProbability
  refine ⟨delta, hdelta, c ^ 2 / (8 * Real.pi),
    div_pos (sq_pos_of_pos hc) (mul_pos (by norm_num) Real.pi_pos),
    max Y 4, le_max_right _ _, ?_⟩
  intro y hy
  have hy4 : 4 ≤ y := (le_max_right Y 4).trans hy
  have hbase := hY y ((le_max_left Y 4).trans hy)
  change delta ≤ mu.real
    (halfMomentLargeEvent (harperSquarefreeCoefficientNormalizedEnergy y)
      (c * harperInitialCriticalScale y ^ ((1 : ℝ) / 2))) at hbase
  exact hbase.trans (measureReal_mono
    (candidate_halfMomentLargeEvent_subset_prefixEnergy hy4 hc.le))

/-- The lower event persists in every fixed finite cylinder. The probability
and cutoff are universal; the raw floor has exactly the proved `49^|s|`
finite-prefix loss. -/
theorem candidate_exists_squarefree_prefix_energy_lower_probability_cylinder :
    ∃ delta : ℝ, 0 < delta ∧ ∃ d : ℝ, 0 < d ∧ ∃ Y : ℕ, 4 ≤ Y ∧
      ∀ (s : Finset ℕ) (η : s → Bool) (y : ℕ), Y ≤ y →
        delta ≤ (candidateCylinderLaw s η).real
          {ω | (d * Real.log (y : ℝ) * harperInitialCriticalScale y) /
            (49 : ℝ) ^ s.card ≤ harperSquarefreeCoefficientPrefixEnergy y ω} := by
  obtain ⟨delta, hdelta, d, hd, Y, hY4, hY⟩ :=
    candidate_exists_squarefree_prefix_energy_lower_probability
  refine ⟨delta, hdelta, d, hd, Y, hY4, ?_⟩
  intro s η y hy
  exact (hY y hy).trans
    (candidate_squarefree_prefix_energy_cylinder_probability_ge s η
      (by omega : 1 ≤ y) (d * Real.log (y : ℝ) * harperInitialCriticalScale y))

end Erdos.Problem1144
