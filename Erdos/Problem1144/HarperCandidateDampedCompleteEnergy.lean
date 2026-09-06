import Erdos.Problem1144.HarperCandidateStationaryTailGaussian

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Erdos.Problem1144

/-- The damped integrated energy of the literal complete normalized process. -/
noncomputable def candidateDampedCompleteEnergy (σ : ℝ) (ω : Omega) : ℝ :=
  σ * ∫ t in Ioi (0 : ℝ), Real.exp (-2 * σ * t) * harperCandidateLogProcess ω t ^ 2

theorem measurable_candidateDampedCompleteEnergy (σ : ℝ) :
    Measurable (candidateDampedCompleteEnergy σ) := by
  have hm : Measurable fun z : Omega × ℝ =>
      Real.exp (-2 * σ * z.2) * harperCandidateLogProcess z.1 z.2 ^ 2 :=
    (by fun_prop : Measurable fun z : Omega × ℝ => Real.exp (-2 * σ * z.2)).mul
      (measurable_harperCandidateLogProcess.pow_const 2)
  exact measurable_const.mul (StronglyMeasurable.integral_prod_right
    hm.stronglyMeasurable (ν := volume.restrict (Ioi (0 : ℝ)))).measurable

theorem candidateDampedCompleteEnergy_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (ω : Omega) :
    0 ≤ candidateDampedCompleteEnergy σ ω := by
  exact mul_nonneg hσ (integral_nonneg fun _ => by positivity)

/-- Remove half the exponential at the omitted interval's lower endpoint.
The remaining integral is the literal damped complete energy. -/
theorem candidateCylinderLaw_ae_stationaryTailVariance_le_dampedEnergy
    (s : Finset ℕ) (η : s → Bool) {c T W : ℝ}
    (hc : 0 ≤ c) (hT : 0 < T) (hW : 0 < W) :
    ∀ᵐ ω ∂candidateCylinderLaw s η,
      candidateCompleteStationaryTailVariance ω c T W ≤
        (2 * Real.exp (-c * W) / W) * candidateDampedCompleteEnergy (W / (2 * T)) ω := by
  have hhalf : 0 < W / (2 * T) := by positivity
  filter_upwards [candidateCylinderLaw_ae_damped_L1_L2 s η (div_pos hW hT),
    candidateCylinderLaw_ae_damped_L1_L2 s η hhalf] with ω hfull hhalfpath
  have hf : Integrable (fun t => Real.exp (-2 * W * t / T) *
      harperCandidateLogProcess ω t ^ 2) := by
    have h := hfull.1.2.integrable_sq
    convert h using 1
    funext t
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  have hh : Integrable (fun t => Real.exp (-W * t / T) *
      harperCandidateLogProcess ω t ^ 2) := by
    have h := hhalfpath.1.2.integrable_sq
    convert h using 1
    funext t
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  have hbound : ∀ t ∈ Ioi (c * T),
      Real.exp (-2 * W * t / T) * harperCandidateLogProcess ω t ^ 2 ≤
        Real.exp (-c * W) * (Real.exp (-W * t / T) * harperCandidateLogProcess ω t ^ 2) := by
    intro t ht
    have hct : c ≤ t / T := (le_div_iff₀ hT).mpr ht.le
    have hx : -2 * W * t / T ≤ -c * W + -W * t / T := by
      have h := mul_le_mul_of_nonneg_left hct hW.le
      linear_combination h
    have he := Real.exp_le_exp.mpr hx
    rw [Real.exp_add] at he
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right he
      (sq_nonneg (harperCandidateLogProcess ω t))
  have hi := setIntegral_mono_on hf.integrableOn
    (hh.const_mul (Real.exp (-c * W))).integrableOn measurableSet_Ioi hbound
  rw [integral_const_mul] at hi
  have hsub : Ioi (c * T) ⊆ Ioi (0 : ℝ) :=
    Ioi_subset_Ioi (mul_nonneg hc hT.le)
  have hregion := setIntegral_mono_set hh.integrableOn
    (ae_of_all _ fun _ => by positivity) hsub.eventuallyLE
  have htotal := hi.trans (mul_le_mul_of_nonneg_left hregion (Real.exp_pos _).le)
  have hscaled := mul_le_mul_of_nonneg_left htotal (by positivity : 0 ≤ 1 / T)
  unfold candidateCompleteStationaryTailVariance candidateDampedCompleteEnergy
  have hexp (t : ℝ) : -2 * (W / (2 * T)) * t = -W * t / T := by ring
  simp_rw [hexp]
  convert hscaled using 1
  field_simp

/-- A cap on the actual integrated energy controls the omitted Gaussian
maximum under every fixed cylinder, without a pathwise weighted-sum bound. -/
theorem candidate_stationary_gaussian_maximum_on_energy_cap_le
    {Ξ ι : Type*} [MeasurableSpace Ξ] [Fintype ι] [Nonempty ι]
    {P : Measure Ξ} [IsProbabilityMeasure P]
    (s : Finset ℕ) (η : s → Bool) {c T W M r : ℝ}
    (hc : 0 ≤ c) (hT : 0 < T) (hW : 0 < W) (hM : 0 ≤ M) (hr : 0 < r)
    {X : ι → Omega × Ξ → ℝ} {v : Omega → ι → ℝ≥0}
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ ω i, P.map (fun ξ => X i (ω, ξ)) = gaussianReal 0 (v ω i))
    (hv : ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ i,
      (v ω i : ℝ) ≤ candidateCompleteStationaryTailVariance ω c T W) :
    ((candidateCylinderLaw s η).prod P).real
      {z | candidateDampedCompleteEnergy (W / (2 * T)) z.1 ≤ M ∧
        ∃ i, r ≤ |X i z|} ≤
      4 * Real.log (2 * Fintype.card ι) * (2 * Real.exp (-c * W) / W * M) / r ^ 2 +
        1 / (2 * Fintype.card ι) := by
  have hE : MeasurableSet {ω | candidateDampedCompleteEnergy (W / (2 * T)) ω ≤ M} :=
    measurableSet_le (measurable_candidateDampedCompleteEnergy _) measurable_const
  have h := candidate_gaussian_maximum_on_event_le hE hXm hX
    (V := fun _ => 0) (A := 2 * Real.exp (-c * W) / W * M)
    (by positivity) (fun _ => le_rfl) (integrable_const 0)
    (by
      filter_upwards [hv,
        candidateCylinderLaw_ae_stationaryTailVariance_le_dampedEnergy s η hc hT hW]
        with ω hω htail
      intro hcap i
      exact (hω i).trans (htail.trans (by
        simpa using mul_le_mul_of_nonneg_left hcap
          (by positivity : 0 ≤ 2 * Real.exp (-c * W) / W)))) hr
  simpa using h

/-- Fractional moments control the actual integrated-energy cap failure. -/
theorem candidate_dampedEnergy_cap_probability_le
    {Q : Measure Omega} [IsProbabilityMeasure Q] {σ q M : ℝ}
    (hσ : 0 ≤ σ) (hq : 0 < q) (hM : 0 < M)
    (hi : Integrable (fun ω => candidateDampedCompleteEnergy σ ω ^ q) Q) :
    Q.real {ω | M < candidateDampedCompleteEnergy σ ω} ≤
      (∫ ω, candidateDampedCompleteEnergy σ ω ^ q ∂Q) / M ^ q := by
  have hMp : 0 < M ^ q := Real.rpow_pos_of_pos hM q
  have h := (hi.div_const (M ^ q)).measure_le_integral
    (ae_of_all _ fun ω => div_nonneg
      (Real.rpow_nonneg (candidateDampedCompleteEnergy_nonneg hσ ω) _) hMp.le)
    (s := {ω | M < candidateDampedCompleteEnergy σ ω})
    (fun ω hω => (one_le_div hMp).mpr (Real.rpow_le_rpow hM.le hω.le hq.le))
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (integral_nonneg fun ω => div_nonneg
    (Real.rpow_nonneg (candidateDampedCompleteEnergy_nonneg hσ ω) _) hMp.le),
    integral_div] at hreal
  exact hreal

/-- A fractional moment of damped complete energy replaces the pathwise
weighted bound in the actual stationary Gaussian error estimate. -/
theorem candidate_stationary_gaussian_maximum_le_energy_moment
    {Ξ ι : Type*} [MeasurableSpace Ξ] [Fintype ι] [Nonempty ι]
    {P : Measure Ξ} [IsProbabilityMeasure P]
    (s : Finset ℕ) (η : s → Bool) {c T W M q r : ℝ}
    (hc : 0 ≤ c) (hT : 0 < T) (hW : 0 < W) (hM : 0 < M) (hq : 0 < q) (hr : 0 < r)
    {X : ι → Omega × Ξ → ℝ} {v : Omega → ι → ℝ≥0}
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ ω i, P.map (fun ξ => X i (ω, ξ)) = gaussianReal 0 (v ω i))
    (hv : ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ i,
      (v ω i : ℝ) ≤ candidateCompleteStationaryTailVariance ω c T W)
    (hi : Integrable (fun ω => candidateDampedCompleteEnergy (W / (2 * T)) ω ^ q)
      (candidateCylinderLaw s η)) :
    ((candidateCylinderLaw s η).prod P).real {z | ∃ i, r ≤ |X i z|} ≤
      4 * Real.log (2 * Fintype.card ι) * (2 * Real.exp (-c * W) / W * M) / r ^ 2 +
        1 / (2 * Fintype.card ι) +
        (∫ ω, candidateDampedCompleteEnergy (W / (2 * T)) ω ^ q
          ∂candidateCylinderLaw s η) / M ^ q := by
  have hcap := candidate_stationary_gaussian_maximum_on_energy_cap_le
    s η hc hT hW hM.le hr hXm hX hv
  have hmark := candidate_dampedEnergy_cap_probability_le (by positivity) hq hM hi
  have hsub : {z : Omega × Ξ | ∃ i, r ≤ |X i z|} ⊆
      {z | candidateDampedCompleteEnergy (W / (2 * T)) z.1 ≤ M ∧ ∃ i, r ≤ |X i z|} ∪
      ({ω | M < candidateDampedCompleteEnergy (W / (2 * T)) ω} ×ˢ (univ : Set Ξ)) := by
    intro z hz
    by_cases h : candidateDampedCompleteEnergy (W / (2 * T)) z.1 ≤ M
    · exact Or.inl ⟨h, hz⟩
    · exact Or.inr ⟨lt_of_not_ge h, mem_univ _⟩
  have h := (measureReal_mono (μ := (candidateCylinderLaw s η).prod P) hsub).trans
    (measureReal_union_le _ _)
  rw [measureReal_prod_prod, probReal_univ, mul_one] at h
  exact h.trans (add_le_add hcap hmark)

end Erdos.Problem1144
