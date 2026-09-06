import Erdos.Problem1144.HarperCandidateStationaryTailDecay

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace Erdos.Problem1144

/-- The weighted path bound can be tested at the countable set of jump times.
This makes its cap events measurable without a measurable random choice of `K`. -/
theorem candidateWeightedLogBound_iff_nat
    (ω : Omega) {K : ℝ} (hK : 0 ≤ K) :
    CandidateWeightedLogBound ω K ↔ ∀ N : ℕ, 1 ≤ N →
      |squarefreeCriticalSum ω (N - 1)| ≤ K * Real.log (Real.log N + 2) := by
  constructor
  · intro h N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    simpa only [candidateWeightedLogProcess, if_pos hn, Real.exp_log hNpos,
      Nat.floor_natCast] using h (Real.log N) hn
  · intro h t ht
    let N := ⌊Real.exp t⌋₊
    have hN : 1 ≤ N := harperCandidateLogCutoff_pos ht
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    have hnt : Real.log (N : ℝ) ≤ t := by
      have hle := Real.log_le_log hNpos (Nat.floor_le (Real.exp_pos t).le)
      simpa only [Real.log_exp] using hle
    simp only [candidateWeightedLogProcess, if_pos ht]
    change |squarefreeCriticalSum ω (N - 1)| ≤ _
    exact (h N hN).trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by linarith : 0 < Real.log (N : ℝ) + 2)
        (by linarith : Real.log (N : ℝ) + 2 ≤ t + 2)) hK)

/-- Every nonnegative deterministic weighted cap is measurable. -/
theorem measurableSet_candidateWeightedLogBound {K : ℝ} (hK : 0 ≤ K) :
    MeasurableSet {ω | CandidateWeightedLogBound ω K} := by
  simp_rw [candidateWeightedLogBound_iff_nat _ hK]
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro N
  apply MeasurableSet.iInter
  intro hN
  exact measurableSet_le (measurable_squarefreeCriticalSum (N - 1)).abs measurable_const

/-- Enlarging a nonnegative weighted cap preserves the path bound. -/
theorem candidateWeightedLogBound_mono {ω : Omega} {K L : ℝ}
    (hKL : K ≤ L) (h : CandidateWeightedLogBound ω K) :
    CandidateWeightedLogBound ω L := by
  intro t ht
  exact (h t ht).trans (mul_le_mul_of_nonneg_right hKL
    (Real.log_nonneg (by linarith : 1 ≤ t + 2)))

/-- A finite pathwise weighted constant gives cap events whose complements
have probability tending to zero, under any finite law. -/
theorem candidate_weighted_cap_complement_tendsto_zero
    {Q : Measure Omega} [IsFiniteMeasure Q]
    (hR : ∀ᵐ ω ∂Q, ∃ K : ℝ, 0 ≤ K ∧ CandidateWeightedLogBound ω K) :
    Tendsto (fun n : ℕ => Q.real {ω | ¬CandidateWeightedLogBound ω (n : ℝ)})
      atTop (𝓝 0) := by
  let E : ℕ → Set Omega := fun n => {ω | ¬CandidateWeightedLogBound ω (n : ℝ)}
  have hmeas (n : ℕ) : MeasurableSet (E n) :=
    (measurableSet_candidateWeightedLogBound (by positivity : (0 : ℝ) ≤ n)).compl
  have hmono : Antitone E := by
    intro n m hnm ω hω hn
    exact hω (candidateWeightedLogBound_mono (by exact_mod_cast hnm) hn)
  have hnull : Q (⋂ n, E n) = 0 := by
    apply measure_mono_null (t := {ω | ¬∃ K : ℝ, 0 ≤ K ∧ CandidateWeightedLogBound ω K})
      _ (ae_iff.mp hR)
    intro ω hω hK
    obtain ⟨K, hK, hbound⟩ := hK
    obtain ⟨n, hn⟩ := exists_nat_ge K
    exact (mem_iInter.mp hω n) (candidateWeightedLogBound_mono hn hbound)
  have h := tendsto_measure_iInter_atTop
    (μ := Q) (fun n => (hmeas n).nullMeasurableSet) hmono ⟨0, measure_ne_top Q _⟩
  rw [hnull] at h
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

/-- The stationary Gaussian maximum vanishes without a cap event, provided
only that the literal weighted squarefree bound has an almost surely finite
constant. This is the remaining arithmetic premise, not an asserted theorem. -/
theorem candidate_stationary_gaussian_maximum_tendsto_zero_of_ae_weighted_bound
    {Ξ : ℝ → Type*} [∀ T, MeasurableSpace (Ξ T)]
    {P : (T : ℝ) → Measure (Ξ T)} [∀ T, IsProbabilityMeasure (P T)]
    (s : Finset ℕ) (η : s → Bool) {c κ r : ℝ}
    (hc : 0 ≤ c) (hκ : 0 < κ) (hgap : 3 / 2 < c * κ) (hr : 0 < r)
    (hR : ∀ᵐ ω ∂candidateCylinderLaw s η,
      ∃ K : ℝ, 0 ≤ K ∧ CandidateWeightedLogBound ω K)
    (X : (T : ℝ) → Fin (candidateScheduleM κ T) → Omega × Ξ T → ℝ)
    (v : (T : ℝ) → Omega → Fin (candidateScheduleM κ T) → ℝ≥0)
    (hXm : ∀ T i, Measurable (X T i))
    (hX : ∀ T ω i, (P T).map (fun ξ => X T i (ω, ξ)) = gaussianReal 0 (v T ω i))
    (hv : ∀ᶠ T in atTop, ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ i,
      (v T ω i : ℝ) ≤ candidateCompleteStationaryTailVariance ω c T (candidateScheduleW κ T)) :
    Tendsto (fun T : ℝ => ((candidateCylinderLaw s η).prod (P T)).real
      {z | ∃ i, r ≤ |X T i z|}) atTop (𝓝 0) := by
  refine tendsto_order.mpr ⟨fun a ha => Eventually.of_forall fun _ =>
    lt_of_lt_of_le ha measureReal_nonneg, fun ε hε => ?_⟩
  have hcap := candidate_weighted_cap_complement_tendsto_zero hR
  obtain ⟨n, hn⟩ := ((tendsto_order.mp hcap).2 (ε / 2) (by positivity)).exists
  let E : Set Omega := {ω | CandidateWeightedLogBound ω (n : ℝ)}
  have hE : MeasurableSet E := measurableSet_candidateWeightedLogBound (by positivity)
  have hlim := candidate_stationary_gaussian_maximum_tendsto_zero_on_weighted_event
    s η hE hc hκ (by positivity : (0 : ℝ) ≤ n) hgap hr
    (ae_of_all _ fun _ h => h) X v hXm hX hv
  filter_upwards [(tendsto_order.mp hlim).2 (ε / 2) (by positivity)] with T hT
  have hsub : {z : Omega × Ξ T | ∃ i, r ≤ |X T i z|} ⊆
      {z | z.1 ∈ E ∧ ∃ i, r ≤ |X T i z|} ∪ (Eᶜ ×ˢ univ) := by
    intro z hz
    by_cases h : z.1 ∈ E
    · exact Or.inl ⟨h, hz⟩
    · exact Or.inr ⟨h, mem_univ _⟩
  have hbound := (measureReal_mono (μ := (candidateCylinderLaw s η).prod (P T)) hsub).trans
    (measureReal_union_le _ _)
  rw [measureReal_prod_prod, probReal_univ, mul_one] at hbound
  change (candidateCylinderLaw s η).real Eᶜ < ε / 2 at hn
  exact lt_of_le_of_lt hbound (by linarith)

/-- Conditional stationary-extension maxima vanish on the literal grid
under every cylinder, from a single almost sure weighted theorem for the
original law. The covariance comparison and event localization are proved. -/
theorem candidate_stationary_extension_gaussian_maximum_tendsto_zero
    {Ξ : ℝ → Type*} [∀ T, MeasurableSpace (Ξ T)]
    {P : (T : ℝ) → Measure (Ξ T)} [∀ T, IsProbabilityMeasure (P T)]
    (s : Finset ℕ) (η : s → Bool) {c κ r : ℝ}
    (hc : 0 ≤ c) (hκ : 0 < κ) (hgap : 3 / 2 < c * κ) (hr : 0 < r)
    (hR : ∀ᵐ ω ∂mu, ∃ K : ℝ, 0 ≤ K ∧ CandidateWeightedLogBound ω K)
    (u : (T : ℝ) → Fin (candidateScheduleM κ T) → ℝ)
    (hu : ∀ᶠ T in atTop, ∀ i, (1 + c) * T ≤ u T i)
    (X : (T : ℝ) → Fin (candidateScheduleM κ T) → Omega × Ξ T → ℝ)
    (v : (T : ℝ) → Omega → Fin (candidateScheduleM κ T) → ℝ≥0)
    (hXm : ∀ T i, Measurable (X T i))
    (hX : ∀ T ω i, (P T).map (fun ξ => X T i (ω, ξ)) = gaussianReal 0 (v T ω i))
    (hv : ∀ᶠ T in atTop, ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ i,
      (v T ω i : ℝ) ≤ candidateStationaryExtensionCovariance ω (u T) T
        (candidateScheduleW κ T) i i) :
    Tendsto (fun T : ℝ => ((candidateCylinderLaw s η).prod (P T)).real
      {z | ∃ i, r ≤ |X T i z|}) atTop (𝓝 0) := by
  apply candidate_stationary_gaussian_maximum_tendsto_zero_of_ae_weighted_bound
    s η hc hκ hgap hr (ProbabilityTheory.cond_absolutelyContinuous.ae_le hR)
    X v hXm hX
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (candidateScheduleW_tendsto hκ).eventually_gt_atTop 0, hu, hv] with T hT hW huT hvT
  filter_upwards [candidateCylinderLaw_ae_stationaryExtension_diag_le s η hT hW, hvT]
    with ω hdiag hvω
  intro i
  exact (hvω i).trans (hdiag _ (u T) huT i)

end Erdos.Problem1144
