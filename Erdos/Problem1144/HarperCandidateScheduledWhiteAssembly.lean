import Erdos.Problem1144.HarperCandidateScheduledPrimeLaw

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Erdos.Problem1144

private theorem integrable_selected_linear_crossing_pair {n m : ℕ}
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (a : Omega → Fin n → Fin m → ℝ) (J : Omega → Finset (Fin m))
    (ha : ∀ p i, Measurable fun ω => a ω p i)
    (hJ : ∀ i, MeasurableSet {ω | i ∈ J ω}) (K : ℝ) :
    Integrable (fun ω => (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
      {g | ∃ i ∈ J ω, K < |∑ p, a ω p i * g p|}) Q ∧
    Integrable (fun ω => (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
      {g | ∃ i ∈ J ω, K ≤ |∑ p, a ω p i * g p|}) Q := by
  have hf (i : Fin m) : Measurable fun z : Omega × (Fin n → ℝ) =>
      |∑ p, a z.1 p i * z.2 p| := by
    apply Measurable.abs
    apply Finset.measurable_sum
    intro p _
    exact ((ha p i).comp measurable_fst).mul ((measurable_pi_apply p).comp measurable_snd)
  have hlt : MeasurableSet {z : Omega × (Fin n → ℝ) |
      ∃ i ∈ J z.1, K < |∑ p, a z.1 p i * z.2 p|} := by
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    exact ((hJ i).preimage measurable_fst).inter (measurableSet_lt measurable_const (hf i))
  have hle : MeasurableSet {z : Omega × (Fin n → ℝ) |
      ∃ i ∈ J z.1, K ≤ |∑ p, a z.1 p i * z.2 p|} := by
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    exact ((hJ i).preimage measurable_fst).inter (measurableSet_le measurable_const (hf i))
  exact ⟨Measure.integrable_measure_prodMk_left hlt (by finiteness),
    Measure.integrable_measure_prodMk_left hle (by finiteness)⟩

/-- The actual complete white law transfers to the scheduled fresh Gaussian
field, uniformly over blocks, shifts, measurable selectors and thresholds.
All prime-bin, prefix-floor and finite-noise identifications are discharged. -/
theorem candidateSchedule_completeWhite_fresh_selected_crossing
    {α β κ : ℝ} (hαβ : α ≤ β) (hβ : 1 ≤ β) (hκ : 0 < κ)
    (s : Finset ℕ) (η : s → Bool) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ k < candidateScheduleN α β κ T,
      ∀ shift ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ∀ (J : Omega → Finset (Fin (candidateScheduleM κ T))),
      (∀ i, MeasurableSet {ω | i ∈ J ω}) → ∀ K : ℝ,
      (∫ ω, candidateComparisonWhiteCrossing false
        (fun i : Fin (candidateScheduleM κ T) => candidateSchedulePoint α κ T k i shift)
        T J (K + 3 * ε) ω ∂candidateCylinderLaw s η) ≤
      (∫ ω, (Measure.pi
        (fun _ : Fin (candidateScheduledFreshPrimes α κ T k shift).card => gaussianReal 0 1)).real
        {g | ∃ i ∈ J ω, K ≤ |candidateScheduledGaussianFresh ω α κ T k shift g i|}
        ∂candidateCylinderLaw s η) + δ := by
  have hν : (0 : ℝ) < 1 / 20 := by norm_num
  have hνPNT : (1 / 20 : ℝ) < 1 / 10 := by norm_num
  filter_upwards [candidate_eventually_prime_white_ceil_selected_crossing_le
    false s η β 1 hβ hν hνPNT hε hδ,
    candidateScheduleM_eventually_le_time hκ, eventually_ge_atTop (1 : ℝ)]
      with T hcomp hcard hT
  intro k hk shift hshift J hJ K
  let u : Fin (candidateScheduleM κ T) → ℝ :=
    fun i => candidateSchedulePoint α κ T k i shift
  let h : ℝ := Real.exp (-(T ^ (1 / 20 : ℝ)))
  let n : ℕ := ⌈((β - 1) * T) / h⌉₊
  have hh : 0 < h := Real.exp_pos _
  have hh1 : h ≤ 1 := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (Real.rpow_nonneg (by linarith : 0 ≤ T) _))
  have hu (i : Fin (candidateScheduleM κ T)) : u i ≤ β * T :=
    (candidate_grid_point_mem_window (by positivity)
      (candidateSchedule_cover hαβ (by linarith)) hk i.isLt hshift).2
  have hcover (i : Fin (candidateScheduleM κ T)) : u i ≤ T + (n : ℝ) * h :=
    (hu i).trans (candidate_macroscopic_ceil_bin_coverage hβ hT hh hh1).1
  have hc := hcomp _ u (by simpa only [Real.rpow_one] using hcard) hu J hJ K
  have heq (ω : Omega) := candidate_complete_comparison_prime_crossing_eq_fresh ω u
    (candidateScheduledFreshPrime α κ T k shift)
    (candidateScheduledFreshPrime α κ T k shift).injective T hh.le n hcover
    (candidateScheduledFreshPrime_image α κ T k shift) J K
  change (∫ ω, candidateComparisonWhiteCrossing false u T J (K + 3 * ε) ω
    ∂candidateCylinderLaw s η) ≤ _
  apply hc.trans
  apply add_le_add _ le_rfl
  change (∫ ω, candidateComparisonPrimeCrossing false u T h n J K ω
    ∂candidateCylinderLaw s η) ≤ _
  simp_rw [show ∀ ω, candidateComparisonPrimeCrossing false u T h n J K ω =
      (Measure.pi (fun _ : Fin (candidateScheduledFreshPrimes α κ T k shift).card =>
        gaussianReal 0 1)).real
      {g | ∃ i ∈ J ω, K < |candidateScheduledGaussianFresh ω α κ T k shift g i|}
      from heq]
  have hi := integrable_selected_linear_crossing_pair (candidateCylinderLaw s η)
    (fun ω p i => S ω (⌊Real.exp (u i)⌋₊ /
      candidateScheduledFreshPrime α κ T k shift p) / Real.exp (u i / 2))
    J (fun _ _ => (measurable_S _).div_const _) hJ K
  apply integral_mono hi.1 hi.2
  intro ω
  apply measureReal_mono _ (by finiteness)
  rintro g ⟨i, hi, hcross⟩
  exact ⟨i, hi, hcross.le⟩

/-- The final robust Gaussian certificate follows from complete-white
crossings on the literal old-negative selector. Only the threshold is moved
by a fixed comparison margin; the lower mass suffers no fixed loss. -/
theorem candidateScheduledGaussianRobustCrossing_of_completeWhite
    {α β κ ρ p0 : ℝ} (hαβ : α ≤ β) (hβ : 1 ≤ β) (hκ : 0 < κ)
    (hwhite : ∀ (s : Finset ℕ) (η : s → Bool) (b K ε : ℝ), 0 < K → 0 < ε →
      ∀ᶠ T : ℝ in atTop, ∀ k < candidateScheduleN α β κ T,
        ∀ shift ∈ Ioc (0 : ℝ) (2 * Real.pi),
        p0 - ε ≤ ∫ ω, candidateComparisonWhiteCrossing false
          (fun i : Fin (candidateScheduleM κ T) => candidateSchedulePoint α κ T k i shift)
          T (candidateRetainedIndices
            (fun ω (i : Fin (candidateScheduleM κ T)) =>
              harperCandidateLogOld ω (candidateScheduleX T)
                (candidateSchedulePoint α κ T k i shift)) b ρ) K ω
          ∂candidateCylinderLaw s η) :
    CandidateScheduledGaussianRobustCrossingStatement α β κ ρ p0 := by
  intro s η b K ε hK hε
  filter_upwards [hwhite s η b (K + 3) (ε / 2) (by linarith) (by positivity),
    candidateSchedule_completeWhite_fresh_selected_crossing hαβ hβ hκ s η
      (ε := 1) (δ := ε / 2) (by norm_num) (by positivity)]
      with T hW hC
  intro k hk shift hshift
  let J : Omega → Finset (Fin (candidateScheduleM κ T)) := candidateRetainedIndices
    (fun ω (i : Fin (candidateScheduleM κ T)) => harperCandidateLogOld ω
      (candidateScheduleX T) (candidateSchedulePoint α κ T k i shift)) b ρ
  have hJ (i : Fin (candidateScheduleM κ T)) : MeasurableSet {ω | i ∈ J ω} := by
    dsimp only [J]
    exact measurableSet_mem_candidateRetainedIndices
      (fun ω (j : Fin (candidateScheduleM κ T)) => harperCandidateLogOld ω
        (candidateScheduleX T) (candidateSchedulePoint α κ T k j shift))
      (fun j => measurable_harperCandidateLogOld (candidateScheduleX T)
        (candidateSchedulePoint α κ T k j shift)) b ρ i
  have hc := hC k hk shift hshift J hJ K
  have hw := hW k hk shift hshift
  simp only [mul_one] at hc
  change p0 - ε / 2 ≤ ∫ ω, candidateComparisonWhiteCrossing false _ _ J _ ω
    ∂candidateCylinderLaw s η at hw
  have hchain := hw.trans hc
  linarith only [hchain]

end Erdos.Problem1144
