import Erdos.Problem1144.HarperCandidateStationarySquarefreeLower
import Erdos.Problem1144.HarperCandidateStationaryWhiteAveraging
import Erdos.Problem1144.HarperCandidateStationaryGaussianTailRates
import Erdos.Problem1144.HarperCandidateScheduleBlockWhiteGeometry

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos.Problem1144

/-- Positive complete-white crossing on the literal scheduled old-negative
selector. All squarefree lower bounds, stationary comparisons and Gaussian
tail losses are instantiated on the same original blocks and selected sets. -/
theorem candidate_exists_scheduled_completeWhite_crossing :
    ∃ p : ℝ, 0 < p ∧ ∀ α β κ ρ : ℝ,
      1 < α → α < β → β < 4 / 3 → 0 < κ → 0 < ρ → ρ ≤ 1 →
      2 < (α - 1) * κ →
      ∀ (s : Finset ℕ) (η : s → Bool) (b K ε : ℝ), 0 < K → 0 < ε →
      ∀ᶠ T : ℝ in atTop, ∀ k < candidateScheduleN α β κ T,
        ∀ shift ∈ Ioc (0 : ℝ) (2 * Real.pi),
        p - ε ≤ ∫ ω, candidateComparisonWhiteCrossing false
          (fun i : Fin (candidateScheduleM κ T) => candidateSchedulePoint α κ T k i shift)
          T (candidateRetainedIndices
            (fun ω (i : Fin (candidateScheduleM κ T)) =>
              harperCandidateLogOld ω (candidateScheduleX T)
                (candidateSchedulePoint α κ T k i shift)) b ρ) K ω
          ∂candidateCylinderLaw s η := by
  obtain ⟨p, hp, hsf⟩ := candidate_exists_stationary_squarefree_selected_lower
  obtain ⟨C, hC, hcompare⟩ := candidate_exists_integral_squarefree_complete_white_comparison
  refine ⟨p / 8, by positivity, ?_⟩
  intro α β κ ρ hα hαβ hβ hκ hρ hρ1 hgap s η b K ε hK hε
  have hβ0 : 0 < β := by linarith
  filter_upwards [hsf α β κ ρ C hα hαβ hβ hκ hρ hρ1 hC s η K hK.le,
    hcompare κ β hκ hβ0,
    candidate_eventually_squarefreeHighCovariance_tail_lt s η hκ
      (by norm_num : (0 : ℝ) < 1) hε,
    candidate_eventually_stationaryExtension_tail_lt s η
      (by linarith : 0 ≤ α - 1) hκ hgap (by norm_num : (0 : ℝ) < 1) hε,
    candidateSchedule_eventually_block_white_geometry hκ hαβ,
    (candidateScheduleM_tendsto hκ).eventually_gt_atTop 0]
    with T hsfT hcompareT hhighT hextT hgeometry hM
  intro k hk shift hshift
  let u := fun i : Fin (candidateScheduleM κ T) => candidateSchedulePoint α κ T k i shift
  let v := fun i : Fin (candidateScheduleM κ T) =>
    α * candidateScheduleWhiteTime κ T + i * (2 * Real.pi)
  let t0 := α * T + (k : ℝ) * candidateScheduleL κ T + shift
  let F := fun ω (i : Fin (candidateScheduleM κ T)) =>
    harperCandidateLogOld ω (candidateScheduleX T) (u i)
  let selector := candidateRetainedIndices F b ρ
  have hF (i : Fin (candidateScheduleM κ T)) : Measurable fun ω => F ω i :=
    measurable_harperCandidateLogOld (candidateScheduleX T) (u i)
  have hs : ∀ i, MeasurableSet {ω | i ∈ selector ω} :=
    measurableSet_mem_candidateRetainedIndices F hF b ρ
  have hg := hgeometry k hk shift hshift
  have hc := hcompareT s η (candidateScheduleM κ T) hM u v
    (t0 - α * candidateScheduleWhiteTime κ T) t0
    (fun i => (hg i).1) (fun i => (hg i).2.2.2.2)
    (fun i => (hg i).2.2.1.2) (fun i => (hg i).2.1.1)
    (fun i => (hg i).2.1.2) selector hs K
  have hlo := hsfT F hF b
  have hhi := (hhighT v).2
  have hex := (hextT u (fun i => by
    have hh := (hg i).2.2.1.1
    convert hh using 1 <;> ring)).2
  change p ≤ ∫ ω, candidateComparisonWhiteCrossing true v
    (T / candidateScheduleW κ T) selector
      (candidateStationaryWhiteTransferThreshold C κ β T K) ω
      ∂candidateCylinderLaw s η at hlo
  change p / 8 - ε ≤ ∫ ω, candidateComparisonWhiteCrossing false u T selector K ω
    ∂candidateCylinderLaw s η
  linarith

end Erdos.Problem1144
