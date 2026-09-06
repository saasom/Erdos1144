import Erdos.Problem1144.HarperCandidateSchedule
import Erdos.Problem1144.HarperCandidatePositiveScreen
import Erdos.Problem1144.HarperCandidateLaplaceIntegrability
import Erdos.Problem1144.HarperCandidateLaplaceApproximation

open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-- The Laplace input needed by the schedule argument, only almost surely on
the bounded-upper-envelope event and only for sufficiently large time. -/
def CandidateScheduledLaplaceStatement : Prop :=
  ∀ (M : ℕ) (s : Finset ℕ) (η : s → Bool), ∀ᶠ T : ℝ in atTop,
    ∀ᵐ ω ∂candidateCylinderLaw s η, ω ∈ candidateUpperEnvelope M →
      IntegrableOn (fun t => Real.exp (-t / T) * harperCandidateLogProcess ω t) (Ioi 0) ∧
      0 ≤ ∫ t in Ioi 0, Real.exp (-t / T) * harperCandidateLogProcess ω t

/-- Only positivity remains in the Laplace input: absolute integrability is
already proved for the actual process under every finite cylinder law. -/
def CandidateScheduledLaplacePositivityStatement : Prop :=
  ∀ (M : ℕ) (s : Finset ℕ) (η : s → Bool), ∀ᶠ T : ℝ in atTop,
    ∀ᵐ ω ∂candidateCylinderLaw s η, ω ∈ candidateUpperEnvelope M →
      0 ≤ ∫ t in Ioi 0, Real.exp (-t / T) * harperCandidateLogProcess ω t

theorem candidateScheduledLaplaceStatement_of_positivity
    (h : CandidateScheduledLaplacePositivityStatement) :
    CandidateScheduledLaplaceStatement := by
  intro M s η
  filter_upwards [h M s η, eventually_gt_atTop (0 : ℝ)] with T hpos hT
  filter_upwards [hpos, candidateCylinderLaw_ae_integrable_laplace s η hT] with ω hp hi
  intro hω
  exact ⟨hi, hp hω⟩

/-- The robust absolute-crossing input on the literal candidate schedule.
The threshold and cylinder are fixed before time tends to infinity; the
estimate is uniform in every deterministic block and shift. The retained
selector is exactly the old-measurable selector consumed by the screen. -/
def CandidateScheduledRobustCrossingStatement (α β κ ρ p0 : ℝ) : Prop :=
  ∀ (s : Finset ℕ) (η : s → Bool) (b K ε : ℝ), 0 < K → 0 < ε →
    ∀ᶠ T : ℝ in atTop, ∀ k < candidateScheduleN α β κ T,
      ∀ shift ∈ Ioc (0 : ℝ) (2 * Real.pi),
      p0 - ε ≤ (candidateCylinderLaw s η).real
        {ω | ∃ i ∈ candidateRetainedIndices
          (fun ω (i : Fin (candidateScheduleM κ T)) =>
            harperCandidateLogOld ω (candidateScheduleX T)
              (candidateSchedulePoint α κ T k i shift)) b ρ ω,
          K < |harperCandidateLogFresh ω (candidateScheduleX T)
            (candidateSchedulePoint α κ T k i shift)|}

/-- The candidate's exact schedules discharge the entire old-tail and
rounding assembly. Only the Laplace and robust-crossing inputs remain. -/
theorem candidateLogCylinderScreenStatement_of_scheduledInputs
    {α β κ ρ p0 : ℝ} (hα : 1 < α) (hαβ : α < β) (hβ : β < 4 / 3) (hκ : 0 < κ)
    (hLaplace : CandidateScheduledLaplaceStatement)
    (hCross : CandidateScheduledRobustCrossingStatement α β κ ρ p0) :
    CandidateLogCylinderScreenStatementWithMass ρ p0 := by
  intro M s η ε hε
  let q : ℝ := (candidateCylinderLaw s η).real (candidateUpperEnvelope M)
  obtain ⟨b, hb, hbudget⟩ := candidateSchedule_exists_threshold_tailBudget hαβ hκ q M hε
  have hK : 0 < (M : ℝ) + b := add_pos_of_nonneg_of_pos (Nat.cast_nonneg M) hb
  have hgood : ∀ᶠ T : ℝ in atTop,
      0 < T ∧ 0 < candidateScheduleM κ T ∧ 0 < candidateScheduleN α β κ T ∧
      (∀ p ∈ s, p ≤ candidateScheduleX T) ∧
      (∀ t ≤ β * T, ⌊Real.exp t⌋₊ < candidateScheduleX T ^ 2) ∧
      2 * ((1 - q) * (β - α) * T + Real.exp β * M * T / b) /
        (candidateScheduleN α β κ T * candidateScheduleL κ T) ≤ 2 * (1 - q) + ε ∧
      (∀ᵐ ω ∂candidateCylinderLaw s η, ω ∈ candidateUpperEnvelope M →
        IntegrableOn (fun t => Real.exp (-t / T) * harperCandidateLogProcess ω t) (Ioi 0) ∧
        0 ≤ ∫ t in Ioi 0, Real.exp (-t / T) * harperCandidateLogProcess ω t) ∧
      (∀ k < candidateScheduleN α β κ T, ∀ shift ∈ Ioc (0 : ℝ) (2 * Real.pi),
        p0 - ε ≤ (candidateCylinderLaw s η).real
          {ω | ∃ i ∈ candidateRetainedIndices
            (fun ω (i : Fin (candidateScheduleM κ T)) =>
              harperCandidateLogOld ω (candidateScheduleX T)
                (candidateSchedulePoint α κ T k i shift)) b ρ ω,
            (M : ℝ) + b < |harperCandidateLogFresh ω (candidateScheduleX T)
              (candidateSchedulePoint α κ T k i shift)|}) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (candidateScheduleM_tendsto hκ).eventually_gt_atTop 0,
      (candidateScheduleN_tendsto hαβ hκ).eventually_gt_atTop 0,
      candidateSchedule_eventually_prefix s,
      candidateSchedule_eventually_cutoff_square (show β < 2 by linarith),
      hbudget, hLaplace M s η, hCross s η b (M + b) ε hK hε]
      with T hT hm hn hs hc hbgt hl hx
    exact ⟨hT, hm, hn, hs, hc, hbgt, hl, hx⟩
  obtain ⟨T, hT, hm, hn, hs, hcut, hbudgetT, hpaths, hcrossT⟩ := hgood.exists
  have hcover := candidateSchedule_cover (κ := κ) hαβ.le hT.le
  obtain ⟨k, hk, shift, hshift, hmem, havg⟩ :=
    candidate_exists_log_grid_old_negative_average_le M s η (candidateScheduleX T) hs
      hT (by linarith : 0 ≤ α) hαβ.le hb hm hn (by positivity : 0 < 2 * Real.pi)
      (by simpa only [candidateScheduleL] using hcover)
      (fun t ht => hcut t ht.2) hpaths
  refine ⟨candidateScheduleX T, candidateScheduleM κ T,
    (fun i => candidateSchedulePoint α κ T k i shift), b, hm, hs, ?_, ?_, ?_⟩
  · intro i
    have hi := hmem i i.isLt
    constructor
    · exact (mul_nonneg (show 0 ≤ α by linarith) hT.le).trans hi.1.le
    · exact hcut _ hi.2
  · have hmean :
        (∑ i : Fin (candidateScheduleM κ T), (candidateCylinderLaw s η).real
          {ω | harperCandidateLogOld ω (candidateScheduleX T)
            (candidateSchedulePoint α κ T k i shift) < -b}) / candidateScheduleM κ T ≤
          2 * (1 - q) + ε := by
      have hh := havg.trans (by simpa only [candidateScheduleL, mul_assoc] using hbudgetT)
      rw [Finset.sum_range] at hh
      simpa only [candidateSchedulePoint, candidateScheduleL] using hh
    exact (div_le_iff₀ (Nat.cast_pos.mpr hm)).mp hmean
  · exact hcrossT k hk shift hshift

/-- The fully assembled conditional endpoint for the candidate's logarithmic
schedule. The substantive analytic hypotheses are explicit arguments. -/
theorem erdos1144_of_candidateScheduledInputs
    {α β κ ρ p0 : ℝ} (hα : 1 < α) (hαβ : α < β) (hβ : β < 4 / 3)
    (hκ : 0 < κ) (hρ : ρ < 1) (hp0 : 0 < p0)
    (hLaplace : CandidateScheduledLaplaceStatement)
    (hCross : CandidateScheduledRobustCrossingStatement α β κ ρ p0) :
    Erdos1144 :=
  erdos1144_of_candidateLogCylinderScreenStatementWithMass hρ hp0
    (candidateLogCylinderScreenStatement_of_scheduledInputs hα hαβ hβ hκ hLaplace hCross)

/-- Absolute Laplace integrability is discharged by the actual complete
process estimate; only transform positivity and robust crossing are assumed. -/
theorem erdos1144_of_candidateScheduledPositivityAndCrossing
    {α β κ ρ p0 : ℝ} (hα : 1 < α) (hαβ : α < β) (hβ : β < 4 / 3)
    (hκ : 0 < κ) (hρ : ρ < 1) (hp0 : 0 < p0)
    (hPositive : CandidateScheduledLaplacePositivityStatement)
    (hCross : CandidateScheduledRobustCrossingStatement α β κ ρ p0) :
    Erdos1144 :=
  erdos1144_of_candidateScheduledInputs hα hαβ hβ hκ hρ hp0
    (candidateScheduledLaplaceStatement_of_positivity hPositive) hCross

/-- The full scheduled Laplace positivity statement is proved for the actual
complete process, including every fixed cylinder law. -/
theorem candidateScheduledLaplacePositivity : CandidateScheduledLaplacePositivityStatement := by
  intro M s η
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  filter_upwards [candidateCylinderLaw_ae_laplace_nonneg s η hT] with ω hω
  exact fun _ => hω

/-- The exact old-tail schedule and all Laplace assumptions are discharged.
The only remaining argument is a fixed positive robust fresh crossing. -/
theorem erdos1144_of_candidateScheduledRobustCrossing
    {α β κ ρ p0 : ℝ} (hα : 1 < α) (hαβ : α < β) (hβ : β < 4 / 3)
    (hκ : 0 < κ) (hρ : ρ < 1) (hp0 : 0 < p0)
    (hCross : CandidateScheduledRobustCrossingStatement α β κ ρ p0) : Erdos1144 :=
  erdos1144_of_candidateScheduledPositivityAndCrossing hα hαβ hβ hκ hρ hp0
    candidateScheduledLaplacePositivity hCross

end Erdos.Problem1144

#print axioms Erdos.Problem1144.candidateLogCylinderScreenStatement_of_scheduledInputs
#print axioms Erdos.Problem1144.erdos1144_of_candidateScheduledInputs

#print axioms Erdos.Problem1144.erdos1144_of_candidateScheduledPositivityAndCrossing
