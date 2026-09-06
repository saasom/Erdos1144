import Erdos.Problem1144.HarperTrackB

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace Erdos
namespace Problem1144

/-!
## Fresh-innovation meta layer

This file isolates the formal probability bookkeeping for the repaired Track B
fresh-innovation route.  The analytic work should eventually supply a
scale-compatible core, an exact decomposition `Y = C + R`, and a
one-dimensional small-ball estimate.  The lemmas here keep that formal layer
independent of the eventual choice of endpoint, annular kernel, or true
first-Walsh projection.
-/

/-- One-point exceedance inside the outside-measurable good event. -/
def freshInnovationExceedanceEvent
    (core : Omega → ℕ → ℕ → ℝ) (good : ℕ → Set Omega)
    (B : ℕ → ℕ → ℝ) (j r : ℕ) : Set Omega :=
  good j ∩ {omega | B j r ≤ core omega j r}

/-- Small-ball event for a fresh core, restricted to the good event. -/
def freshInnovationSmallBallEvent
    (core : Omega → ℕ → ℕ → ℝ) (good : ℕ → Set Omega)
    (B : ℕ → ℕ → ℝ) (j r : ℕ) : Set Omega :=
  good j ∩ {omega | |core omega j r| ≤ B j r}

/-- The part of the good event not covered by the positive threshold or the
small-ball event.  Analytically this is paid by symmetry of the conditional
fresh Rademacher sum. -/
def freshInnovationLowerTailRemainderEvent
    (core : Omega → ℕ → ℕ → ℝ) (good : ℕ → Set Omega)
    (B : ℕ → ℕ → ℝ) (j r : ℕ) : Set Omega :=
  good j \
    (freshInnovationExceedanceEvent core good B j r ∪
      freshInnovationSmallBallEvent core good B j r)

/-- The genuine negative core tail at the same threshold.  The formal
lower-tail remainder event is contained in this set when `B j r >= 0`. -/
def freshInnovationCoreNegativeTailEvent
    (core : Omega → ℕ → ℕ → ℝ)
    (B : ℕ → ℕ → ℝ) (j r : ℕ) : Set Omega :=
  {omega | core omega j r < -B j r}

/-- Pair exceedance for two fresh cores. -/
def freshInnovationPairExceedanceEvent
    (core : Omega → ℕ → ℕ → ℝ) (good : ℕ → Set Omega)
    (B : ℕ → ℕ → ℝ) (j r s : ℕ) : Set Omega :=
  freshInnovationExceedanceEvent core good B j r ∩
    freshInnovationExceedanceEvent core good B j s

/-- Negative selected-remainder event at the innovation scale. -/
def freshInnovationRemainderBadEvent
    (remainder : Omega → ℕ → ℕ → ℝ)
    (B : ℕ → ℕ → ℝ) (j r : ℕ) : Set Omega :=
  {omega | remainder omega j r < -B j r}

theorem measurableSet_freshInnovationExceedanceEvent
    {core : Omega → ℕ → ℕ → ℝ} {good : ℕ → Set Omega}
    {B : ℕ → ℕ → ℝ}
    (hgood : MeasurableSet (good j))
    (hcore : Measurable fun omega : Omega => core omega j r) :
    MeasurableSet (freshInnovationExceedanceEvent core good B j r) := by
  exact hgood.inter (measurableSet_le measurable_const hcore)

theorem measurableSet_freshInnovationSmallBallEvent
    {core : Omega → ℕ → ℕ → ℝ} {good : ℕ → Set Omega}
    {B : ℕ → ℕ → ℝ}
    (hgood : MeasurableSet (good j))
    (hcore : Measurable fun omega : Omega => core omega j r) :
    MeasurableSet (freshInnovationSmallBallEvent core good B j r) := by
  exact hgood.inter
    (measurableSet_le (continuous_abs.measurable.comp hcore) measurable_const)

theorem measurableSet_freshInnovationLowerTailRemainderEvent
    {core : Omega → ℕ → ℕ → ℝ} {good : ℕ → Set Omega}
    {B : ℕ → ℕ → ℝ}
    (hgood : MeasurableSet (good j))
    (hcore : Measurable fun omega : Omega => core omega j r) :
    MeasurableSet (freshInnovationLowerTailRemainderEvent core good B j r) := by
  exact hgood.diff
    ((measurableSet_freshInnovationExceedanceEvent (j := j) (r := r) hgood hcore).union
      (measurableSet_freshInnovationSmallBallEvent (j := j) (r := r) hgood hcore))

theorem measurableSet_freshInnovationCoreNegativeTailEvent
    {core : Omega → ℕ → ℕ → ℝ} {B : ℕ → ℕ → ℝ}
    (hcore : Measurable fun omega : Omega => core omega j r) :
    MeasurableSet (freshInnovationCoreNegativeTailEvent core B j r) := by
  exact measurableSet_lt hcore measurable_const

theorem measurableSet_freshInnovationPairExceedanceEvent
    {core : Omega → ℕ → ℕ → ℝ} {good : ℕ → Set Omega}
    {B : ℕ → ℕ → ℝ}
    (hgood : MeasurableSet (good j))
    (hcore_r : Measurable fun omega : Omega => core omega j r)
    (hcore_s : Measurable fun omega : Omega => core omega j s) :
    MeasurableSet (freshInnovationPairExceedanceEvent core good B j r s) := by
  exact
    (measurableSet_freshInnovationExceedanceEvent (j := j) (r := r) hgood hcore_r).inter
      (measurableSet_freshInnovationExceedanceEvent (j := j) (r := s) hgood hcore_s)

/-- The good event is covered by the positive exceedance, the small-ball event,
and the formal lower-tail remainder event. -/
theorem freshInnovationGood_subset_three_events
    (core : Omega → ℕ → ℕ → ℝ) (good : ℕ → Set Omega)
    (B : ℕ → ℕ → ℝ) (j r : ℕ) :
    good j ⊆
      freshInnovationExceedanceEvent core good B j r ∪
        (freshInnovationSmallBallEvent core good B j r ∪
          freshInnovationLowerTailRemainderEvent core good B j r) := by
  intro omega hgood
  by_cases hpos : omega ∈ freshInnovationExceedanceEvent core good B j r
  · exact Or.inl hpos
  · by_cases hsmall : omega ∈ freshInnovationSmallBallEvent core good B j r
    · exact Or.inr (Or.inl hsmall)
    · refine Or.inr (Or.inr ?_)
      exact ⟨hgood, by intro h; exact h.elim hpos hsmall⟩

/-- The formal leftover inside the good event is a genuine negative tail of
the core, provided the threshold is nonnegative.  This is the deterministic
part of the conditional-symmetry handoff. -/
theorem freshInnovationLowerTailRemainder_subset_coreNegativeTail
    (core : Omega → ℕ → ℕ → ℝ) (good : ℕ → Set Omega)
    (B : ℕ → ℕ → ℝ) (j r : ℕ)
    (_hB : 0 ≤ B j r) :
    freshInnovationLowerTailRemainderEvent core good B j r ⊆
      freshInnovationCoreNegativeTailEvent core B j r := by
  intro omega homega
  rcases homega with ⟨_hgood, hnot⟩
  rw [Set.mem_union, not_or] at hnot
  rcases hnot with ⟨hnotExceed, hnotSmall⟩
  rw [freshInnovationSmallBallEvent, Set.mem_inter_iff, not_and_or] at hnotSmall
  have hnotAbs : ¬ |core omega j r| ≤ B j r := by
    exact hnotSmall.resolve_left (fun hnotGood => hnotGood _hgood)
  have hB_lt_abs : B j r < |core omega j r| := lt_of_not_ge hnotAbs
  have hnotCore_ge : ¬ B j r ≤ core omega j r := by
    intro hcore_ge
    exact hnotExceed ⟨_hgood, hcore_ge⟩
  have hcore_lt_B : core omega j r < B j r := lt_of_not_ge hnotCore_ge
  have hcore_neg : core omega j r < 0 := by
    by_contra hnot_neg
    have hcore_nonneg : 0 ≤ core omega j r := le_of_not_gt hnot_neg
    have hcore_abs_le_B : |core omega j r| ≤ B j r := by
      rw [abs_of_nonneg hcore_nonneg]
      exact le_of_lt hcore_lt_B
    exact hnotAbs hcore_abs_le_B
  have hcore_abs_eq : |core omega j r| = -core omega j r := abs_of_neg hcore_neg
  have hB_lt_neg_core : B j r < -core omega j r := by
    simpa [hcore_abs_eq] using hB_lt_abs
  change core omega j r < -B j r
  linarith

/-- Real-measure version of the three-event cover. -/
theorem freshInnovationGood_measureReal_le
    (core : Omega → ℕ → ℕ → ℝ) (good : ℕ → Set Omega)
    (B : ℕ → ℕ → ℝ) (j r : ℕ) :
    mu.real (good j) ≤
      mu.real (freshInnovationExceedanceEvent core good B j r) +
        mu.real (freshInnovationSmallBallEvent core good B j r) +
          mu.real (freshInnovationLowerTailRemainderEvent core good B j r) := by
  let E := freshInnovationExceedanceEvent core good B j r
  let S := freshInnovationSmallBallEvent core good B j r
  let L := freshInnovationLowerTailRemainderEvent core good B j r
  have hsubset : good j ⊆ E ∪ (S ∪ L) :=
    freshInnovationGood_subset_three_events core good B j r
  calc
    mu.real (good j) ≤ mu.real (E ∪ (S ∪ L)) := measureReal_mono hsubset
    _ ≤ mu.real E + mu.real (S ∪ L) := measureReal_union_le _ _
    _ ≤ mu.real E + (mu.real S + mu.real L) := by
          linarith [measureReal_union_le (μ := mu) S L]
    _ = mu.real E + mu.real S + mu.real L := by ring

/-- One-point lower bound from a high-probability good event, a small-ball
bound, and the symmetry input that the uncovered lower tail is no larger than
the positive exceedance. -/
theorem freshInnovationExceedance_measureReal_lower_of_smallBall
    {core : Omega → ℕ → ℕ → ℝ} {good : ℕ → Set Omega}
    {B : ℕ → ℕ → ℝ} {j r : ℕ}
    {goodFail smallBall : ℝ}
    (hgood :
      1 - goodFail ≤ mu.real (good j))
    (hsmall :
      mu.real (freshInnovationSmallBallEvent core good B j r) ≤ smallBall)
    (hlower :
      mu.real (freshInnovationLowerTailRemainderEvent core good B j r) ≤
        mu.real (freshInnovationExceedanceEvent core good B j r)) :
    (1 - goodFail - smallBall) / 2 ≤
      mu.real (freshInnovationExceedanceEvent core good B j r) := by
  let E := freshInnovationExceedanceEvent core good B j r
  let S := freshInnovationSmallBallEvent core good B j r
  let L := freshInnovationLowerTailRemainderEvent core good B j r
  have hcover :
      mu.real (good j) ≤ mu.real E + mu.real S + mu.real L :=
    freshInnovationGood_measureReal_le core good B j r
  have hmain : 1 - goodFail ≤ 2 * mu.real E + smallBall := by
    calc
      1 - goodFail ≤ mu.real (good j) := hgood
      _ ≤ mu.real E + mu.real S + mu.real L := hcover
      _ ≤ 2 * mu.real E + smallBall := by
            linarith [hsmall, hlower]
  linarith

/-- Budgeted one-point lower bound.  If the good-event and small-ball losses
fit inside `2 * slack`, the positive exceedance has probability at least
`1/2 - slack`. -/
theorem freshInnovationExceedance_measureReal_lower_of_budget
    {core : Omega → ℕ → ℕ → ℝ} {good : ℕ → Set Omega}
    {B : ℕ → ℕ → ℝ} {j r : ℕ}
    {goodFail smallBall slack : ℝ}
    (hgood :
      1 - goodFail ≤ mu.real (good j))
    (hsmall :
      mu.real (freshInnovationSmallBallEvent core good B j r) ≤ smallBall)
    (hlower :
      mu.real (freshInnovationLowerTailRemainderEvent core good B j r) ≤
        mu.real (freshInnovationExceedanceEvent core good B j r))
    (hbudget : goodFail + smallBall ≤ 2 * slack) :
    (1 : ℝ) / 2 - slack ≤
      mu.real (freshInnovationExceedanceEvent core good B j r) := by
  have hlowerProb :=
    freshInnovationExceedance_measureReal_lower_of_smallBall
      (core := core) (good := good) (B := B) (j := j) (r := r)
      (goodFail := goodFail) (smallBall := smallBall) hgood hsmall hlower
  linarith

/-- One-point lower bound using the genuine negative-tail symmetry input,
rather than the formal leftover event. -/
theorem freshInnovationExceedance_measureReal_lower_of_negativeTail
    {core : Omega → ℕ → ℕ → ℝ} {good : ℕ → Set Omega}
    {B : ℕ → ℕ → ℝ} {j r : ℕ}
    {goodFail smallBall : ℝ}
    (hB : 0 ≤ B j r)
    (hgood :
      1 - goodFail ≤ mu.real (good j))
    (hsmall :
      mu.real (freshInnovationSmallBallEvent core good B j r) ≤ smallBall)
    (hnegative :
      mu.real (freshInnovationCoreNegativeTailEvent core B j r) ≤
        mu.real (freshInnovationExceedanceEvent core good B j r)) :
    (1 - goodFail - smallBall) / 2 ≤
      mu.real (freshInnovationExceedanceEvent core good B j r) := by
  refine
    freshInnovationExceedance_measureReal_lower_of_smallBall
      (core := core) (good := good) (B := B) (j := j) (r := r)
      (goodFail := goodFail) (smallBall := smallBall) hgood hsmall ?_
  exact
    le_trans
      (measureReal_mono
        (freshInnovationLowerTailRemainder_subset_coreNegativeTail
          core good B j r hB))
      hnegative

/-- Budgeted version of
`freshInnovationExceedance_measureReal_lower_of_negativeTail`. -/
theorem freshInnovationExceedance_measureReal_lower_of_negativeTail_budget
    {core : Omega → ℕ → ℕ → ℝ} {good : ℕ → Set Omega}
    {B : ℕ → ℕ → ℝ} {j r : ℕ}
    {goodFail smallBall slack : ℝ}
    (hB : 0 ≤ B j r)
    (hgood :
      1 - goodFail ≤ mu.real (good j))
    (hsmall :
      mu.real (freshInnovationSmallBallEvent core good B j r) ≤ smallBall)
    (hnegative :
      mu.real (freshInnovationCoreNegativeTailEvent core B j r) ≤
        mu.real (freshInnovationExceedanceEvent core good B j r))
    (hbudget : goodFail + smallBall ≤ 2 * slack) :
    (1 : ℝ) / 2 - slack ≤
      mu.real (freshInnovationExceedanceEvent core good B j r) := by
  have hlower :=
    freshInnovationExceedance_measureReal_lower_of_negativeTail
      (core := core) (good := good) (B := B) (j := j) (r := r)
      (goodFail := goodFail) (smallBall := smallBall)
      hB hgood hsmall hnegative
  linarith

/-- Generic one-point negative-tail Markov bound for any scale-compatible
remainder. -/
theorem measure_freshInnovationRemainderBadEvent_le_second
    (remainder : Omega → ℕ → ℕ → ℝ) (B second : ℕ → ℕ → ℝ)
    (j r : ℕ)
    (hB : 0 < B j r)
    (hint : Integrable (fun omega => (remainder omega j r) ^ 2) mu)
    (hsecond :
      (∫ omega, (remainder omega j r) ^ 2 ∂mu) ≤ second j r) :
    mu (freshInnovationRemainderBadEvent remainder B j r) ≤
      ENNReal.ofReal (second j r / (B j r) ^ 2) := by
  have hsubset :
      freshInnovationRemainderBadEvent remainder B j r ⊆
        {omega | B j r < |remainder omega j r|} := by
    intro omega hbad
    change remainder omega j r < -B j r at hbad
    have hlt_neg : B j r < -remainder omega j r := by linarith
    exact lt_of_lt_of_le hlt_neg (neg_le_abs _)
  calc
    mu (freshInnovationRemainderBadEvent remainder B j r)
        ≤ mu {omega | B j r < |remainder omega j r|} :=
          measure_mono hsubset
    _ ≤ ENNReal.ofReal (second j r / (B j r) ^ 2) := by
          exact
            measure_abs_error_gt_le_second
              (E := fun omega => remainder omega j r)
              (A := B j r)
              (V := second j r)
              hB hint hsecond

/-- If the selected remainder is identically zero and the threshold is
positive, then the negative-remainder bad event is empty.  This is the formal
wrapper needed by endpoint-shell observables, where the first fresh-prime core
is the whole observable. -/
theorem freshInnovationRemainderBadEvent_zero_eq_empty
    (B : ℕ → ℕ → ℝ) (j r : ℕ)
    (hB : 0 < B j r) :
    freshInnovationRemainderBadEvent (fun _omega _j _r => 0) B j r = ∅ := by
  ext omega
  simp [freshInnovationRemainderBadEvent, hB.not_gt]

/-- Measure form of `freshInnovationRemainderBadEvent_zero_eq_empty`. -/
theorem measure_freshInnovationRemainderBadEvent_zero
    (B : ℕ → ℕ → ℝ) (j r : ℕ)
    (hB : 0 < B j r) :
    mu (freshInnovationRemainderBadEvent (fun _omega _j _r => 0) B j r) = 0 := by
  rw [freshInnovationRemainderBadEvent_zero_eq_empty B j r hB]
  simp

end Problem1144
end Erdos
