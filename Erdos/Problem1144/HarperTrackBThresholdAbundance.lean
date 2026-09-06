import Erdos.Problem1144.HarperAbundance

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-!
# Track B threshold-abundance bridge

The limited Track B route can avoid the full prefix-process Brownian crossing
theorem.  It is enough to prove many one-sided exceedances of a sparse
rough-core process, plus a small overlap with the selected remainder.

This module is deliberately abstract in the decomposition:

```text
normSum(N) = core(j,N) + remainder(j,N)
```

is not assumed as an equality.  The only deterministic requirement is the
absorption implication

```text
core(j,N) >= M_j + buffer_j
and remainder(j,N) >= -buffer_j
  => normSum(N) >= M_j.
```

The probability layer is the same second-moment abundance argument used by the
Harper threshold-selector route, but now it is independent of the old
complete-model large-prime/smooth decomposition.
-/

/-- Test points whose abstract Track B core exceeds the threshold
`M + buffer`. -/
noncomputable def trackBThresholdExceedanceSet
    (testSet : ℕ → Finset ℕ)
    (core : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ) (omega : Omega) (j : ℕ) : Finset ℕ := by
  classical
  exact (testSet j).filter fun N => M j + buffer j ≤ core omega j N

/-- Test points whose abstract Track B remainder is below the negative
buffer. -/
noncomputable def trackBThresholdRemainderBadSet
    (testSet : ℕ → Finset ℕ)
    (remainder : Omega → ℕ → ℕ → ℝ)
    (buffer : ℕ → ℝ) (omega : Omega) (j : ℕ) : Finset ℕ := by
  classical
  exact (testSet j).filter fun N => remainder omega j N < -buffer j

/-- Test points where the core threshold is exceeded but the selected
remainder is bad. -/
noncomputable def trackBThresholdOverlapSet
    (testSet : ℕ → Finset ℕ)
    (core remainder : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ) (omega : Omega) (j : ℕ) : Finset ℕ := by
  classical
  exact
    (testSet j).filter fun N =>
      M j + buffer j ≤ core omega j N ∧
        remainder omega j N < -buffer j

theorem mem_trackBThresholdExceedanceSet
    (testSet : ℕ → Finset ℕ)
    (core : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ) (omega : Omega) (j N : ℕ) :
    N ∈ trackBThresholdExceedanceSet testSet core M buffer omega j ↔
      N ∈ testSet j ∧ M j + buffer j ≤ core omega j N := by
  classical
  unfold trackBThresholdExceedanceSet
  simp

theorem mem_trackBThresholdRemainderBadSet
    (testSet : ℕ → Finset ℕ)
    (remainder : Omega → ℕ → ℕ → ℝ)
    (buffer : ℕ → ℝ) (omega : Omega) (j N : ℕ) :
    N ∈ trackBThresholdRemainderBadSet testSet remainder buffer omega j ↔
      N ∈ testSet j ∧ remainder omega j N < -buffer j := by
  classical
  unfold trackBThresholdRemainderBadSet
  simp

theorem mem_trackBThresholdOverlapSet
    (testSet : ℕ → Finset ℕ)
    (core remainder : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ) (omega : Omega) (j N : ℕ) :
    N ∈ trackBThresholdOverlapSet testSet core remainder M buffer omega j ↔
      N ∈ testSet j ∧
        M j + buffer j ≤ core omega j N ∧
          remainder omega j N < -buffer j := by
  classical
  unfold trackBThresholdOverlapSet
  simp

theorem trackBThresholdOverlapSet_subset_exceedanceSet
    (testSet : ℕ → Finset ℕ)
    (core remainder : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ) (omega : Omega) (j : ℕ) :
    trackBThresholdOverlapSet testSet core remainder M buffer omega j ⊆
      trackBThresholdExceedanceSet testSet core M buffer omega j := by
  intro N hN
  rw [mem_trackBThresholdExceedanceSet]
  exact ⟨(mem_trackBThresholdOverlapSet testSet core remainder M buffer omega j N).mp hN |>.1,
    (mem_trackBThresholdOverlapSet testSet core remainder M buffer omega j N).mp hN |>.2.1⟩

theorem trackBThresholdOverlapSet_subset_remainderBadSet
    (testSet : ℕ → Finset ℕ)
    (core remainder : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ) (omega : Omega) (j : ℕ) :
    trackBThresholdOverlapSet testSet core remainder M buffer omega j ⊆
      trackBThresholdRemainderBadSet testSet remainder buffer omega j := by
  intro N hN
  rw [mem_trackBThresholdRemainderBadSet]
  exact ⟨(mem_trackBThresholdOverlapSet testSet core remainder M buffer omega j N).mp hN |>.1,
    (mem_trackBThresholdOverlapSet testSet core remainder M buffer omega j N).mp hN |>.2.2⟩

theorem trackBThresholdOverlapSet_card_le_exceedanceSet_card
    (testSet : ℕ → Finset ℕ)
    (core remainder : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ) (omega : Omega) (j : ℕ) :
    (trackBThresholdOverlapSet testSet core remainder M buffer omega j).card ≤
      (trackBThresholdExceedanceSet testSet core M buffer omega j).card :=
  Finset.card_le_card
    (trackBThresholdOverlapSet_subset_exceedanceSet testSet core remainder M buffer omega j)

theorem trackBThresholdOverlapSet_card_le_remainderBadSet_card
    (testSet : ℕ → Finset ℕ)
    (core remainder : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ) (omega : Omega) (j : ℕ) :
    (trackBThresholdOverlapSet testSet core remainder M buffer omega j).card ≤
      (trackBThresholdRemainderBadSet testSet remainder buffer omega j).card :=
  Finset.card_le_card
    (trackBThresholdOverlapSet_subset_remainderBadSet testSet core remainder M buffer omega j)

/-- Event that the abstract core has fewer than `r_j` threshold exceedances. -/
def trackBThresholdFewExceedances
    (testSet : ℕ → Finset ℕ)
    (core : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ) (r : ℕ → ℕ) (j : ℕ) : Set Omega :=
  {omega |
    (trackBThresholdExceedanceSet testSet core M buffer omega j).card < r j}

/-- Event that at least `r_j` core exceedances also have bad remainder. -/
def trackBThresholdOverlapMany
    (testSet : ℕ → Finset ℕ)
    (core remainder : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ) (r : ℕ → ℕ) (j : ℕ) : Set Omega :=
  {omega |
    r j ≤
      (trackBThresholdOverlapSet testSet core remainder M buffer omega j).card}

/-- If many overlap points occur, then many remainder-bad points occur.  This
lets the selected-overlap budget be paid by any estimate controlling the number
of bad remainders on the test set. -/
theorem trackBThresholdOverlapMany_subset_remainderBadMany
    (testSet : ℕ → Finset ℕ)
    (core remainder : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ) (r : ℕ → ℕ) (j : ℕ) :
    trackBThresholdOverlapMany testSet core remainder M buffer r j ⊆
      {omega |
        r j ≤ (trackBThresholdRemainderBadSet testSet remainder buffer omega j).card} := by
  intro omega homega
  exact le_trans homega
    (trackBThresholdOverlapSet_card_le_remainderBadSet_card
      testSet core remainder M buffer omega j)

/-- If the required number of bad remainders is positive, then the many-bad
remainder event is contained in the finite union of one-point bad-remainder
events. -/
theorem trackBThresholdRemainderBadMany_subset_exists_bad
    (testSet : ℕ → Finset ℕ)
    (remainder : Omega → ℕ → ℕ → ℝ)
    (buffer : ℕ → ℝ) (r : ℕ → ℕ) (j : ℕ)
    (hr_pos : 0 < r j) :
    {omega |
      r j ≤ (trackBThresholdRemainderBadSet testSet remainder buffer omega j).card} ⊆
      ⋃ N ∈ testSet j, {omega | remainder omega j N < -buffer j} := by
  intro omega homega
  have hcard_pos :
      0 < (trackBThresholdRemainderBadSet testSet remainder buffer omega j).card :=
    lt_of_lt_of_le hr_pos homega
  rcases Finset.card_pos.mp hcard_pos with ⟨N, hNbad⟩
  rcases (mem_trackBThresholdRemainderBadSet testSet remainder buffer omega j N).mp hNbad
    with ⟨hNtest, hbad⟩
  exact Set.mem_iUnion₂.mpr ⟨N, hNtest, hbad⟩

/-- Union-bound control of the many-bad-remainder event from one-point
bad-remainder probabilities. -/
theorem measure_trackBThresholdRemainderBadMany_le_sum_single
    (testSet : ℕ → Finset ℕ)
    (remainder : Omega → ℕ → ℕ → ℝ)
    (buffer : ℕ → ℝ) (r : ℕ → ℕ) (j : ℕ)
    (hr_pos : 0 < r j) :
    mu {omega |
        r j ≤ (trackBThresholdRemainderBadSet testSet remainder buffer omega j).card}
      ≤
        ∑ N ∈ testSet j,
          mu {omega | remainder omega j N < -buffer j} := by
  exact le_trans
    (measure_mono
      (trackBThresholdRemainderBadMany_subset_exists_bad
        testSet remainder buffer r j hr_pos))
    (measure_biUnion_finset_le (μ := mu) (testSet j)
      fun N => {omega | remainder omega j N < -buffer j})

/-- Real-valued number of abstract core threshold exceedances. -/
noncomputable def trackBThresholdExceedanceCountReal
    (testSet : ℕ → Finset ℕ)
    (core : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ) (j : ℕ) (omega : Omega) : ℝ :=
  ((trackBThresholdExceedanceSet testSet core M buffer omega j).card : ℝ)

/-- Under block failure, every abstract core threshold exceedance must have
bad remainder; otherwise absorption gives a positive block success. -/
theorem trackBThresholdExceedanceSet_subset_overlapSet_of_blockFailure
    (lo hi : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (testSet : ℕ → Finset ℕ)
    (core remainder : Omega → ℕ → ℕ → ℝ)
    (omega : Omega) (j : ℕ)
    (testSet_in_block :
      ∀ N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j))
    (absorb :
      ∀ N, N ∈ testSet j →
        M j + buffer j ≤ core omega j N →
        -buffer j ≤ remainder omega j N →
        M j ≤ normSum omega N)
    (hfail : omega ∈ blockFailure lo hi M j) :
    trackBThresholdExceedanceSet testSet core M buffer omega j ⊆
      trackBThresholdOverlapSet testSet core remainder M buffer omega j := by
  intro N hN
  rw [mem_trackBThresholdExceedanceSet] at hN
  rcases hN with ⟨hNtest, hcore⟩
  rw [mem_trackBThresholdOverlapSet]
  refine ⟨hNtest, hcore, ?_⟩
  by_contra hrem_not_bad
  have hrem : -buffer j ≤ remainder omega j N := not_lt.mp hrem_not_bad
  have hsucc : blockSuccess lo hi M omega j := by
    refine ⟨N, testSet_in_block N hNtest, ?_⟩
    exact absorb N hNtest hcore hrem
  exact hfail hsucc

/-- Deterministic abstract threshold-selector bridge. -/
theorem blockFailure_subset_trackBThreshold_good_compl_union_few_union_overlapMany
    (lo hi : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (testSet : ℕ → Finset ℕ) (good : ℕ → Set Omega)
    (core remainder : Omega → ℕ → ℕ → ℝ)
    (r : ℕ → ℕ) (j : ℕ)
    (testSet_in_block :
      ∀ N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j))
    (absorb :
      ∀ omega N, N ∈ testSet j →
        M j + buffer j ≤ core omega j N →
        -buffer j ≤ remainder omega j N →
        M j ≤ normSum omega N) :
    blockFailure lo hi M j ⊆
      (good j)ᶜ ∪
        ((good j ∩
            trackBThresholdFewExceedances testSet core M buffer r j) ∪
          trackBThresholdOverlapMany testSet core remainder M buffer r j) := by
  intro omega hfail
  by_cases hgood : omega ∈ good j
  · by_cases hfew :
      omega ∈ trackBThresholdFewExceedances testSet core M buffer r j
    · exact Or.inr (Or.inl ⟨hgood, hfew⟩)
    · right
      right
      have hnotfew :
          r j ≤
            (trackBThresholdExceedanceSet testSet core M buffer omega j).card :=
        not_lt.mp hfew
      have hcard :
          (trackBThresholdExceedanceSet testSet core M buffer omega j).card ≤
            (trackBThresholdOverlapSet testSet core remainder M buffer omega j).card :=
        Finset.card_le_card
          (trackBThresholdExceedanceSet_subset_overlapSet_of_blockFailure
            lo hi M buffer testSet core remainder omega j testSet_in_block
            (fun N hN => absorb omega N hN) hfail)
      exact le_trans hnotfew hcard
  · exact Or.inl hgood

/-- Abstract threshold-abundance certificate for the Track B sparse block
route.  The analytic work supplies the moments of the abstract core exceedance
count and the selected-remainder overlap bound. -/
structure TrackBThresholdAbundanceCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  testSet : ℕ → Finset ℕ
  core : Omega → ℕ → ℕ → ℝ
  remainder : Omega → ℕ → ℕ → ℝ
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
  absorb :
    ∀ omega j N, N ∈ testSet j →
      M j + buffer j ≤ core omega j N →
      -buffer j ≤ remainder omega j N →
      M j ≤ normSum omega N
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  count_centered_second_integrable :
    ∀ j,
      Integrable
        (fun omega =>
          (trackBThresholdExceedanceCountReal testSet core M buffer j omega -
            ∫ omega',
              trackBThresholdExceedanceCountReal testSet core M buffer j omega'
                ∂mu) ^ 2)
        mu
  count_mean_lower :
    ∀ j,
      countMean j ≤
        ∫ omega, trackBThresholdExceedanceCountReal testSet core M buffer j omega
          ∂mu
  count_centered_second_upper :
    ∀ j,
      (∫ omega,
          (trackBThresholdExceedanceCountReal testSet core M buffer j omega -
            ∫ omega',
              trackBThresholdExceedanceCountReal testSet core M buffer j omega'
                ∂mu) ^ 2 ∂mu)
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
      mu
          (trackBThresholdOverlapMany testSet core remainder M buffer r j) ≤
        failOverlap j

/-- Abstract Track B threshold-abundance certificates imply positive blocks. -/
noncomputable def positiveBlockOmega_of_trackBThresholdAbundanceCertificate
    (h : TrackBThresholdAbundanceCertificate) :
    PositiveBlockOmega where
  X := h.lo
  Y := h.hi
  M := h.M
  fail := fun j =>
    h.failGood j +
      ENNReal.ofReal (4 * h.countSecond j / h.countMean j ^ 2) +
      h.failOverlap j
  X_tendsto := h.lo_tendsto_atTop
  M_tendsto := h.M_tendsto_atTop
  fail_summable := h.fail_summable
  prob_fail := by
    intro j
    let R : Omega → ℝ :=
      trackBThresholdExceedanceCountReal h.testSet h.core h.M h.buffer j
    let few : Set Omega :=
      trackBThresholdFewExceedances h.testSet h.core h.M h.buffer h.r j
    let overlap : Set Omega :=
      trackBThresholdOverlapMany h.testSet h.core h.remainder h.M h.buffer h.r j
    have hfew_subset :
        h.good j ∩ few ⊆ {omega | R omega < h.countMean j / 2} := by
      intro omega homega
      rcases homega with ⟨_, hfew⟩
      have hcard_lt :
          ((trackBThresholdExceedanceSet h.testSet h.core h.M h.buffer omega j).card : ℝ)
            < (h.r j : ℝ) :=
        Nat.cast_lt.mpr hfew
      have hRdef :
          R omega =
            ((trackBThresholdExceedanceSet h.testSet h.core h.M h.buffer omega j).card : ℝ) :=
        rfl
      change R omega < h.countMean j / 2
      rw [hRdef]
      exact lt_of_lt_of_le hcard_lt (h.r_le_half_countMean j)
    calc
      mu (blockFailure h.lo h.hi h.M j)
          ≤ mu ((h.good j)ᶜ ∪ ((h.good j ∩ few) ∪ overlap)) := by
            exact
              measure_mono
                (blockFailure_subset_trackBThreshold_good_compl_union_few_union_overlapMany
                  h.lo h.hi h.M h.buffer h.testSet h.good h.core h.remainder h.r j
                  (h.testSet_in_block j) (h.absorb · j ·))
      _ ≤ mu (h.good j)ᶜ + (mu (h.good j ∩ few) + mu overlap) := by
            calc
              mu ((h.good j)ᶜ ∪ ((h.good j ∩ few) ∪ overlap))
                  ≤ mu (h.good j)ᶜ + mu ((h.good j ∩ few) ∪ overlap) :=
                    measure_union_le (h.good j)ᶜ ((h.good j ∩ few) ∪ overlap)
              _ ≤ mu (h.good j)ᶜ + (mu (h.good j ∩ few) + mu overlap) := by
                    gcongr
                    exact measure_union_le (h.good j ∩ few) overlap
      _ ≤ h.failGood j +
            (ENNReal.ofReal
              (4 * h.countSecond j / h.countMean j ^ 2) +
              h.failOverlap j) := by
            gcongr
            · exact h.prob_good_compl j
            · calc
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
            · exact h.prob_overlap_many j
      _ = h.failGood j +
            ENNReal.ofReal
              (4 * h.countSecond j / h.countMean j ^ 2) +
            h.failOverlap j := by
            simp [add_assoc]

/-- Direct closure from the abstract Track B threshold-abundance certificate. -/
theorem erdos1144_of_trackBThresholdAbundanceCertificate
    (h : TrackBThresholdAbundanceCertificate) :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    (positiveBlockOmega_of_trackBThresholdAbundanceCertificate h)

end Problem1144
end Erdos
