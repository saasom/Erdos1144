import Erdos.Problem1144.HarperSelector

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-- Test points whose large-prime process exceeds the threshold `M + buffer`. -/
noncomputable def largePrimeExceedanceSet
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (omega : Omega) (j : ℕ) : Finset ℕ :=
  by
    classical
    exact
      (testSet j).filter fun N =>
        M j + buffer j ≤ largePrimeProcess omega (cut j) (N + 1)

/-- Test points whose smooth process is below the negative buffer. -/
noncomputable def smoothBadSet
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (buffer : ℕ → ℝ)
    (omega : Omega) (j : ℕ) : Finset ℕ :=
  by
    classical
    exact
      (testSet j).filter fun N =>
        smoothProcess omega (cut j) (N + 1) < -buffer j

/-- Test points where the large-prime threshold is exceeded and the smooth
process is bad. This is the finite overlap controlled by the
threshold-selector bridge. -/
noncomputable def thresholdSmoothOverlapSet
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (omega : Omega) (j : ℕ) : Finset ℕ :=
  by
    classical
    exact
      (testSet j).filter fun N =>
        M j + buffer j ≤ largePrimeProcess omega (cut j) (N + 1) ∧
          smoothProcess omega (cut j) (N + 1) < -buffer j

theorem mem_largePrimeExceedanceSet
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (omega : Omega) (j N : ℕ) :
    N ∈ largePrimeExceedanceSet testSet cut M buffer omega j ↔
      N ∈ testSet j ∧
        M j + buffer j ≤ largePrimeProcess omega (cut j) (N + 1) := by
  classical
  unfold largePrimeExceedanceSet
  simp

theorem mem_smoothBadSet
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (buffer : ℕ → ℝ)
    (omega : Omega) (j N : ℕ) :
    N ∈ smoothBadSet testSet cut buffer omega j ↔
      N ∈ testSet j ∧
        smoothProcess omega (cut j) (N + 1) < -buffer j := by
  classical
  unfold smoothBadSet
  simp

theorem mem_thresholdSmoothOverlapSet
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (omega : Omega) (j N : ℕ) :
    N ∈ thresholdSmoothOverlapSet testSet cut M buffer omega j ↔
      N ∈ testSet j ∧
        M j + buffer j ≤ largePrimeProcess omega (cut j) (N + 1) ∧
          smoothProcess omega (cut j) (N + 1) < -buffer j := by
  classical
  unfold thresholdSmoothOverlapSet
  simp

/-- Event that there are fewer than the requested number of large-prime
threshold exceedances. -/
def thresholdFewExceedances
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (r : ℕ → ℕ) (j : ℕ) : Set Omega :=
  {omega |
    (largePrimeExceedanceSet testSet cut M buffer omega j).card < r j}

/-- Event that the threshold/smooth-bad overlap has at least the requested
cardinality. -/
def thresholdSmoothOverlapMany
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (r : ℕ → ℕ) (j : ℕ) : Set Omega :=
  {omega |
    r j ≤ (thresholdSmoothOverlapSet testSet cut M buffer omega j).card}

/-- Under block failure, every large-prime threshold exceedance must have bad
smooth remainder; otherwise absorption gives a block success. -/
theorem largePrimeExceedanceSet_subset_thresholdSmoothOverlapSet_of_blockFailure
    (lo hi cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (testSet : ℕ → Finset ℕ) (omega : Omega) (j : ℕ)
    (testSet_in_block :
      ∀ N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j))
    (testSet_in_range :
      ∀ N, N ∈ testSet j → N + 1 < (cut j) ^ 2)
    (hfail : omega ∈ blockFailure lo hi M j) :
    largePrimeExceedanceSet testSet cut M buffer omega j ⊆
      thresholdSmoothOverlapSet testSet cut M buffer omega j := by
  intro N hN
  rw [mem_largePrimeExceedanceSet] at hN
  rcases hN with ⟨hNtest, hlarge⟩
  rw [mem_thresholdSmoothOverlapSet]
  refine ⟨hNtest, hlarge, ?_⟩
  by_contra hsmooth_not_bad
  have hsmooth :
      -buffer j ≤ smoothProcess omega (cut j) (N + 1) :=
    not_lt.mp hsmooth_not_bad
  have hsucc : blockSuccess lo hi M omega j :=
    blockSuccess_of_largePrimeProcess_ge_of_smoothProcess_ge
      lo hi cut M buffer omega j N
      (testSet_in_block N hNtest)
      (testSet_in_range N hNtest)
      hlarge
      hsmooth
  exact hfail hsucc

/-- Deterministic threshold-selector bridge.

If a block fails, then either the good geometry event fails, or we are on the
good event with too few large-prime threshold exceedances, or the
threshold/smooth-bad overlap has cardinality at least `r j`. -/
theorem blockFailure_subset_good_compl_union_few_union_overlapMany
    (lo hi cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (testSet : ℕ → Finset ℕ) (good : ℕ → Set Omega) (r : ℕ → ℕ)
    (j : ℕ)
    (testSet_in_block :
      ∀ N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j))
    (testSet_in_range :
      ∀ N, N ∈ testSet j → N + 1 < (cut j) ^ 2) :
    blockFailure lo hi M j ⊆
      (good j)ᶜ ∪
        ((good j ∩ thresholdFewExceedances testSet cut M buffer r j) ∪
          thresholdSmoothOverlapMany testSet cut M buffer r j) := by
  intro omega hfail
  by_cases hgood : omega ∈ good j
  · by_cases hfew :
      omega ∈ thresholdFewExceedances testSet cut M buffer r j
    · exact Or.inr (Or.inl ⟨hgood, hfew⟩)
    · right
      right
      have hnotfew :
          r j ≤
            (largePrimeExceedanceSet testSet cut M buffer omega j).card :=
        not_lt.mp hfew
      have hcard :
          (largePrimeExceedanceSet testSet cut M buffer omega j).card ≤
            (thresholdSmoothOverlapSet testSet cut M buffer omega j).card :=
        Finset.card_le_card
          (largePrimeExceedanceSet_subset_thresholdSmoothOverlapSet_of_blockFailure
            lo hi cut M buffer testSet omega j
            testSet_in_block testSet_in_range hfail)
      exact le_trans hnotfew hcard
  · exact Or.inl hgood

/-- Threshold-selector certificate.

The analytic work is split into: a good-geometry failure probability, a
probability of too few large-prime threshold exceedances on the good event, and
a probability that many threshold exceedances also have bad smooth remainder. -/
structure HarperThresholdSelectorBlockCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  cut : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  testSet : ℕ → Finset ℕ
  good : ℕ → Set Omega
  r : ℕ → ℕ
  failGood : ℕ → ℝ≥0∞
  failFew : ℕ → ℝ≥0∞
  failOverlap : ℕ → ℝ≥0∞
  r_pos : ∀ j, 0 < r j
  testSet_in_block :
    ∀ j N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j)
  testSet_in_range :
    ∀ j N, N ∈ testSet j → N + 1 < (cut j) ^ 2
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  fail_summable :
    (∑' j, (failGood j + failFew j + failOverlap j)) ≠ ⊤
  prob_good_compl :
    ∀ j, mu (good j)ᶜ ≤ failGood j
  prob_few_exceedances :
    ∀ j,
      mu (good j ∩ thresholdFewExceedances testSet cut M buffer r j) ≤
        failFew j
  prob_overlap_many :
    ∀ j,
      mu (thresholdSmoothOverlapMany testSet cut M buffer r j) ≤
        failOverlap j

/-- Threshold-selector certificates imply the active positive-block
certificate. -/
noncomputable def positiveBlockOmega_of_harperThresholdSelectorBlockCertificate
    (h : HarperThresholdSelectorBlockCertificate) :
    PositiveBlockOmega where
  X := h.lo
  Y := h.hi
  M := h.M
  fail := fun j => h.failGood j + h.failFew j + h.failOverlap j
  X_tendsto := h.lo_tendsto_atTop
  M_tendsto := h.M_tendsto_atTop
  fail_summable := h.fail_summable
  prob_fail := by
    intro j
    let few :=
      thresholdFewExceedances h.testSet h.cut h.M h.buffer h.r j
    let overlap :=
      thresholdSmoothOverlapMany h.testSet h.cut h.M h.buffer h.r j
    calc
      mu (blockFailure h.lo h.hi h.M j)
          ≤ mu ((h.good j)ᶜ ∪ ((h.good j ∩ few) ∪ overlap)) := by
            exact
              measure_mono
                (blockFailure_subset_good_compl_union_few_union_overlapMany
                  h.lo h.hi h.cut h.M h.buffer h.testSet h.good h.r j
                  (h.testSet_in_block j)
                  (h.testSet_in_range j))
      _ ≤ mu (h.good j)ᶜ + mu ((h.good j ∩ few) ∪ overlap) :=
            measure_union_le _ _
      _ ≤ mu (h.good j)ᶜ + (mu (h.good j ∩ few) + mu overlap) :=
            add_le_add (le_refl _) (measure_union_le _ _)
      _ ≤ h.failGood j + (h.failFew j + h.failOverlap j) :=
            add_le_add
              (h.prob_good_compl j)
              (add_le_add
                (h.prob_few_exceedances j)
                (h.prob_overlap_many j))
      _ = h.failGood j + h.failFew j + h.failOverlap j := by
            rw [add_assoc]

/-- Direct closure from the threshold-selector certificate. -/
theorem erdos1144_of_harperThresholdSelectorBlockCertificate
    (h : HarperThresholdSelectorBlockCertificate) :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    (positiveBlockOmega_of_harperThresholdSelectorBlockCertificate h)

end Problem1144
end Erdos
