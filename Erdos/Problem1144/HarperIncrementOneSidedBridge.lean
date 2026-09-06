import Erdos.Problem1144.HarperIncrementGeometry

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-!
# One-sided increment bridge

This file isolates the deterministic part of the one-sided increment route.
Large absolute increments are not used as a substitute for #1144.  Instead, a
positive large-prime increment certifies a positive value only after the left
endpoint and the increment remainder are controlled at the selected interval.
-/

/-- Normalized value at the left endpoint of an interval. -/
noncomputable def leftValue
    (leftEnd : ℕ → ℕ → ℕ) (omega : Omega) (j r : ℕ) : ℝ :=
  normSum omega (leftEnd j r)

/-- Normalized value at the right endpoint of an interval. -/
noncomputable def rightValue
    (rightEnd : ℕ → ℕ → ℕ) (omega : Omega) (j r : ℕ) : ℝ :=
  normSum omega (rightEnd j r)

/-- Full normalized increment across an interval. -/
noncomputable def incrementValue
    (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (omega : Omega) (j r : ℕ) : ℝ :=
  rightValue rightEnd omega j r - leftValue leftEnd omega j r

/-- Large-prime part of an interval increment. -/
noncomputable def incrementLargePrime
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (omega : Omega) (j r : ℕ) : ℝ :=
  largePrimeIncrementProcess omega (cut j) (leftEnd j r) (rightEnd j r)

/-- Remainder after subtracting the large-prime increment from the full
endpoint increment. -/
noncomputable def remainderError
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (omega : Omega) (j r : ℕ) : ℝ :=
  incrementValue leftEnd rightEnd omega j r -
    incrementLargePrime cut leftEnd rightEnd omega j r

/-- One-sided success for a selected interval. -/
def positiveIncrementSuccess
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (U bufferLeft bufferErr : ℕ → ℝ)
    (omega : Omega) (j r : ℕ) : Prop :=
  U j ≤ incrementLargePrime cut leftEnd rightEnd omega j r ∧
    -bufferLeft j ≤ leftValue leftEnd omega j r ∧
      -bufferErr j ≤ remainderError cut leftEnd rightEnd omega j r

/-- A positive large-prime increment plus endpoint/remainder buffers gives a
positive right endpoint value. -/
theorem rightValue_ge_of_positiveIncrementSuccess
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (M U bufferLeft bufferErr : ℕ → ℝ)
    (omega : Omega) (j r : ℕ)
    (hmargin : M j + bufferLeft j + bufferErr j ≤ U j)
    (hsucc :
      positiveIncrementSuccess cut leftEnd rightEnd
        U bufferLeft bufferErr omega j r) :
    M j ≤ rightValue rightEnd omega j r := by
  rcases hsucc with ⟨hlarge, hleft, herr⟩
  unfold remainderError incrementValue at herr
  unfold incrementLargePrime at hlarge
  unfold leftValue at hleft
  unfold rightValue leftValue incrementLargePrime at herr
  unfold rightValue
  linarith

/-- Intervals whose large-prime increment exceeds the positive threshold. -/
noncomputable def positiveIncrementExceedanceSet
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (indexSet : ℕ → Finset ℕ) (U : ℕ → ℝ)
    (omega : Omega) (j : ℕ) : Finset ℕ := by
  classical
  exact
    (indexSet j).filter fun r =>
      U j ≤ incrementLargePrime cut leftEnd rightEnd omega j r

theorem mem_positiveIncrementExceedanceSet
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (indexSet : ℕ → Finset ℕ) (U : ℕ → ℝ)
    (omega : Omega) (j r : ℕ) :
    r ∈ positiveIncrementExceedanceSet cut leftEnd rightEnd indexSet U omega j ↔
      r ∈ indexSet j ∧
        U j ≤ incrementLargePrime cut leftEnd rightEnd omega j r := by
  classical
  unfold positiveIncrementExceedanceSet
  simp

/-- Point event that one interval has a positive large-prime increment
exceedance. -/
def positiveIncrementExceedanceEvent
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (U : ℕ → ℝ) (j r : ℕ) : Set Omega :=
  {omega | U j ≤ incrementLargePrime cut leftEnd rightEnd omega j r}

/-- Pair event that two intervals both have positive large-prime increment
exceedances. -/
def positiveIncrementPairExceedanceEvent
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (U : ℕ → ℝ) (j r s : ℕ) : Set Omega :=
  positiveIncrementExceedanceEvent cut leftEnd rightEnd U j r ∩
    positiveIncrementExceedanceEvent cut leftEnd rightEnd U j s

/-- Measurability of the large-prime increment process. -/
theorem measurable_incrementLargePrime
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (j r : ℕ) :
    Measurable fun omega : Omega =>
      incrementLargePrime cut leftEnd rightEnd omega j r := by
  unfold incrementLargePrime largePrimeIncrementProcess
  exact (measurable_largePrimeProcess (cut j) (rightEnd j r)).sub
    (measurable_largePrimeProcess (cut j) (leftEnd j r))

/-- Measurability of a one-point positive increment exceedance event. -/
theorem measurableSet_positiveIncrementExceedanceEvent
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (U : ℕ → ℝ) (j r : ℕ) :
    MeasurableSet
      (positiveIncrementExceedanceEvent cut leftEnd rightEnd U j r) := by
  unfold positiveIncrementExceedanceEvent
  exact measurableSet_le measurable_const
    (measurable_incrementLargePrime cut leftEnd rightEnd j r)

/-- Measurability of a two-point positive increment exceedance event. -/
theorem measurableSet_positiveIncrementPairExceedanceEvent
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (U : ℕ → ℝ) (j r s : ℕ) :
    MeasurableSet
      (positiveIncrementPairExceedanceEvent cut leftEnd rightEnd U j r s) := by
  exact
    (measurableSet_positiveIncrementExceedanceEvent
      cut leftEnd rightEnd U j r).inter
      (measurableSet_positiveIncrementExceedanceEvent
        cut leftEnd rightEnd U j s)

/-- Real-valued count of positive large-prime increment exceedances. -/
noncomputable def positiveIncrementExceedanceCountReal
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (indexSet : ℕ → Finset ℕ) (U : ℕ → ℝ)
    (j : ℕ) (omega : Omega) : ℝ :=
  ((positiveIncrementExceedanceSet
    cut leftEnd rightEnd indexSet U omega j).card : ℝ)

/-- Pointwise count expansion as a finite sum of event indicators. -/
theorem positiveIncrementExceedanceCountReal_eq_sum_indicator
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (indexSet : ℕ → Finset ℕ) (U : ℕ → ℝ)
    (j : ℕ) (omega : Omega) :
    positiveIncrementExceedanceCountReal
        cut leftEnd rightEnd indexSet U j omega =
      ∑ r ∈ indexSet j,
        (positiveIncrementExceedanceEvent
          cut leftEnd rightEnd U j r).indicator
          (fun _ : Omega => (1 : ℝ)) omega := by
  classical
  unfold positiveIncrementExceedanceCountReal positiveIncrementExceedanceSet
  rw [Finset.card_filter]
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  by_cases h :
      U j ≤ incrementLargePrime cut leftEnd rightEnd omega j r
  · simp [positiveIncrementExceedanceEvent, h]
  · simp [positiveIncrementExceedanceEvent, h]

/-- The pointwise square of the exceedance count expands into the double sum
of pair-exceedance indicators. -/
theorem positiveIncrementExceedanceCountReal_sq_eq_sum_pair_indicator
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (indexSet : ℕ → Finset ℕ) (U : ℕ → ℝ)
    (j : ℕ) (omega : Omega) :
    (positiveIncrementExceedanceCountReal
        cut leftEnd rightEnd indexSet U j omega) ^ 2 =
      ∑ r ∈ indexSet j, ∑ s ∈ indexSet j,
        (positiveIncrementPairExceedanceEvent
          cut leftEnd rightEnd U j r s).indicator
          (fun _ : Omega => (1 : ℝ)) omega := by
  classical
  rw [positiveIncrementExceedanceCountReal_eq_sum_indicator]
  rw [pow_two, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  refine Finset.sum_congr rfl fun s hs => ?_
  by_cases hrω :
      omega ∈ positiveIncrementExceedanceEvent cut leftEnd rightEnd U j r
  · by_cases hsω :
        omega ∈ positiveIncrementExceedanceEvent cut leftEnd rightEnd U j s
    · simp [positiveIncrementPairExceedanceEvent, hrω, hsω]
    · simp [positiveIncrementPairExceedanceEvent, hrω, hsω]
  · simp [positiveIncrementPairExceedanceEvent, hrω]

/-- The positive increment exceedance count is integrable. -/
theorem integrable_positiveIncrementExceedanceCountReal
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (indexSet : ℕ → Finset ℕ) (U : ℕ → ℝ) (j : ℕ) :
    Integrable
      (positiveIncrementExceedanceCountReal
        cut leftEnd rightEnd indexSet U j)
      mu := by
  classical
  rw [show
      positiveIncrementExceedanceCountReal
          cut leftEnd rightEnd indexSet U j =
        fun omega =>
          ∑ r ∈ indexSet j,
            (positiveIncrementExceedanceEvent
              cut leftEnd rightEnd U j r).indicator
              (fun _ : Omega => (1 : ℝ)) omega by
        funext omega
        exact positiveIncrementExceedanceCountReal_eq_sum_indicator
          cut leftEnd rightEnd indexSet U j omega]
  refine integrable_finset_sum (indexSet j) ?_
  intro r hr
  exact
    (integrable_const (1 : ℝ)).indicator
      (measurableSet_positiveIncrementExceedanceEvent
        cut leftEnd rightEnd U j r)

/-- The square of the positive increment exceedance count is integrable. -/
theorem integrable_positiveIncrementExceedanceCountReal_sq
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (indexSet : ℕ → Finset ℕ) (U : ℕ → ℝ) (j : ℕ) :
    Integrable
      (fun omega =>
        (positiveIncrementExceedanceCountReal
          cut leftEnd rightEnd indexSet U j omega) ^ 2)
      mu := by
  classical
  rw [show
      (fun omega =>
        (positiveIncrementExceedanceCountReal
          cut leftEnd rightEnd indexSet U j omega) ^ 2) =
        fun omega =>
          ∑ r ∈ indexSet j, ∑ s ∈ indexSet j,
            (positiveIncrementPairExceedanceEvent
              cut leftEnd rightEnd U j r s).indicator
              (fun _ : Omega => (1 : ℝ)) omega by
        funext omega
        exact positiveIncrementExceedanceCountReal_sq_eq_sum_pair_indicator
          cut leftEnd rightEnd indexSet U j omega]
  refine integrable_finset_sum (indexSet j) ?_
  intro r hr
  refine integrable_finset_sum (indexSet j) ?_
  intro s hs
  exact
    (integrable_const (1 : ℝ)).indicator
      (measurableSet_positiveIncrementPairExceedanceEvent
        cut leftEnd rightEnd U j r s)

/-- First-moment identity for the exceedance count. -/
theorem integral_positiveIncrementExceedanceCountReal
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (indexSet : ℕ → Finset ℕ) (U : ℕ → ℝ) (j : ℕ) :
    (∫ omega,
      positiveIncrementExceedanceCountReal
        cut leftEnd rightEnd indexSet U j omega ∂mu)
      =
    ∑ r ∈ indexSet j,
      mu.real
        (positiveIncrementExceedanceEvent
          cut leftEnd rightEnd U j r) := by
  classical
  rw [show
      (fun omega =>
        positiveIncrementExceedanceCountReal
          cut leftEnd rightEnd indexSet U j omega) =
        fun omega =>
          ∑ r ∈ indexSet j,
            (positiveIncrementExceedanceEvent
              cut leftEnd rightEnd U j r).indicator
              (fun _ : Omega => (1 : ℝ)) omega by
        funext omega
        exact positiveIncrementExceedanceCountReal_eq_sum_indicator
          cut leftEnd rightEnd indexSet U j omega]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun r hr => ?_
    exact
      MeasureTheory.integral_indicator_one
        (measurableSet_positiveIncrementExceedanceEvent
          cut leftEnd rightEnd U j r)
  · intro r hr
    exact
      (integrable_const (1 : ℝ)).indicator
        (measurableSet_positiveIncrementExceedanceEvent
          cut leftEnd rightEnd U j r)

/-- Raw second-moment identity for the exceedance count. -/
theorem integral_positiveIncrementExceedanceCountReal_sq
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (indexSet : ℕ → Finset ℕ) (U : ℕ → ℝ) (j : ℕ) :
    (∫ omega,
      (positiveIncrementExceedanceCountReal
        cut leftEnd rightEnd indexSet U j omega) ^ 2 ∂mu)
      =
    ∑ r ∈ indexSet j, ∑ s ∈ indexSet j,
      mu.real
        (positiveIncrementPairExceedanceEvent
          cut leftEnd rightEnd U j r s) := by
  classical
  rw [show
      (fun omega =>
        (positiveIncrementExceedanceCountReal
          cut leftEnd rightEnd indexSet U j omega) ^ 2) =
        fun omega =>
          ∑ r ∈ indexSet j, ∑ s ∈ indexSet j,
            (positiveIncrementPairExceedanceEvent
              cut leftEnd rightEnd U j r s).indicator
              (fun _ : Omega => (1 : ℝ)) omega by
        funext omega
        exact positiveIncrementExceedanceCountReal_sq_eq_sum_pair_indicator
          cut leftEnd rightEnd indexSet U j omega]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun r hr => ?_
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun s hs => ?_
      exact
        MeasureTheory.integral_indicator_one
          (measurableSet_positiveIncrementPairExceedanceEvent
            cut leftEnd rightEnd U j r s)
    · intro s hs
      exact
        (integrable_const (1 : ℝ)).indicator
          (measurableSet_positiveIncrementPairExceedanceEvent
            cut leftEnd rightEnd U j r s)
  · intro r hr
    refine integrable_finset_sum (indexSet j) ?_
    intro s hs
    exact
      (integrable_const (1 : ℝ)).indicator
        (measurableSet_positiveIncrementPairExceedanceEvent
          cut leftEnd rightEnd U j r s)

/-- Event that there are too few positive large-prime increment exceedances. -/
def incrementFewPositiveExceedances
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (indexSet : ℕ → Finset ℕ) (U : ℕ → ℝ)
    (r : ℕ → ℕ) (j : ℕ) : Set Omega :=
  {omega |
    (positiveIncrementExceedanceSet
      cut leftEnd rightEnd indexSet U omega j).card < r j}

/-- Count-moment abundance certificate for positive increment exceedances.

This is the one-sided analogue of `HarperIncrementAbundanceCertificate`.  It
does not prove any Gaussian/Rademacher comparison itself; it is the finite
Chebyshev target that those comparison estimates must instantiate. -/
structure PositiveIncrementAbundanceCertificate where
  cut : ℕ → ℕ
  leftEnd : ℕ → ℕ → ℕ
  rightEnd : ℕ → ℕ → ℕ
  indexSet : ℕ → Finset ℕ
  U : ℕ → ℝ
  r : ℕ → ℕ
  countMean : ℕ → ℝ
  countSecond : ℕ → ℝ
  r_pos : ∀ j, 0 < r j
  countMean_pos : ∀ j, 0 < countMean j
  r_le_half_countMean : ∀ j, (r j : ℝ) ≤ countMean j / 2
  count_centered_second_integrable :
    ∀ j,
      Integrable
        (fun omega =>
          (positiveIncrementExceedanceCountReal
              cut leftEnd rightEnd indexSet U j omega -
            ∫ omega',
              positiveIncrementExceedanceCountReal
                cut leftEnd rightEnd indexSet U j omega' ∂mu) ^ 2)
        mu
  count_mean_lower :
    ∀ j,
      countMean j ≤
        ∫ omega,
          positiveIncrementExceedanceCountReal
            cut leftEnd rightEnd indexSet U j omega ∂mu
  count_centered_second_upper :
    ∀ j,
      (∫ omega,
          (positiveIncrementExceedanceCountReal
              cut leftEnd rightEnd indexSet U j omega -
            ∫ omega',
              positiveIncrementExceedanceCountReal
                cut leftEnd rightEnd indexSet U j omega' ∂mu) ^ 2 ∂mu)
        ≤ countSecond j

/-- Centered second moments are controlled by raw second moments on the
probability space. The harmless factor `4` keeps this lemma robust and avoids
needing an exact variance identity. -/
theorem centered_second_le_four_raw_second
    (D : Omega → ℝ)
    (hD_int : Integrable D mu)
    (hD2_int : Integrable (fun omega => D omega ^ 2) mu) :
    (∫ omega, (D omega - ∫ omega, D omega ∂mu) ^ 2 ∂mu)
      ≤ 4 * ∫ omega, D omega ^ 2 ∂mu := by
  let m : ℝ := ∫ omega, D omega ∂mu
  have hpoly : ∀ x : ℝ, (x - m) ^ 2 ≤ 2 * (x ^ 2 + m ^ 2) := by
    intro x
    nlinarith [sq_nonneg (x - m), sq_nonneg (x + m)]
  have hbound_ae :
      (fun omega => (D omega - m) ^ 2) ≤ᵐ[mu]
        (fun omega => 2 * (D omega ^ 2 + m ^ 2)) :=
    ae_of_all _ fun omega => hpoly (D omega)
  have hmajor_int :
      Integrable (fun omega => 2 * (D omega ^ 2 + m ^ 2)) mu := by
    exact (hD2_int.add (integrable_const (m ^ 2))).const_mul 2
  have hcenter_int : Integrable (fun omega => (D omega - m) ^ 2) mu := by
    refine Integrable.mono' hmajor_int ?_ ?_
    · exact (((hD_int.sub (integrable_const m)).aemeasurable.pow_const 2).aestronglyMeasurable)
    · filter_upwards [hbound_ae] with omega homega
      rw [Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ (D omega - m) ^ 2)]
      exact homega
  have hle_int :
      (∫ omega, (D omega - m) ^ 2 ∂mu) ≤
        ∫ omega, 2 * (D omega ^ 2 + m ^ 2) ∂mu :=
    integral_mono_ae hcenter_int hmajor_int hbound_ae
  have hc : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => x ^ 2) := by
    simpa using ((by norm_num : Even 2).convexOn_pow (𝕜 := ℝ))
  have hcont : ContinuousOn (fun x : ℝ => x ^ 2) (Set.univ : Set ℝ) := by
    fun_prop
  have hmap : (∀ᵐ omega ∂mu, D omega ∈ (Set.univ : Set ℝ)) := by
    simp
  have hmean2 : m ^ 2 ≤ ∫ omega, D omega ^ 2 ∂mu := by
    simpa [m] using
      ConvexOn.map_integral_le (μ := mu) hc hcont isClosed_univ hmap
        hD_int hD2_int
  have hmajor_eval :
      (∫ omega, 2 * (D omega ^ 2 + m ^ 2) ∂mu)
        = 2 * (∫ omega, D omega ^ 2 ∂mu) + 2 * m ^ 2 := by
    calc
      (∫ omega, 2 * (D omega ^ 2 + m ^ 2) ∂mu)
          = ∫ omega, (2 * D omega ^ 2 + 2 * m ^ 2) ∂mu := by
            congr 1
            ext omega
            ring
      _ = (∫ omega, 2 * D omega ^ 2 ∂mu) +
            ∫ omega, 2 * m ^ 2 ∂mu := by
            rw [integral_add]
            · exact (hD2_int.const_mul 2)
            · exact integrable_const (2 * m ^ 2)
      _ = 2 * (∫ omega, D omega ^ 2 ∂mu) + 2 * m ^ 2 := by
            rw [integral_const_mul 2 (fun omega => D omega ^ 2)]
            simp [integral_const]
  rw [show
      (∫ omega, (D omega - ∫ omega, D omega ∂mu) ^ 2 ∂mu)
        = ∫ omega, (D omega - m) ^ 2 ∂mu by rfl]
  calc
    (∫ omega, (D omega - m) ^ 2 ∂mu)
        ≤ ∫ omega, 2 * (D omega ^ 2 + m ^ 2) ∂mu := hle_int
    _ = 2 * (∫ omega, D omega ^ 2 ∂mu) + 2 * m ^ 2 := hmajor_eval
    _ ≤ 4 * ∫ omega, D omega ^ 2 ∂mu := by nlinarith

/-- Positive increment abundance certificate using a raw second-moment bound.

One- and two-point tail estimates naturally control `E R_j^2`. This structure
keeps that analytic input separate and uses `centered_second_le_four_raw_second`
to produce the centered-second field required by
`PositiveIncrementAbundanceCertificate`. -/
structure PositiveIncrementRawSecondMomentCertificate where
  cut : ℕ → ℕ
  leftEnd : ℕ → ℕ → ℕ
  rightEnd : ℕ → ℕ → ℕ
  indexSet : ℕ → Finset ℕ
  U : ℕ → ℝ
  r : ℕ → ℕ
  countMean : ℕ → ℝ
  countRawSecond : ℕ → ℝ
  r_pos : ∀ j, 0 < r j
  countMean_pos : ∀ j, 0 < countMean j
  r_le_half_countMean : ∀ j, (r j : ℝ) ≤ countMean j / 2
  count_integrable :
    ∀ j,
      Integrable
        (positiveIncrementExceedanceCountReal
          cut leftEnd rightEnd indexSet U j)
        mu
  count_sq_integrable :
    ∀ j,
      Integrable
        (fun omega =>
          (positiveIncrementExceedanceCountReal
            cut leftEnd rightEnd indexSet U j omega) ^ 2)
        mu
  count_mean_lower :
    ∀ j,
      countMean j ≤
        ∫ omega,
          positiveIncrementExceedanceCountReal
            cut leftEnd rightEnd indexSet U j omega ∂mu
  count_raw_second_upper :
    ∀ j,
      (∫ omega,
          (positiveIncrementExceedanceCountReal
            cut leftEnd rightEnd indexSet U j omega) ^ 2 ∂mu)
        ≤ countRawSecond j

/-- One- and two-point positive tail bounds for the exceedance count.

This is the finite probabilistic target supplied by the later
Rademacher/Gaussian comparison layer: lower bounds for individual positive
increment tails, upper bounds for pair tails, and deterministic arithmetic
budgets turning those tail estimates into the count mean and raw second
moment needed for Chebyshev. -/
structure PositiveIncrementTailProbabilityCertificate where
  cut : ℕ → ℕ
  leftEnd : ℕ → ℕ → ℕ
  rightEnd : ℕ → ℕ → ℕ
  indexSet : ℕ → Finset ℕ
  U : ℕ → ℝ
  r : ℕ → ℕ
  tailLower : ℕ → ℕ → ℝ
  pairUpper : ℕ → ℕ → ℕ → ℝ
  countMean : ℕ → ℝ
  countRawSecond : ℕ → ℝ
  r_pos : ∀ j, 0 < r j
  countMean_pos : ∀ j, 0 < countMean j
  r_le_half_countMean : ∀ j, (r j : ℝ) ≤ countMean j / 2
  countMean_le_tailLower_sum :
    ∀ j,
      countMean j ≤
        ∑ r ∈ indexSet j, tailLower j r
  pairUpper_sum_le_countRawSecond :
    ∀ j,
      (∑ r ∈ indexSet j, ∑ s ∈ indexSet j, pairUpper j r s)
        ≤ countRawSecond j
  tailLower_le_prob :
    ∀ (j r : ℕ), r ∈ indexSet j →
      tailLower j r ≤
        mu.real
          (positiveIncrementExceedanceEvent
            cut leftEnd rightEnd U j r)
  pair_prob_le_pairUpper :
    ∀ (j r s : ℕ), r ∈ indexSet j → s ∈ indexSet j →
      mu.real
        (positiveIncrementPairExceedanceEvent
          cut leftEnd rightEnd U j r s)
        ≤ pairUpper j r s

/-- Uniform one- and two-point tail package for a fixed positive-increment mesh.

This is the shape expected from the finite Rademacher/Gaussian comparison on a
pairwise-good increment mesh: a common lower tail `beta`, a common one-point
upper tail for diagonal second-moment terms, and a common off-diagonal pair
tail. The arithmetic budgets are still explicit finite sums, so later
parameter choices can keep constants transparent. -/
structure PositiveIncrementUniformTailProbabilityCertificate where
  cut : ℕ → ℕ
  leftEnd : ℕ → ℕ → ℕ
  rightEnd : ℕ → ℕ → ℕ
  indexSet : ℕ → Finset ℕ
  U : ℕ → ℝ
  r : ℕ → ℕ
  beta : ℕ → ℝ
  tailUpper : ℕ → ℝ
  pairUpper : ℕ → ℝ
  countMean : ℕ → ℝ
  countRawSecond : ℕ → ℝ
  r_pos : ∀ j, 0 < r j
  countMean_pos : ∀ j, 0 < countMean j
  r_le_half_countMean : ∀ j, (r j : ℝ) ≤ countMean j / 2
  countMean_le_beta_sum :
    ∀ j,
      countMean j ≤
        ∑ _r ∈ indexSet j, beta j
  pairBudget_le_countRawSecond :
    ∀ j,
      (∑ r ∈ indexSet j, ∑ s ∈ indexSet j,
        if r = s then tailUpper j else pairUpper j)
        ≤ countRawSecond j
  beta_le_tail_prob :
    ∀ (j r : ℕ), r ∈ indexSet j →
      beta j ≤
        mu.real
          (positiveIncrementExceedanceEvent
            cut leftEnd rightEnd U j r)
  tail_prob_le_tailUpper :
    ∀ (j r : ℕ), r ∈ indexSet j →
      mu.real
        (positiveIncrementExceedanceEvent
          cut leftEnd rightEnd U j r)
        ≤ tailUpper j
  offdiag_pair_prob_le_pairUpper :
    ∀ (j r s : ℕ), r ∈ indexSet j → s ∈ indexSet j → r ≠ s →
      mu.real
        (positiveIncrementPairExceedanceEvent
          cut leftEnd rightEnd U j r s)
        ≤ pairUpper j

/-- Uniform tail packages imply the more general tail-probability
certificate. Diagonal pair terms are bounded by the one-point upper tail; all
off-diagonal terms are bounded by the product-size pair upper tail. -/
noncomputable def positiveIncrementTailProbabilityCertificate_of_uniform
    (h : PositiveIncrementUniformTailProbabilityCertificate) :
    PositiveIncrementTailProbabilityCertificate where
  cut := h.cut
  leftEnd := h.leftEnd
  rightEnd := h.rightEnd
  indexSet := h.indexSet
  U := h.U
  r := h.r
  tailLower := fun j _r => h.beta j
  pairUpper := fun j r s =>
    if r = s then h.tailUpper j else h.pairUpper j
  countMean := h.countMean
  countRawSecond := h.countRawSecond
  r_pos := h.r_pos
  countMean_pos := h.countMean_pos
  r_le_half_countMean := h.r_le_half_countMean
  countMean_le_tailLower_sum := h.countMean_le_beta_sum
  pairUpper_sum_le_countRawSecond := h.pairBudget_le_countRawSecond
  tailLower_le_prob := h.beta_le_tail_prob
  pair_prob_le_pairUpper := by
    intro j r s hr hs
    by_cases hrs : r = s
    · subst s
      have hsubset :
          positiveIncrementPairExceedanceEvent
              h.cut h.leftEnd h.rightEnd h.U j r r ⊆
            positiveIncrementExceedanceEvent
              h.cut h.leftEnd h.rightEnd h.U j r := by
        intro omega homega
        exact homega.1
      have hdiag :
          mu.real
              (positiveIncrementPairExceedanceEvent
                h.cut h.leftEnd h.rightEnd h.U j r r)
            ≤
          mu.real
              (positiveIncrementExceedanceEvent
                h.cut h.leftEnd h.rightEnd h.U j r) :=
        measureReal_mono hsubset
      simpa using (hdiag.trans (h.tail_prob_le_tailUpper j r hr))
    · simpa [hrs] using h.offdiag_pair_prob_le_pairUpper j r s hr hs hrs

/-- Tail-probability certificates imply raw second-moment count certificates.

All measure-theoretic content here is finite: exact integral identities for
the count and its square reduce the problem to one-point and two-point event
probabilities. -/
noncomputable def positiveIncrementRawSecondMomentCertificate_of_tailProbability
    (h : PositiveIncrementTailProbabilityCertificate) :
    PositiveIncrementRawSecondMomentCertificate where
  cut := h.cut
  leftEnd := h.leftEnd
  rightEnd := h.rightEnd
  indexSet := h.indexSet
  U := h.U
  r := h.r
  countMean := h.countMean
  countRawSecond := h.countRawSecond
  r_pos := h.r_pos
  countMean_pos := h.countMean_pos
  r_le_half_countMean := h.r_le_half_countMean
  count_integrable := by
    intro j
    exact integrable_positiveIncrementExceedanceCountReal
      h.cut h.leftEnd h.rightEnd h.indexSet h.U j
  count_sq_integrable := by
    intro j
    exact integrable_positiveIncrementExceedanceCountReal_sq
      h.cut h.leftEnd h.rightEnd h.indexSet h.U j
  count_mean_lower := by
    intro j
    calc
      h.countMean j
          ≤ ∑ r ∈ h.indexSet j, h.tailLower j r :=
            h.countMean_le_tailLower_sum j
      _ ≤
          ∑ r ∈ h.indexSet j,
            mu.real
              (positiveIncrementExceedanceEvent
                h.cut h.leftEnd h.rightEnd h.U j r) := by
            refine Finset.sum_le_sum fun r hr => ?_
            exact h.tailLower_le_prob j r hr
      _ =
          ∫ omega,
            positiveIncrementExceedanceCountReal
              h.cut h.leftEnd h.rightEnd h.indexSet h.U j omega ∂mu := by
            exact
              (integral_positiveIncrementExceedanceCountReal
                h.cut h.leftEnd h.rightEnd h.indexSet h.U j).symm
  count_raw_second_upper := by
    intro j
    calc
      (∫ omega,
          (positiveIncrementExceedanceCountReal
            h.cut h.leftEnd h.rightEnd h.indexSet h.U j omega) ^ 2 ∂mu)
          =
          ∑ r ∈ h.indexSet j, ∑ s ∈ h.indexSet j,
            mu.real
              (positiveIncrementPairExceedanceEvent
                h.cut h.leftEnd h.rightEnd h.U j r s) :=
            integral_positiveIncrementExceedanceCountReal_sq
              h.cut h.leftEnd h.rightEnd h.indexSet h.U j
      _ ≤
          ∑ r ∈ h.indexSet j, ∑ s ∈ h.indexSet j,
            h.pairUpper j r s := by
            refine Finset.sum_le_sum fun r hr => ?_
            refine Finset.sum_le_sum fun s hs => ?_
            exact h.pair_prob_le_pairUpper j r s hr hs
      _ ≤ h.countRawSecond j :=
            h.pairUpper_sum_le_countRawSecond j

/-- Raw-second-moment certificates imply centered-second abundance
certificates, with the explicit factor `4`. -/
noncomputable def positiveIncrementAbundanceCertificate_of_rawSecond
    (h : PositiveIncrementRawSecondMomentCertificate) :
    PositiveIncrementAbundanceCertificate where
  cut := h.cut
  leftEnd := h.leftEnd
  rightEnd := h.rightEnd
  indexSet := h.indexSet
  U := h.U
  r := h.r
  countMean := h.countMean
  countSecond := fun j => 4 * h.countRawSecond j
  r_pos := h.r_pos
  countMean_pos := h.countMean_pos
  r_le_half_countMean := h.r_le_half_countMean
  count_centered_second_integrable := by
    intro j
    let D : Omega → ℝ :=
      positiveIncrementExceedanceCountReal
        h.cut h.leftEnd h.rightEnd h.indexSet h.U j
    have hmajor_int :
        Integrable (fun omega => 2 *
          (D omega ^ 2 + (∫ omega, D omega ∂mu) ^ 2)) mu := by
      exact ((h.count_sq_integrable j).add
        (integrable_const ((∫ omega, D omega ∂mu) ^ 2))).const_mul 2
    refine Integrable.mono' hmajor_int ?_ ?_
    · exact
        ((((h.count_integrable j).sub
          (integrable_const (∫ omega, D omega ∂mu))).aemeasurable.pow_const 2).aestronglyMeasurable)
    · filter_upwards [] with omega
      rw [Real.norm_eq_abs,
        abs_of_nonneg
          (by positivity :
            0 ≤ (D omega - ∫ omega, D omega ∂mu) ^ 2)]
      have hpoly :
          (D omega - ∫ omega, D omega ∂mu) ^ 2 ≤
            2 * (D omega ^ 2 + (∫ omega, D omega ∂mu) ^ 2) := by
        nlinarith [sq_nonneg (D omega - ∫ omega, D omega ∂mu),
          sq_nonneg (D omega + ∫ omega, D omega ∂mu)]
      exact hpoly
  count_mean_lower := h.count_mean_lower
  count_centered_second_upper := by
    intro j
    let D : Omega → ℝ :=
      positiveIncrementExceedanceCountReal
        h.cut h.leftEnd h.rightEnd h.indexSet h.U j
    calc
      (∫ omega,
          (D omega - ∫ omega', D omega' ∂mu) ^ 2 ∂mu)
          ≤ 4 * ∫ omega, D omega ^ 2 ∂mu :=
            centered_second_le_four_raw_second
              (D := D) (h.count_integrable j) (h.count_sq_integrable j)
      _ ≤ 4 * h.countRawSecond j := by
            exact mul_le_mul_of_nonneg_left
              (h.count_raw_second_upper j) (by norm_num : (0 : ℝ) ≤ 4)

/-- Positive increment abundance lower-tail bound. -/
theorem measure_incrementFewPositiveExceedances_le
    (h : PositiveIncrementAbundanceCertificate) (j : ℕ) :
    mu (incrementFewPositiveExceedances
      h.cut h.leftEnd h.rightEnd h.indexSet h.U h.r j)
      ≤ ENNReal.ofReal (4 * h.countSecond j / h.countMean j ^ 2) := by
  let R : Omega → ℝ :=
    positiveIncrementExceedanceCountReal
      h.cut h.leftEnd h.rightEnd h.indexSet h.U j
  let few : Set Omega :=
    incrementFewPositiveExceedances
      h.cut h.leftEnd h.rightEnd h.indexSet h.U h.r j
  have hfew_subset :
      few ⊆ {omega | R omega < h.countMean j / 2} := by
    intro omega hfew
    have hcard_lt :
        ((positiveIncrementExceedanceSet
            h.cut h.leftEnd h.rightEnd h.indexSet h.U omega j).card : ℝ)
          < (h.r j : ℝ) :=
      Nat.cast_lt.mpr hfew
    have hRdef :
        R omega =
          ((positiveIncrementExceedanceSet
            h.cut h.leftEnd h.rightEnd h.indexSet h.U omega j).card : ℝ) :=
      rfl
    change R omega < h.countMean j / 2
    rw [hRdef]
    exact lt_of_lt_of_le hcard_lt (h.r_le_half_countMean j)
  calc
    mu few ≤ mu {omega | R omega < h.countMean j / 2} :=
      measure_mono hfew_subset
    _ ≤ ENNReal.ofReal (4 * h.countSecond j / h.countMean j ^ 2) := by
      exact measure_lt_half_mean_le_centered_second
        (R := R) (m := h.countMean j) (V := h.countSecond j)
        (h.countMean_pos j)
        (by simpa [R] using h.count_centered_second_integrable j)
        (by simpa [R] using h.count_mean_lower j)
        (by simpa [R] using h.count_centered_second_upper j)

/-- The selected interval has a bad left endpoint. -/
def selectedLeftBad
    (leftEnd : ℕ → ℕ → ℕ) (bufferLeft : ℕ → ℝ)
    (selector : ℕ → Omega → ℕ) (j : ℕ) : Set Omega :=
  {omega | leftValue leftEnd omega j (selector j omega) < -bufferLeft j}

/-- The selected interval has a bad non-large-prime remainder. -/
def selectedRemainderBad
    (cut : ℕ → ℕ) (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (bufferErr : ℕ → ℝ) (selector : ℕ → Omega → ℕ)
    (j : ℕ) : Set Omega :=
  {omega |
    remainderError cut leftEnd rightEnd omega j (selector j omega) <
      -bufferErr j}

/-- If a block fails, then a valid positive-increment selector must either be
unavailable, have a bad left endpoint, or have a bad remainder. -/
theorem blockFailure_subset_increment_few_union_selected_bad
    (lo hi cut : ℕ → ℕ)
    (leftEnd rightEnd : ℕ → ℕ → ℕ)
    (indexSet : ℕ → Finset ℕ)
    (selector : ℕ → Omega → ℕ)
    (M U bufferLeft bufferErr : ℕ → ℝ)
    (r : ℕ → ℕ) (j : ℕ)
    (rightEnd_in_block :
      ∀ r, r ∈ indexSet j → rightEnd j r ∈ Finset.Icc (lo j) (hi j))
    (hmargin : M j + bufferLeft j + bufferErr j ≤ U j)
    (selector_mem_of_not_few :
      ∀ omega,
        omega ∉ incrementFewPositiveExceedances
          cut leftEnd rightEnd indexSet U r j →
        selector j omega ∈
          positiveIncrementExceedanceSet
            cut leftEnd rightEnd indexSet U omega j) :
    blockFailure lo hi M j ⊆
      incrementFewPositiveExceedances cut leftEnd rightEnd indexSet U r j ∪
        (selectedLeftBad leftEnd bufferLeft selector j ∪
          selectedRemainderBad cut leftEnd rightEnd bufferErr selector j) := by
  intro omega hfail
  by_cases hfew :
      omega ∈ incrementFewPositiveExceedances
        cut leftEnd rightEnd indexSet U r j
  · exact Or.inl hfew
  · right
    by_cases hleftbad :
        omega ∈ selectedLeftBad leftEnd bufferLeft selector j
    · exact Or.inl hleftbad
    · right
      by_cases herrbad :
          omega ∈ selectedRemainderBad
            cut leftEnd rightEnd bufferErr selector j
      · exact herrbad
      · exfalso
        have hsel_mem :=
          selector_mem_of_not_few omega hfew
        rw [mem_positiveIncrementExceedanceSet] at hsel_mem
        rcases hsel_mem with ⟨hsel_index, hlarge⟩
        have hleft :
            -bufferLeft j ≤
              leftValue leftEnd omega j (selector j omega) :=
          not_lt.mp hleftbad
        have herr :
            -bufferErr j ≤
              remainderError cut leftEnd rightEnd omega j (selector j omega) :=
          not_lt.mp herrbad
        have hright :
            M j ≤ rightValue rightEnd omega j (selector j omega) :=
          rightValue_ge_of_positiveIncrementSuccess
            cut leftEnd rightEnd M U bufferLeft bufferErr omega j
            (selector j omega) hmargin ⟨hlarge, hleft, herr⟩
        have hblock : blockSuccess lo hi M omega j :=
          ⟨rightEnd j (selector j omega),
            rightEnd_in_block (selector j omega) hsel_index,
            hright⟩
        exact hfail hblock

/-- A one-sided increment bridge certificate.

The analytic proof is responsible for constructing a selector that picks a
positive large-prime increment when there are sufficiently many exceedances,
and for bounding the selected left-endpoint and selected-remainder bad events. -/
structure OneSidedIncrementBridgeCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  cut : ℕ → ℕ
  leftEnd : ℕ → ℕ → ℕ
  rightEnd : ℕ → ℕ → ℕ
  indexSet : ℕ → Finset ℕ
  selector : ℕ → Omega → ℕ
  M : ℕ → ℝ
  U : ℕ → ℝ
  bufferLeft : ℕ → ℝ
  bufferErr : ℕ → ℝ
  r : ℕ → ℕ
  failIncrement : ℕ → ℝ≥0∞
  failLeft : ℕ → ℝ≥0∞
  failRemainder : ℕ → ℝ≥0∞
  r_pos : ∀ j, 0 < r j
  rightEnd_in_block :
    ∀ j r, r ∈ indexSet j → rightEnd j r ∈ Finset.Icc (lo j) (hi j)
  margin : ∀ j, M j + bufferLeft j + bufferErr j ≤ U j
  selector_mem_of_not_few :
    ∀ j omega,
      omega ∉ incrementFewPositiveExceedances
        cut leftEnd rightEnd indexSet U r j →
      selector j omega ∈
        positiveIncrementExceedanceSet
          cut leftEnd rightEnd indexSet U omega j
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  fail_summable :
    (∑' j, (failIncrement j + failLeft j + failRemainder j)) ≠ ⊤
  prob_few_increment :
    ∀ j,
      mu (incrementFewPositiveExceedances
        cut leftEnd rightEnd indexSet U r j) ≤ failIncrement j
  prob_selected_left_bad :
    ∀ j,
      mu (selectedLeftBad leftEnd bufferLeft selector j) ≤ failLeft j
  prob_selected_remainder_bad :
    ∀ j,
      mu (selectedRemainderBad
        cut leftEnd rightEnd bufferErr selector j) ≤ failRemainder j

/-- One-sided increment bridge with the positive-increment failure supplied by
a finite second-moment abundance estimate. -/
structure OneSidedIncrementBridgeAbundanceCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  cut : ℕ → ℕ
  leftEnd : ℕ → ℕ → ℕ
  rightEnd : ℕ → ℕ → ℕ
  indexSet : ℕ → Finset ℕ
  selector : ℕ → Omega → ℕ
  M : ℕ → ℝ
  U : ℕ → ℝ
  bufferLeft : ℕ → ℝ
  bufferErr : ℕ → ℝ
  r : ℕ → ℕ
  countMean : ℕ → ℝ
  countSecond : ℕ → ℝ
  failLeft : ℕ → ℝ≥0∞
  failRemainder : ℕ → ℝ≥0∞
  r_pos : ∀ j, 0 < r j
  countMean_pos : ∀ j, 0 < countMean j
  r_le_half_countMean : ∀ j, (r j : ℝ) ≤ countMean j / 2
  rightEnd_in_block :
    ∀ j r, r ∈ indexSet j → rightEnd j r ∈ Finset.Icc (lo j) (hi j)
  margin : ∀ j, M j + bufferLeft j + bufferErr j ≤ U j
  selector_mem_of_not_few :
    ∀ j omega,
      omega ∉ incrementFewPositiveExceedances
        cut leftEnd rightEnd indexSet U r j →
      selector j omega ∈
        positiveIncrementExceedanceSet
          cut leftEnd rightEnd indexSet U omega j
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  count_centered_second_integrable :
    ∀ j,
      Integrable
        (fun omega =>
          (positiveIncrementExceedanceCountReal
              cut leftEnd rightEnd indexSet U j omega -
            ∫ omega',
              positiveIncrementExceedanceCountReal
                cut leftEnd rightEnd indexSet U j omega' ∂mu) ^ 2)
        mu
  count_mean_lower :
    ∀ j,
      countMean j ≤
        ∫ omega,
          positiveIncrementExceedanceCountReal
            cut leftEnd rightEnd indexSet U j omega ∂mu
  count_centered_second_upper :
    ∀ j,
      (∫ omega,
          (positiveIncrementExceedanceCountReal
              cut leftEnd rightEnd indexSet U j omega -
            ∫ omega',
              positiveIncrementExceedanceCountReal
                cut leftEnd rightEnd indexSet U j omega' ∂mu) ^ 2 ∂mu)
        ≤ countSecond j
  fail_summable :
    (∑' j,
      (ENNReal.ofReal (4 * countSecond j / countMean j ^ 2) +
        failLeft j + failRemainder j)) ≠ ⊤
  prob_selected_left_bad :
    ∀ j,
      mu (selectedLeftBad leftEnd bufferLeft selector j) ≤ failLeft j
  prob_selected_remainder_bad :
    ∀ j,
      mu (selectedRemainderBad
        cut leftEnd rightEnd bufferErr selector j) ≤ failRemainder j

/-- Convert the count-moment one-sided increment bridge into the raw bridge
certificate. -/
noncomputable def oneSidedIncrementBridgeCertificate_of_abundance
    (h : OneSidedIncrementBridgeAbundanceCertificate) :
    OneSidedIncrementBridgeCertificate where
  lo := h.lo
  hi := h.hi
  cut := h.cut
  leftEnd := h.leftEnd
  rightEnd := h.rightEnd
  indexSet := h.indexSet
  selector := h.selector
  M := h.M
  U := h.U
  bufferLeft := h.bufferLeft
  bufferErr := h.bufferErr
  r := h.r
  failIncrement := fun j =>
    ENNReal.ofReal (4 * h.countSecond j / h.countMean j ^ 2)
  failLeft := h.failLeft
  failRemainder := h.failRemainder
  r_pos := h.r_pos
  rightEnd_in_block := h.rightEnd_in_block
  margin := h.margin
  selector_mem_of_not_few := h.selector_mem_of_not_few
  lo_tendsto_atTop := h.lo_tendsto_atTop
  M_tendsto_atTop := h.M_tendsto_atTop
  fail_summable := h.fail_summable
  prob_few_increment := by
    intro j
    exact measure_incrementFewPositiveExceedances_le
      ({ cut := h.cut
         leftEnd := h.leftEnd
         rightEnd := h.rightEnd
         indexSet := h.indexSet
         U := h.U
         r := h.r
         countMean := h.countMean
         countSecond := h.countSecond
         r_pos := h.r_pos
         countMean_pos := h.countMean_pos
         r_le_half_countMean := h.r_le_half_countMean
         count_centered_second_integrable :=
           h.count_centered_second_integrable
         count_mean_lower := h.count_mean_lower
         count_centered_second_upper :=
           h.count_centered_second_upper } :
        PositiveIncrementAbundanceCertificate) j
  prob_selected_left_bad := h.prob_selected_left_bad
  prob_selected_remainder_bad := h.prob_selected_remainder_bad

/-- One-sided increment bridge certificates imply the positive-block
certificate. This route is off-path until the analytic certificate is proved. -/
noncomputable def positiveBlockOmega_of_oneSidedIncrementBridgeCertificate
    (h : OneSidedIncrementBridgeCertificate) :
    PositiveBlockOmega where
  X := h.lo
  Y := h.hi
  M := h.M
  fail := fun j => h.failIncrement j + h.failLeft j + h.failRemainder j
  X_tendsto := h.lo_tendsto_atTop
  M_tendsto := h.M_tendsto_atTop
  fail_summable := h.fail_summable
  prob_fail := by
    intro j
    let few :=
      incrementFewPositiveExceedances
        h.cut h.leftEnd h.rightEnd h.indexSet h.U h.r j
    let leftBad :=
      selectedLeftBad h.leftEnd h.bufferLeft h.selector j
    let remBad :=
      selectedRemainderBad
        h.cut h.leftEnd h.rightEnd h.bufferErr h.selector j
    calc
      mu (blockFailure h.lo h.hi h.M j)
          ≤ mu (few ∪ (leftBad ∪ remBad)) := by
            exact
              measure_mono
                (blockFailure_subset_increment_few_union_selected_bad
                  h.lo h.hi h.cut h.leftEnd h.rightEnd h.indexSet
                  h.selector h.M h.U h.bufferLeft h.bufferErr h.r j
                  (h.rightEnd_in_block j)
                  (h.margin j)
                  (h.selector_mem_of_not_few j))
      _ ≤ mu few + mu (leftBad ∪ remBad) :=
            measure_union_le _ _
      _ ≤ mu few + (mu leftBad + mu remBad) :=
            add_le_add (le_refl _) (measure_union_le _ _)
      _ ≤ h.failIncrement j + (h.failLeft j + h.failRemainder j) :=
            add_le_add
              (h.prob_few_increment j)
              (add_le_add
                (h.prob_selected_left_bad j)
                (h.prob_selected_remainder_bad j))
      _ = h.failIncrement j + h.failLeft j + h.failRemainder j := by
            rw [add_assoc]

/-- Direct closure from the one-sided increment bridge certificate. -/
theorem erdos1144_of_oneSidedIncrementBridgeCertificate
    (h : OneSidedIncrementBridgeCertificate) :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    (positiveBlockOmega_of_oneSidedIncrementBridgeCertificate h)

/-- Direct positive-block closure from the one-sided increment bridge with
positive-increment abundance supplied by count moments. -/
noncomputable def positiveBlockOmega_of_oneSidedIncrementBridgeAbundanceCertificate
    (h : OneSidedIncrementBridgeAbundanceCertificate) :
    PositiveBlockOmega :=
  positiveBlockOmega_of_oneSidedIncrementBridgeCertificate
    (oneSidedIncrementBridgeCertificate_of_abundance h)

/-- Direct #1144 closure from the one-sided increment abundance bridge. -/
theorem erdos1144_of_oneSidedIncrementBridgeAbundanceCertificate
    (h : OneSidedIncrementBridgeAbundanceCertificate) :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    (positiveBlockOmega_of_oneSidedIncrementBridgeAbundanceCertificate h)

end Problem1144
end Erdos
