import Erdos.Problem1144.HarperProcess
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.MeasureTheory.Order.Group.Lattice

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-- Large-prime process success on a block: some tested cutoff in the block
beats the final target by the smooth-remainder buffer. -/
def largePrimeBlockSuccess
    (lo hi cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (omega : Omega) (j : ℕ) : Prop :=
  ∃ N ∈ Finset.Icc (lo j) (hi j),
    M j + buffer j ≤ largePrimeProcess omega (cut j) (N + 1)

/-- Large-prime process block failure. -/
def largePrimeBlockFailure
    (lo hi cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (j : ℕ) : Set Omega :=
  {omega | ¬ largePrimeBlockSuccess lo hi cut M buffer omega j}

/-- The smooth process is not negative enough to cancel the large-prime win
anywhere in the block. This strong form is convenient for the first certificate;
later one can replace it by a pointwise-at-the-winner statement if needed. -/
def smoothBlockGood
    (lo hi cut : ℕ → ℕ) (buffer : ℕ → ℝ)
    (omega : Omega) (j : ℕ) : Prop :=
  ∀ N ∈ Finset.Icc (lo j) (hi j),
    -buffer j ≤ smoothProcess omega (cut j) (N + 1)

/-- Smooth process bad event. -/
def smoothBlockBad
    (lo hi cut : ℕ → ℕ) (buffer : ℕ → ℝ)
    (j : ℕ) : Set Omega :=
  {omega | ¬ smoothBlockGood lo hi cut buffer omega j}

/-- Finite block maximum of the normalized large-prime process. -/
noncomputable def largePrimeBlockMax
    (lo hi cut : ℕ → ℕ) (omega : Omega) (j : ℕ) : ℝ :=
  let block := Finset.Icc (lo j) (hi j)
  if h : block.Nonempty then
    block.sup' h fun N => largePrimeProcess omega (cut j) (N + 1)
  else 0

/-- On nonempty blocks, large-prime process failure is exactly the strict lower
tail of the finite large-prime process maximum. -/
theorem largePrimeBlockMax_lt_iff_largePrimeBlockFailure
    (lo hi cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (omega : Omega) (j : ℕ) (hlohi : lo j ≤ hi j) :
    largePrimeBlockMax lo hi cut omega j < M j + buffer j ↔
      omega ∈ largePrimeBlockFailure lo hi cut M buffer j := by
  classical
  unfold largePrimeBlockMax largePrimeBlockFailure largePrimeBlockSuccess
  have hI : (Finset.Icc (lo j) (hi j)).Nonempty :=
    Finset.nonempty_Icc.mpr hlohi
  rw [dif_pos hI, Finset.sup'_lt_iff]
  constructor
  · intro hlt hsucc
    rcases hsucc with ⟨N, hN, hle⟩
    exact not_lt_of_ge hle (hlt N hN)
  · intro hfail N hN
    exact lt_of_not_ge fun hle => hfail ⟨N, hN, hle⟩

/-- The finite large-prime process block maximum is measurable. -/
theorem measurable_largePrimeBlockMax
    (lo hi cut : ℕ → ℕ) (j : ℕ) :
    Measurable fun omega : Omega => largePrimeBlockMax lo hi cut omega j := by
  classical
  unfold largePrimeBlockMax
  let block := Finset.Icc (lo j) (hi j)
  change Measurable fun omega : Omega =>
    if h : block.Nonempty then
      block.sup' h fun N => largePrimeProcess omega (cut j) (N + 1)
    else 0
  by_cases hI : block.Nonempty
  · have hEq :
        (fun omega : Omega =>
          if h : block.Nonempty then
            block.sup' h fun N => largePrimeProcess omega (cut j) (N + 1)
          else 0)
        =
        (fun omega : Omega =>
          block.sup' hI fun N => largePrimeProcess omega (cut j) (N + 1)) := by
      funext omega
      simp [hI]
    rw [hEq]
    have hEqApply :
        (fun omega : Omega =>
          block.sup' hI fun N => largePrimeProcess omega (cut j) (N + 1))
        =
        block.sup' hI
          (fun N (omega : Omega) => largePrimeProcess omega (cut j) (N + 1)) := by
      funext omega
      exact
        (Finset.sup'_apply hI
          (fun N (omega : Omega) => largePrimeProcess omega (cut j) (N + 1))
          omega).symm
    rw [hEqApply]
    exact
      Finset.measurable_sup'
        (s := block)
        (f := fun N (omega : Omega) => largePrimeProcess omega (cut j) (N + 1))
        hI
        (fun N _hN => measurable_largePrimeProcess (cut j) (N + 1))
  · have hEq :
        (fun omega : Omega =>
          if h : block.Nonempty then
            block.sup' h fun N => largePrimeProcess omega (cut j) (N + 1)
          else 0)
        =
        (fun _omega : Omega => 0) := by
      funext omega
      simp [hI]
    rw [hEq]
    exact measurable_const

/-- On nonempty blocks, the large-prime process failure event is measurable. -/
theorem measurableSet_largePrimeBlockFailure
    (lo hi cut : ℕ → ℕ) (M buffer : ℕ → ℝ) (j : ℕ)
    (hlohi : lo j ≤ hi j) :
    MeasurableSet (largePrimeBlockFailure lo hi cut M buffer j) := by
  have hset :
      largePrimeBlockFailure lo hi cut M buffer j =
        {omega : Omega |
          largePrimeBlockMax lo hi cut omega j < M j + buffer j} := by
    ext omega
    exact
      (largePrimeBlockMax_lt_iff_largePrimeBlockFailure
        lo hi cut M buffer omega j hlohi).symm
  rw [hset]
  exact
    measurableSet_lt
      (measurable_largePrimeBlockMax lo hi cut j)
      measurable_const

/-- Smooth badness is a finite union of pointwise lower-tail failures. -/
theorem smoothBlockBad_eq_iUnion
    (lo hi cut : ℕ → ℕ) (buffer : ℕ → ℝ) (j : ℕ) :
    smoothBlockBad lo hi cut buffer j =
      ⋃ N ∈ Finset.Icc (lo j) (hi j),
        {omega : Omega | smoothProcess omega (cut j) (N + 1) < -buffer j} := by
  ext omega
  simp only [smoothBlockBad, smoothBlockGood, Set.mem_setOf_eq, Set.mem_iUnion,
    not_forall, not_le, Finset.mem_Icc]

/-- The smooth-remainder bad event is measurable. -/
theorem measurableSet_smoothBlockBad
    (lo hi cut : ℕ → ℕ) (buffer : ℕ → ℝ) (j : ℕ) :
    MeasurableSet (smoothBlockBad lo hi cut buffer j) := by
  rw [smoothBlockBad_eq_iUnion]
  exact
    Finset.measurableSet_biUnion _ fun N _hN =>
      measurableSet_lt
        (measurable_smoothProcess (cut j) (N + 1))
        measurable_const

/-- Large-prime process success on a selected finite test set. Harper-style
proofs usually work with a mesh of test points rather than all cutoffs in the
block. -/
def largePrimeTestSuccess
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (omega : Omega) (j : ℕ) : Prop :=
  ∃ N ∈ testSet j,
    M j + buffer j ≤ largePrimeProcess omega (cut j) (N + 1)

/-- Large-prime process failure on the selected test set. -/
def largePrimeTestFailure
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (j : ℕ) : Set Omega :=
  {omega | ¬ largePrimeTestSuccess testSet cut M buffer omega j}

/-- Smooth remainder is good on the selected test set. -/
def smoothTestGood
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (buffer : ℕ → ℝ)
    (omega : Omega) (j : ℕ) : Prop :=
  ∀ N ∈ testSet j,
    -buffer j ≤ smoothProcess omega (cut j) (N + 1)

/-- Smooth remainder is bad on the selected test set. -/
def smoothTestBad
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (buffer : ℕ → ℝ)
    (j : ℕ) : Set Omega :=
  {omega | ¬ smoothTestGood testSet cut buffer omega j}

/-- Finite maximum of the normalized large-prime process over a selected test
set. -/
noncomputable def largePrimeTestMax
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (omega : Omega) (j : ℕ) : ℝ :=
  if h : (testSet j).Nonempty then
    (testSet j).sup' h fun N => largePrimeProcess omega (cut j) (N + 1)
  else 0

/-- On nonempty test sets, large-prime test failure is exactly the strict lower
tail of the finite test maximum. -/
theorem largePrimeTestMax_lt_iff_largePrimeTestFailure
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (omega : Omega) (j : ℕ) (htest : (testSet j).Nonempty) :
    largePrimeTestMax testSet cut omega j < M j + buffer j ↔
      omega ∈ largePrimeTestFailure testSet cut M buffer j := by
  classical
  unfold largePrimeTestMax largePrimeTestFailure largePrimeTestSuccess
  rw [dif_pos htest, Finset.sup'_lt_iff]
  constructor
  · intro hlt hsucc
    rcases hsucc with ⟨N, hN, hle⟩
    exact not_lt_of_ge hle (hlt N hN)
  · intro hfail N hN
    exact lt_of_not_ge fun hle => hfail ⟨N, hN, hle⟩

/-- The finite large-prime test maximum is measurable. -/
theorem measurable_largePrimeTestMax
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (j : ℕ) :
    Measurable fun omega : Omega => largePrimeTestMax testSet cut omega j := by
  classical
  unfold largePrimeTestMax
  by_cases hI : (testSet j).Nonempty
  · have hEq :
        (fun omega : Omega =>
          if h : (testSet j).Nonempty then
            (testSet j).sup' h fun N =>
              largePrimeProcess omega (cut j) (N + 1)
          else 0)
        =
        (fun omega : Omega =>
          (testSet j).sup' hI fun N =>
            largePrimeProcess omega (cut j) (N + 1)) := by
      funext omega
      simp [hI]
    rw [hEq]
    have hEqApply :
        (fun omega : Omega =>
          (testSet j).sup' hI fun N =>
            largePrimeProcess omega (cut j) (N + 1))
        =
        (testSet j).sup' hI
          (fun N (omega : Omega) => largePrimeProcess omega (cut j) (N + 1)) := by
      funext omega
      exact
        (Finset.sup'_apply hI
          (fun N (omega : Omega) => largePrimeProcess omega (cut j) (N + 1))
          omega).symm
    rw [hEqApply]
    exact
      Finset.measurable_sup'
        (s := testSet j)
        (f := fun N (omega : Omega) => largePrimeProcess omega (cut j) (N + 1))
        hI
        (fun N _hN => measurable_largePrimeProcess (cut j) (N + 1))
  · have hEq :
        (fun omega : Omega =>
          if h : (testSet j).Nonempty then
            (testSet j).sup' h fun N =>
              largePrimeProcess omega (cut j) (N + 1)
          else 0)
        =
        (fun _omega : Omega => 0) := by
      funext omega
      simp [hI]
    rw [hEq]
    exact measurable_const

/-- On nonempty test sets, the large-prime test failure event is measurable. -/
theorem measurableSet_largePrimeTestFailure
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (j : ℕ) (htest : (testSet j).Nonempty) :
    MeasurableSet (largePrimeTestFailure testSet cut M buffer j) := by
  have hset :
      largePrimeTestFailure testSet cut M buffer j =
        {omega : Omega |
          largePrimeTestMax testSet cut omega j < M j + buffer j} := by
    ext omega
    exact
      (largePrimeTestMax_lt_iff_largePrimeTestFailure
        testSet cut M buffer omega j htest).symm
  rw [hset]
  exact
    measurableSet_lt
      (measurable_largePrimeTestMax testSet cut j)
      measurable_const

/-- Test-set smooth badness is a finite union of pointwise lower-tail
failures. -/
theorem smoothTestBad_eq_iUnion
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (buffer : ℕ → ℝ) (j : ℕ) :
    smoothTestBad testSet cut buffer j =
      ⋃ N ∈ testSet j,
        {omega : Omega | smoothProcess omega (cut j) (N + 1) < -buffer j} := by
  ext omega
  simp only [smoothTestBad, smoothTestGood, Set.mem_setOf_eq, Set.mem_iUnion,
    not_forall, not_le]

/-- The test-set smooth-remainder bad event is measurable. -/
theorem measurableSet_smoothTestBad
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (buffer : ℕ → ℝ) (j : ℕ) :
    MeasurableSet (smoothTestBad testSet cut buffer j) := by
  rw [smoothTestBad_eq_iUnion]
  exact
    Finset.measurableSet_biUnion _ fun N _hN =>
      measurableSet_lt
        (measurable_smoothProcess (cut j) (N + 1))
        measurable_const

/-- The selected large-prime coefficients have enough conditional variance at
every test point. -/
def largePrimeVarianceFloorGood
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (varianceFloor : ℕ → ℝ) (j : ℕ) : Set Omega :=
  {omega | ∀ N ∈ testSet j,
    varianceFloor j ≤ largePrimeVariance omega (cut j) (N + 1)}

/-- The selected large-prime coefficients have small conditional covariance
between distinct test points. -/
def largePrimeCovarianceCeilGood
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (covarianceCeil : ℕ → ℝ) (j : ℕ) : Set Omega :=
  {omega | ∀ M ∈ testSet j, ∀ N ∈ testSet j, M ≠ N →
    |largePrimeCovariance omega (cut j) (M + 1) (N + 1)| ≤
      covarianceCeil j}

/-- The coefficient-geometry event needed by the Harper large-prime maximum
argument: all selected variances are large and all selected off-diagonal
covariances are small. -/
def largePrimeGeometryGood
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (varianceFloor covarianceCeil : ℕ → ℝ) (j : ℕ) : Set Omega :=
  largePrimeVarianceFloorGood testSet cut varianceFloor j ∩
    largePrimeCovarianceCeilGood testSet cut covarianceCeil j

/-- The variance-floor geometry event is measurable. -/
theorem measurableSet_largePrimeVarianceFloorGood
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (varianceFloor : ℕ → ℝ) (j : ℕ) :
    MeasurableSet
      (largePrimeVarianceFloorGood testSet cut varianceFloor j) := by
  classical
  unfold largePrimeVarianceFloorGood
  rw [show
      {omega : Omega | ∀ N ∈ testSet j,
        varianceFloor j ≤ largePrimeVariance omega (cut j) (N + 1)}
        =
      ⋂ N ∈ testSet j,
        {omega : Omega |
          varianceFloor j ≤ largePrimeVariance omega (cut j) (N + 1)} by
        ext omega
        simp]
  exact
    Finset.measurableSet_biInter (testSet j) fun N _hN =>
      measurableSet_le measurable_const
        (measurable_largePrimeVariance (cut j) (N + 1))

/-- The covariance-ceiling geometry event is measurable. -/
theorem measurableSet_largePrimeCovarianceCeilGood
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (covarianceCeil : ℕ → ℝ) (j : ℕ) :
    MeasurableSet
      (largePrimeCovarianceCeilGood testSet cut covarianceCeil j) := by
  classical
  unfold largePrimeCovarianceCeilGood
  rw [show
      {omega : Omega | ∀ M ∈ testSet j, ∀ N ∈ testSet j, M ≠ N →
        |largePrimeCovariance omega (cut j) (M + 1) (N + 1)| ≤
          covarianceCeil j}
        =
      ⋂ M ∈ testSet j,
        ⋂ N ∈ testSet j,
          {omega : Omega |
            M ≠ N →
              |largePrimeCovariance omega (cut j) (M + 1) (N + 1)| ≤
                covarianceCeil j} by
        ext omega
        simp]
  refine Finset.measurableSet_biInter (testSet j) fun M _hM => ?_
  refine Finset.measurableSet_biInter (testSet j) fun N _hN => ?_
  by_cases hMN : M = N
  · have hset :
        {omega : Omega |
          M ≠ N →
            |largePrimeCovariance omega (cut j) (M + 1) (N + 1)| ≤
              covarianceCeil j}
          =
        Set.univ := by
          ext omega
          simp [hMN]
    rw [hset]
    exact MeasurableSet.univ
  · have hset :
        {omega : Omega |
          M ≠ N →
            |largePrimeCovariance omega (cut j) (M + 1) (N + 1)| ≤
              covarianceCeil j}
          =
        {omega : Omega |
          |largePrimeCovariance omega (cut j) (M + 1) (N + 1)| ≤
            covarianceCeil j} := by
          ext omega
          simp [hMN]
    rw [hset]
    have hcov_abs :
        Measurable fun omega : Omega =>
          |largePrimeCovariance omega (cut j) (M + 1) (N + 1)| := by
      exact
        _root_.continuous_abs.measurable.comp
          (measurable_largePrimeCovariance (cut j) (M + 1) (N + 1))
    exact
      measurableSet_le
        hcov_abs
        measurable_const

/-- The combined coefficient-geometry event is measurable. -/
theorem measurableSet_largePrimeGeometryGood
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (varianceFloor covarianceCeil : ℕ → ℝ) (j : ℕ) :
    MeasurableSet
      (largePrimeGeometryGood testSet cut varianceFloor covarianceCeil j) := by
  unfold largePrimeGeometryGood
  exact
    (measurableSet_largePrimeVarianceFloorGood
      testSet cut varianceFloor j).inter
      (measurableSet_largePrimeCovarianceCeilGood
        testSet cut covarianceCeil j)

/-- Bad coefficient geometry is controlled by the finite union of pointwise
variance-floor failures and off-diagonal covariance-ceiling failures. -/
theorem measure_largePrimeGeometryBad_le_pointwise
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (varianceFloor covarianceCeil : ℕ → ℝ) (j : ℕ) :
    mu
        ((largePrimeGeometryGood
          testSet cut varianceFloor covarianceCeil j)ᶜ)
      ≤
        (∑ N ∈ testSet j,
          mu {omega : Omega |
            largePrimeVariance omega (cut j) (N + 1) < varianceFloor j})
        +
        (∑ M ∈ testSet j,
          ∑ N ∈ testSet j,
            mu {omega : Omega |
              M ≠ N ∧
                covarianceCeil j <
                  |largePrimeCovariance omega (cut j) (M + 1) (N + 1)|}) := by
  classical
  let V := largePrimeVarianceFloorGood testSet cut varianceFloor j
  let C := largePrimeCovarianceCeilGood testSet cut covarianceCeil j
  let Vbad : Set Omega :=
    ⋃ N ∈ testSet j,
      {omega : Omega |
        largePrimeVariance omega (cut j) (N + 1) < varianceFloor j}
  let Cbad : Set Omega :=
    ⋃ M ∈ testSet j,
      ⋃ N ∈ testSet j,
        {omega : Omega |
          M ≠ N ∧
            covarianceCeil j <
              |largePrimeCovariance omega (cut j) (M + 1) (N + 1)|}
  have hVsubset : Vᶜ ⊆ Vbad := by
    intro omega homega
    simp only [V, largePrimeVarianceFloorGood, Set.mem_compl_iff,
      Set.mem_setOf_eq, not_forall, not_le] at homega
    rcases homega with ⟨N, hN, hlt⟩
    simp only [Vbad, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨N, hN, hlt⟩
  have hCsubset : Cᶜ ⊆ Cbad := by
    intro omega homega
    simp only [C, largePrimeCovarianceCeilGood, Set.mem_compl_iff,
      Set.mem_setOf_eq, not_forall, not_le] at homega
    rcases homega with ⟨M, hM, N, hN, hMN, hlt⟩
    simp only [Cbad, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨M, hM, N, hN, hMN, hlt⟩
  have hGsubset :
      ((largePrimeGeometryGood
          testSet cut varianceFloor covarianceCeil j)ᶜ)
        ⊆ Vbad ∪ Cbad := by
    intro omega homega
    by_cases hVmem : omega ∈ V
    · have hCnot : omega ∈ Cᶜ := by
        intro hCmem
        exact homega ⟨hVmem, hCmem⟩
      exact Or.inr (hCsubset hCnot)
    · exact Or.inl (hVsubset hVmem)
  calc
    mu
        ((largePrimeGeometryGood
          testSet cut varianceFloor covarianceCeil j)ᶜ)
        ≤ mu (Vbad ∪ Cbad) := measure_mono hGsubset
    _ ≤ mu Vbad + mu Cbad := measure_union_le _ _
    _ ≤
        (∑ N ∈ testSet j,
          mu {omega : Omega |
            largePrimeVariance omega (cut j) (N + 1) < varianceFloor j})
        +
        (∑ M ∈ testSet j,
          ∑ N ∈ testSet j,
            mu {omega : Omega |
              M ≠ N ∧
                covarianceCeil j <
                  |largePrimeCovariance omega (cut j) (M + 1) (N + 1)|}) := by
          refine add_le_add ?_ ?_
          · unfold Vbad
            exact
              measure_biUnion_finset_le (testSet j)
                fun N =>
                  {omega : Omega |
                    largePrimeVariance omega (cut j) (N + 1) <
                      varianceFloor j}
          · calc
              mu Cbad
                  ≤
                    ∑ M ∈ testSet j,
                      mu
                        (⋃ N ∈ testSet j,
                          {omega : Omega |
                            M ≠ N ∧
                              covarianceCeil j <
                                |largePrimeCovariance omega (cut j)
                                  (M + 1) (N + 1)|}) := by
                    unfold Cbad
                    exact
                      measure_biUnion_finset_le (testSet j)
                        fun M =>
                          ⋃ N ∈ testSet j,
                            {omega : Omega |
                              M ≠ N ∧
                                covarianceCeil j <
                                  |largePrimeCovariance omega (cut j)
                                    (M + 1) (N + 1)|}
              _ ≤
                    ∑ M ∈ testSet j,
                      ∑ N ∈ testSet j,
                        mu {omega : Omega |
                          M ≠ N ∧
                            covarianceCeil j <
                              |largePrimeCovariance omega (cut j)
                                (M + 1) (N + 1)|} := by
                    refine Finset.sum_le_sum fun M hM => ?_
                    exact
                      measure_biUnion_finset_le (testSet j)
                        fun N =>
                          {omega : Omega |
                            M ≠ N ∧
                              covarianceCeil j <
                                |largePrimeCovariance omega (cut j)
                                  (M + 1) (N + 1)|}

/-- A large-prime failure is covered by bad coefficient geometry or failure
inside the good-geometry event. -/
theorem measure_largePrimeTestFailure_le_geometry_split
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (varianceFloor covarianceCeil : ℕ → ℝ) (j : ℕ)
    (failGeometry failProcess : ℝ≥0∞)
    (hgeom :
      mu
        ((largePrimeGeometryGood
          testSet cut varianceFloor covarianceCeil j)ᶜ) ≤ failGeometry)
    (hprocess :
      mu
        (largePrimeTestFailure testSet cut M buffer j ∩
          largePrimeGeometryGood testSet cut varianceFloor covarianceCeil j)
          ≤ failProcess) :
    mu (largePrimeTestFailure testSet cut M buffer j) ≤
      failGeometry + failProcess := by
  let G := largePrimeGeometryGood testSet cut varianceFloor covarianceCeil j
  let F := largePrimeTestFailure testSet cut M buffer j
  have hsubset : F ⊆ Gᶜ ∪ (F ∩ G) := by
    intro omega hF
    by_cases hG : omega ∈ G
    · right
      exact ⟨hF, hG⟩
    · left
      exact hG
  calc
    mu F ≤ mu (Gᶜ ∪ (F ∩ G)) := measure_mono hsubset
    _ ≤ mu Gᶜ + mu (F ∩ G) := measure_union_le _ _
    _ ≤ failGeometry + failProcess := add_le_add hgeom hprocess

/-- The finite second-moment budget controlling smooth badness on a selected
test mesh. -/
noncomputable def smoothSecondMomentMeshBudget
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (buffer : ℕ → ℝ) (j : ℕ) : ℝ≥0∞ :=
  ∑ N ∈ testSet j,
    ENNReal.ofReal
      ((smoothPairCount (cut j) (N + 1) /
          (Real.sqrt (((N + 1 : ℕ) : ℝ))) ^ 2) /
        (buffer j) ^ 2)

/-- A finite kernel-form upper budget for the smooth mesh. If one has the
pointwise estimate `smoothPairCount (cut j) (N+1) <= (N+1) * D j` on the
test mesh, this is the resulting second-moment budget. -/
noncomputable def smoothKernelMeshBudget
    (testSet : ℕ → Finset ℕ) (buffer : ℕ → ℝ)
    (D : ℕ → ℝ) (j : ℕ) : ℝ≥0∞ :=
  ∑ _N ∈ testSet j,
    ENNReal.ofReal (D j / (buffer j) ^ 2)

/-- The canonical finite-kernel mesh budget obtained from the proved smooth
square-pair estimate with the cutoff `N+1` at each test point. -/
noncomputable def smoothFiniteKernelMeshBudget
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (buffer : ℕ → ℝ) (j : ℕ) : ℝ≥0∞ :=
  ∑ N ∈ testSet j,
    ENNReal.ofReal
      (smoothSquareKernelWeight (cut j) (N + 1) / (buffer j) ^ 2)

/-- A pointwise smooth-pair count bound of the form
`smoothPairCount X n <= n * D` implies the corresponding finite kernel mesh
budget. This is the Lean-facing form of the elementary estimate
`# {a,b <= n: a,b X-smooth, ab square} <= n D_X`. -/
theorem smoothSecondMomentMeshBudget_le_kernelMeshBudget
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (buffer D : ℕ → ℝ) (j : ℕ)
    (hcount :
      ∀ N, N ∈ testSet j →
        smoothPairCount (cut j) (N + 1) ≤
          (((N + 1 : ℕ) : ℝ) * D j)) :
    smoothSecondMomentMeshBudget testSet cut buffer j ≤
      smoothKernelMeshBudget testSet buffer D j := by
  classical
  unfold smoothSecondMomentMeshBudget smoothKernelMeshBudget
  refine Finset.sum_le_sum fun N hN => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hNpos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hsqrt_sq :
      (Real.sqrt (((N + 1 : ℕ) : ℝ))) ^ 2 =
        (((N + 1 : ℕ) : ℝ)) := by
    rw [Real.sq_sqrt]
    positivity
  have hdiv :
      smoothPairCount (cut j) (N + 1) /
          (Real.sqrt (((N + 1 : ℕ) : ℝ))) ^ 2
        ≤ D j := by
    rw [hsqrt_sq]
    rw [div_le_iff₀ hNpos]
    simpa [mul_comm] using hcount N hN
  exact div_le_div_of_nonneg_right hdiv (sq_nonneg (buffer j))

/-- A convenience wrapper: it is enough to bound the kernel mesh budget. -/
theorem smoothSecondMomentMeshBudget_le_of_kernelMeshBudget
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (buffer D : ℕ → ℝ) (failSmooth : ℕ → ℝ≥0∞) (j : ℕ)
    (_hbuffer : 0 < buffer j)
    (hcount :
      ∀ N, N ∈ testSet j →
        smoothPairCount (cut j) (N + 1) ≤
          (((N + 1 : ℕ) : ℝ) * D j))
    (hbudget :
      smoothKernelMeshBudget testSet buffer D j ≤ failSmooth j) :
    smoothSecondMomentMeshBudget testSet cut buffer j ≤ failSmooth j :=
  (smoothSecondMomentMeshBudget_le_kernelMeshBudget
    testSet cut buffer D j hcount).trans hbudget

/-- The proved finite smooth square-pair estimate controls the smooth mesh
budget by the finite reciprocal-kernel budget. -/
theorem smoothSecondMomentMeshBudget_le_finiteKernelMeshBudget
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (buffer : ℕ → ℝ) (j : ℕ) :
    smoothSecondMomentMeshBudget testSet cut buffer j ≤
      smoothFiniteKernelMeshBudget testSet cut buffer j := by
  classical
  unfold smoothSecondMomentMeshBudget smoothFiniteKernelMeshBudget
  refine Finset.sum_le_sum fun N hN => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hNpos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hsqrt_sq :
      (Real.sqrt (((N + 1 : ℕ) : ℝ))) ^ 2 =
        (((N + 1 : ℕ) : ℝ)) := by
    rw [Real.sq_sqrt]
    positivity
  have hdiv :
      smoothPairCount (cut j) (N + 1) /
          (Real.sqrt (((N + 1 : ℕ) : ℝ))) ^ 2
        ≤ smoothSquareKernelWeight (cut j) (N + 1) := by
    rw [hsqrt_sq]
    rw [div_le_iff₀ hNpos]
    simpa [mul_comm] using
      smoothPairCount_le_mul_smoothSquareKernelWeight (cut j) (N + 1)
  exact div_le_div_of_nonneg_right hdiv (sq_nonneg (buffer j))

/-- Test-set smooth badness is controlled by the sum of the pointwise second
moments on the selected mesh. -/
theorem measure_smoothTestBad_le_sum_second
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (buffer : ℕ → ℝ) (j : ℕ)
    (hbuffer : 0 < buffer j) :
    mu (smoothTestBad testSet cut buffer j) ≤
      smoothSecondMomentMeshBudget testSet cut buffer j := by
  unfold smoothSecondMomentMeshBudget
  rw [smoothTestBad_eq_iUnion]
  calc
    mu
        (⋃ N ∈ testSet j,
          {omega : Omega |
            smoothProcess omega (cut j) (N + 1) < -buffer j})
        ≤
        ∑ N ∈ testSet j,
          mu
            {omega : Omega |
              smoothProcess omega (cut j) (N + 1) < -buffer j} := by
          exact
            measure_biUnion_finset_le (testSet j)
              (fun N : ℕ =>
                {omega : Omega |
                  smoothProcess omega (cut j) (N + 1) < -buffer j})
    _ ≤
        ∑ N ∈ testSet j,
          ENNReal.ofReal
            ((smoothPairCount (cut j) (N + 1) /
                (Real.sqrt (((N + 1 : ℕ) : ℝ))) ^ 2) /
              (buffer j) ^ 2) := by
          refine Finset.sum_le_sum fun N _hN => ?_
          exact
            measure_smoothProcess_lt_neg_le_second
              (X := cut j) (N := N + 1) (B := buffer j) hbuffer

/-- If the large-prime process succeeds and the smooth remainder is good, then
the original block succeeds. -/
theorem blockSuccess_of_largePrimeBlockSuccess_of_smoothBlockGood
    (lo hi cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (omega : Omega) (j : ℕ)
    (block_in_range :
      ∀ N, N ∈ Finset.Icc (lo j) (hi j) → N + 1 < (cut j) ^ 2)
    (hLarge : largePrimeBlockSuccess lo hi cut M buffer omega j)
    (hSmooth : smoothBlockGood lo hi cut buffer omega j) :
    blockSuccess lo hi M omega j := by
  rcases hLarge with ⟨N, hN, hLargeN⟩
  exact
    blockSuccess_of_largePrimeProcess_ge_of_smoothProcess_ge
      lo hi cut M buffer omega j N hN (block_in_range N hN)
      hLargeN (hSmooth N hN)

/-- Block failure is contained in the union of large-prime-process failure and
smooth-remainder badness. -/
theorem blockFailure_subset_largePrimeFailure_union_smoothBad
    (lo hi cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (j : ℕ)
    (block_in_range :
      ∀ N, N ∈ Finset.Icc (lo j) (hi j) → N + 1 < (cut j) ^ 2) :
    blockFailure lo hi M j ⊆
      largePrimeBlockFailure lo hi cut M buffer j ∪
        smoothBlockBad lo hi cut buffer j := by
  intro omega hfail
  by_cases hLarge : largePrimeBlockSuccess lo hi cut M buffer omega j
  · right
    intro hSmooth
    exact
      hfail
        (blockSuccess_of_largePrimeBlockSuccess_of_smoothBlockGood
          lo hi cut M buffer omega j block_in_range hLarge hSmooth)
  · left
    exact hLarge

/-- If a selected test point has a large-prime win and the smooth remainder is
good on all selected test points, then the original block succeeds. -/
theorem blockSuccess_of_largePrimeTestSuccess_of_smoothTestGood
    (lo hi cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (testSet : ℕ → Finset ℕ)
    (omega : Omega) (j : ℕ)
    (testSet_in_block :
      ∀ N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j))
    (testSet_in_range :
      ∀ N, N ∈ testSet j → N + 1 < (cut j) ^ 2)
    (hLarge : largePrimeTestSuccess testSet cut M buffer omega j)
    (hSmooth : smoothTestGood testSet cut buffer omega j) :
    blockSuccess lo hi M omega j := by
  rcases hLarge with ⟨N, hN, hLargeN⟩
  exact
    blockSuccess_of_largePrimeProcess_ge_of_smoothProcess_ge
      lo hi cut M buffer omega j N
      (testSet_in_block N hN)
      (testSet_in_range N hN)
      hLargeN
      (hSmooth N hN)

/-- Original block failure is contained in test-set large-prime failure or
test-set smooth badness. -/
theorem blockFailure_subset_largePrimeTestFailure_union_smoothTestBad
    (lo hi cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (testSet : ℕ → Finset ℕ) (j : ℕ)
    (testSet_in_block :
      ∀ N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j))
    (testSet_in_range :
      ∀ N, N ∈ testSet j → N + 1 < (cut j) ^ 2) :
    blockFailure lo hi M j ⊆
      largePrimeTestFailure testSet cut M buffer j ∪
        smoothTestBad testSet cut buffer j := by
  intro omega hfail
  by_cases hLarge : largePrimeTestSuccess testSet cut M buffer omega j
  · right
    intro hSmooth
    exact
      hfail
        (blockSuccess_of_largePrimeTestSuccess_of_smoothTestGood
          lo hi cut M buffer testSet omega j
          testSet_in_block testSet_in_range hLarge hSmooth)
  · left
    exact hLarge

/-- Harper-process block certificate.

This separates the analytic work into two estimates: a high-probability
one-sided maximum for the large-prime process and a high-probability lower
bound for the smooth remainder. Lean then combines them into the active
`PositiveBlockOmega` interface. -/
structure HarperProcessBlockCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  cut : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  failLarge : ℕ → ℝ≥0∞
  failSmooth : ℕ → ℝ≥0∞
  block_in_range :
    ∀ j N, N ∈ Finset.Icc (lo j) (hi j) → N + 1 < (cut j) ^ 2
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  fail_summable :
    (∑' j, (failLarge j + failSmooth j)) ≠ ⊤
  prob_large_fail :
    ∀ j,
      mu (largePrimeBlockFailure lo hi cut M buffer j) ≤ failLarge j
  prob_smooth_bad :
    ∀ j,
      mu (smoothBlockBad lo hi cut buffer j) ≤ failSmooth j

/-- A Harper-process block certificate gives the active positive block
certificate. -/
noncomputable def positiveBlockOmega_of_harperProcessBlockCertificate
    (h : HarperProcessBlockCertificate) :
    PositiveBlockOmega where
  X := h.lo
  Y := h.hi
  M := h.M
  fail := fun j => h.failLarge j + h.failSmooth j
  X_tendsto := h.lo_tendsto_atTop
  M_tendsto := h.M_tendsto_atTop
  fail_summable := h.fail_summable
  prob_fail := by
    intro j
    calc
      mu (blockFailure h.lo h.hi h.M j)
          ≤ mu
              (largePrimeBlockFailure h.lo h.hi h.cut h.M h.buffer j ∪
                smoothBlockBad h.lo h.hi h.cut h.buffer j) := by
            exact
              measure_mono
                (blockFailure_subset_largePrimeFailure_union_smoothBad
                  h.lo h.hi h.cut h.M h.buffer j (h.block_in_range j))
      _ ≤
          mu (largePrimeBlockFailure h.lo h.hi h.cut h.M h.buffer j) +
            mu (smoothBlockBad h.lo h.hi h.cut h.buffer j) :=
            measure_union_le _ _
      _ ≤ h.failLarge j + h.failSmooth j :=
            add_le_add (h.prob_large_fail j) (h.prob_smooth_bad j)

/-- Direct closure from the Harper-process split certificate. -/
theorem erdos1144_of_harperProcessBlockCertificate
    (h : HarperProcessBlockCertificate) :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    (positiveBlockOmega_of_harperProcessBlockCertificate h)

/-- Harper-process certificate on selected test points.

This is the form closest to Harper's proof: choose a finite mesh `testSet j`
inside the block, prove a positive maximum for the large-prime process on that
mesh, and control the smooth remainder on that same mesh. -/
structure HarperTestPointBlockCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  cut : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  testSet : ℕ → Finset ℕ
  failLarge : ℕ → ℝ≥0∞
  failSmooth : ℕ → ℝ≥0∞
  testSet_nonempty : ∀ j, (testSet j).Nonempty
  testSet_in_block :
    ∀ j N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j)
  testSet_in_range :
    ∀ j N, N ∈ testSet j → N + 1 < (cut j) ^ 2
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  fail_summable :
    (∑' j, (failLarge j + failSmooth j)) ≠ ⊤
  prob_large_fail :
    ∀ j,
      mu (largePrimeTestFailure testSet cut M buffer j) ≤ failLarge j
  prob_smooth_bad :
    ∀ j,
      mu (smoothTestBad testSet cut buffer j) ≤ failSmooth j

/-- Refined test-point Harper certificate where the smooth-remainder failure
budget is supplied by a finite second-moment count. The only remaining direct
probability estimate is the large-prime positive maximum failure. -/
structure HarperTestPointSecondMomentCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  cut : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  testSet : ℕ → Finset ℕ
  failLarge : ℕ → ℝ≥0∞
  failSmooth : ℕ → ℝ≥0∞
  testSet_nonempty : ∀ j, (testSet j).Nonempty
  testSet_in_block :
    ∀ j N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j)
  testSet_in_range :
    ∀ j N, N ∈ testSet j → N + 1 < (cut j) ^ 2
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  buffer_pos : ∀ j, 0 < buffer j
  fail_summable :
    (∑' j, (failLarge j + failSmooth j)) ≠ ⊤
  prob_large_fail :
    ∀ j,
      mu (largePrimeTestFailure testSet cut M buffer j) ≤ failLarge j
  smooth_second_bound :
    ∀ j,
      smoothSecondMomentMeshBudget testSet cut buffer j ≤ failSmooth j

/-- Geometry-refined test-point Harper certificate.

This separates the large-prime estimate into two paper tasks:

1. the coefficient geometry is good with high probability, meaning selected
   variances are large and selected covariances are small;
2. on the good-geometry event, the one-sided large-prime maximum failure has
   small probability.

The smooth side is still supplied by the finite second-moment mesh budget. -/
structure HarperGeometrySecondMomentCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  cut : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  testSet : ℕ → Finset ℕ
  varianceFloor : ℕ → ℝ
  covarianceCeil : ℕ → ℝ
  failGeometry : ℕ → ℝ≥0∞
  failProcess : ℕ → ℝ≥0∞
  failSmooth : ℕ → ℝ≥0∞
  testSet_nonempty : ∀ j, (testSet j).Nonempty
  testSet_in_block :
    ∀ j N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j)
  testSet_in_range :
    ∀ j N, N ∈ testSet j → N + 1 < (cut j) ^ 2
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  buffer_pos : ∀ j, 0 < buffer j
  fail_summable :
    (∑' j, ((failGeometry j + failProcess j) + failSmooth j)) ≠ ⊤
  prob_geometry_bad :
    ∀ j,
      mu
        ((largePrimeGeometryGood
          testSet cut varianceFloor covarianceCeil j)ᶜ) ≤ failGeometry j
  prob_large_fail_on_geometry :
    ∀ j,
      mu
        (largePrimeTestFailure testSet cut M buffer j ∩
          largePrimeGeometryGood testSet cut varianceFloor covarianceCeil j)
          ≤ failProcess j
  smooth_second_bound :
    ∀ j,
      smoothSecondMomentMeshBudget testSet cut buffer j ≤ failSmooth j

/-- Geometry-refined certificate with the smooth side reduced to the proved
finite reciprocal-kernel budget. This is the sharper closure interface after
formalising the elementary smooth square-pair count. -/
structure HarperGeometryFiniteKernelCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  cut : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  testSet : ℕ → Finset ℕ
  varianceFloor : ℕ → ℝ
  covarianceCeil : ℕ → ℝ
  failGeometry : ℕ → ℝ≥0∞
  failProcess : ℕ → ℝ≥0∞
  failSmooth : ℕ → ℝ≥0∞
  testSet_nonempty : ∀ j, (testSet j).Nonempty
  testSet_in_block :
    ∀ j N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j)
  testSet_in_range :
    ∀ j N, N ∈ testSet j → N + 1 < (cut j) ^ 2
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  buffer_pos : ∀ j, 0 < buffer j
  fail_summable :
    (∑' j, ((failGeometry j + failProcess j) + failSmooth j)) ≠ ⊤
  prob_geometry_bad :
    ∀ j,
      mu
        ((largePrimeGeometryGood
          testSet cut varianceFloor covarianceCeil j)ᶜ) ≤ failGeometry j
  prob_large_fail_on_geometry :
    ∀ j,
      mu
        (largePrimeTestFailure testSet cut M buffer j ∩
          largePrimeGeometryGood testSet cut varianceFloor covarianceCeil j)
          ≤ failProcess j
  smooth_finiteKernel_bound :
    ∀ j,
      smoothFiniteKernelMeshBudget testSet cut buffer j ≤ failSmooth j

/-- The finite-kernel geometry certificate supplies the previous
second-moment geometry certificate. -/
noncomputable def harperGeometrySecondMomentCertificate_of_finiteKernel
    (h : HarperGeometryFiniteKernelCertificate) :
    HarperGeometrySecondMomentCertificate where
  lo := h.lo
  hi := h.hi
  cut := h.cut
  M := h.M
  buffer := h.buffer
  testSet := h.testSet
  varianceFloor := h.varianceFloor
  covarianceCeil := h.covarianceCeil
  failGeometry := h.failGeometry
  failProcess := h.failProcess
  failSmooth := h.failSmooth
  testSet_nonempty := h.testSet_nonempty
  testSet_in_block := h.testSet_in_block
  testSet_in_range := h.testSet_in_range
  lo_tendsto_atTop := h.lo_tendsto_atTop
  M_tendsto_atTop := h.M_tendsto_atTop
  buffer_pos := h.buffer_pos
  fail_summable := h.fail_summable
  prob_geometry_bad := h.prob_geometry_bad
  prob_large_fail_on_geometry := h.prob_large_fail_on_geometry
  smooth_second_bound := by
    intro j
    exact
      (smoothSecondMomentMeshBudget_le_finiteKernelMeshBudget
        h.testSet h.cut h.buffer j).trans
        (h.smooth_finiteKernel_bound j)

/-- The geometry-refined certificate supplies the refined test-point Harper
certificate. -/
noncomputable def harperTestPointSecondMomentCertificate_of_geometry
    (h : HarperGeometrySecondMomentCertificate) :
    HarperTestPointSecondMomentCertificate where
  lo := h.lo
  hi := h.hi
  cut := h.cut
  M := h.M
  buffer := h.buffer
  testSet := h.testSet
  failLarge := fun j => h.failGeometry j + h.failProcess j
  failSmooth := h.failSmooth
  testSet_nonempty := h.testSet_nonempty
  testSet_in_block := h.testSet_in_block
  testSet_in_range := h.testSet_in_range
  lo_tendsto_atTop := h.lo_tendsto_atTop
  M_tendsto_atTop := h.M_tendsto_atTop
  buffer_pos := h.buffer_pos
  fail_summable := h.fail_summable
  prob_large_fail := by
    intro j
    exact
      measure_largePrimeTestFailure_le_geometry_split
        h.testSet h.cut h.M h.buffer h.varianceFloor h.covarianceCeil j
        (h.failGeometry j) (h.failProcess j)
        (h.prob_geometry_bad j)
        (h.prob_large_fail_on_geometry j)
  smooth_second_bound := h.smooth_second_bound

/-- The finite smooth second-moment certificate supplies the raw test-point
Harper block certificate. -/
noncomputable def harperTestPointBlockCertificate_of_secondMoment
    (h : HarperTestPointSecondMomentCertificate) :
    HarperTestPointBlockCertificate where
  lo := h.lo
  hi := h.hi
  cut := h.cut
  M := h.M
  buffer := h.buffer
  testSet := h.testSet
  failLarge := h.failLarge
  failSmooth := h.failSmooth
  testSet_nonempty := h.testSet_nonempty
  testSet_in_block := h.testSet_in_block
  testSet_in_range := h.testSet_in_range
  lo_tendsto_atTop := h.lo_tendsto_atTop
  M_tendsto_atTop := h.M_tendsto_atTop
  fail_summable := h.fail_summable
  prob_large_fail := h.prob_large_fail
  prob_smooth_bad := by
    intro j
    exact
      (measure_smoothTestBad_le_sum_second
        h.testSet h.cut h.buffer j (h.buffer_pos j)).trans
        (h.smooth_second_bound j)

/-- A test-point Harper certificate gives the active positive block
certificate. -/
noncomputable def positiveBlockOmega_of_harperTestPointBlockCertificate
    (h : HarperTestPointBlockCertificate) :
    PositiveBlockOmega where
  X := h.lo
  Y := h.hi
  M := h.M
  fail := fun j => h.failLarge j + h.failSmooth j
  X_tendsto := h.lo_tendsto_atTop
  M_tendsto := h.M_tendsto_atTop
  fail_summable := h.fail_summable
  prob_fail := by
    intro j
    calc
      mu (blockFailure h.lo h.hi h.M j)
          ≤ mu
              (largePrimeTestFailure h.testSet h.cut h.M h.buffer j ∪
                smoothTestBad h.testSet h.cut h.buffer j) := by
            exact
              measure_mono
                (blockFailure_subset_largePrimeTestFailure_union_smoothTestBad
                  h.lo h.hi h.cut h.M h.buffer h.testSet j
                  (h.testSet_in_block j)
                  (h.testSet_in_range j))
      _ ≤
          mu (largePrimeTestFailure h.testSet h.cut h.M h.buffer j) +
            mu (smoothTestBad h.testSet h.cut h.buffer j) :=
            measure_union_le _ _
      _ ≤ h.failLarge j + h.failSmooth j :=
            add_le_add (h.prob_large_fail j) (h.prob_smooth_bad j)

/-- Direct closure from the test-point Harper-process certificate. -/
theorem erdos1144_of_harperTestPointBlockCertificate
    (h : HarperTestPointBlockCertificate) :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    (positiveBlockOmega_of_harperTestPointBlockCertificate h)

/-- A refined test-point Harper certificate gives the active positive block
certificate. -/
noncomputable def positiveBlockOmega_of_harperTestPointSecondMomentCertificate
    (h : HarperTestPointSecondMomentCertificate) :
    PositiveBlockOmega :=
  positiveBlockOmega_of_harperTestPointBlockCertificate
    (harperTestPointBlockCertificate_of_secondMoment h)

/-- Direct closure from the refined test-point Harper certificate. -/
theorem erdos1144_of_harperTestPointSecondMomentCertificate
    (h : HarperTestPointSecondMomentCertificate) :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    (positiveBlockOmega_of_harperTestPointSecondMomentCertificate h)

/-- A geometry-refined test-point Harper certificate gives the active positive
block certificate. -/
noncomputable def positiveBlockOmega_of_harperGeometrySecondMomentCertificate
    (h : HarperGeometrySecondMomentCertificate) :
    PositiveBlockOmega :=
  positiveBlockOmega_of_harperTestPointSecondMomentCertificate
    (harperTestPointSecondMomentCertificate_of_geometry h)

/-- Direct closure from the geometry-refined test-point Harper certificate. -/
theorem erdos1144_of_harperGeometrySecondMomentCertificate
    (h : HarperGeometrySecondMomentCertificate) :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    (positiveBlockOmega_of_harperGeometrySecondMomentCertificate h)

/-- A finite-kernel geometry certificate gives the active positive block
certificate. -/
noncomputable def positiveBlockOmega_of_harperGeometryFiniteKernelCertificate
    (h : HarperGeometryFiniteKernelCertificate) :
    PositiveBlockOmega :=
  positiveBlockOmega_of_harperGeometrySecondMomentCertificate
    (harperGeometrySecondMomentCertificate_of_finiteKernel h)

/-- Direct closure from the finite-kernel geometry certificate. -/
theorem erdos1144_of_harperGeometryFiniteKernelCertificate
    (h : HarperGeometryFiniteKernelCertificate) :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    (positiveBlockOmega_of_harperGeometryFiniteKernelCertificate h)

end Problem1144
end Erdos
