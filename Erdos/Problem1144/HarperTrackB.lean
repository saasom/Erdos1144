import Erdos.Problem1144.SquareConvolution
import Erdos.Problem1144.PositiveBlockCertificate
import Mathlib.Analysis.Convex.Integral

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-!
# Track B: squarefree Brownian block transfer

This is the limited closure route:

* prove a Brownian one-sided block theorem for the squarefree critical process
  `R(N) = sum_{d <= N+1, d squarefree} f(d) / sqrt(d)`;
* control the complete-to-squarefree error on the deterministic block grid;
* conclude the one-sided complete-model Erdős #1144 statement.

The Harper/weighted-Proposition-3 machinery remains available as the broader
route.  This file only formalizes the elementary transfer once the squarefree
Brownian block theorem and grid-error estimates are supplied.
-/

/-- Squarefree critical sum on the same shifted endpoint convention as
`normSum`: input `N` corresponds to the cutoff `N + 1`. -/
noncomputable def squarefreeCriticalSum (omega : Omega) (N : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 1 (N + 1)) fun d =>
    gSquarefree omega d / Real.sqrt ((d : ℕ) : ℝ)

/-- Complete normalized sum minus the squarefree critical approximation. -/
noncomputable def trackBError (omega : Omega) (N : ℕ) : ℝ :=
  normSum omega N - squarefreeCriticalSum omega N

/-- The squarefree critical approximation is measurable for each shifted
cutoff. -/
theorem measurable_squarefreeCriticalSum (N : ℕ) :
    Measurable fun omega : Omega => squarefreeCriticalSum omega N := by
  unfold squarefreeCriticalSum
  exact
    Finset.measurable_sum _ fun d _ =>
      (measurable_gSquarefree d).div_const _

/-- The Track B complete-to-squarefree error is measurable for each shifted
cutoff. -/
theorem measurable_trackBError (N : ℕ) :
    Measurable fun omega : Omega => trackBError omega N := by
  unfold trackBError
  exact (measurable_normSum N).sub (measurable_squarefreeCriticalSum N)

/-- The squarefree Brownian block succeeds if, from the fixed base endpoint,
some grid point has a positive squarefree critical increment of size `B j`. -/
def trackBSquarefreeBlockSuccess
    (base : ℕ) (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ)
    (B : ℕ → ℝ) (omega : Omega) (j : ℕ) : Prop :=
  ∃ m ∈ Finset.Icc 1 (mesh j),
    B j ≤
      squarefreeCriticalSum omega (endpoint j m) -
        squarefreeCriticalSum omega base

/-- Failure of the squarefree Brownian block event. -/
def trackBSquarefreeBlockFailure
    (base : ℕ) (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ)
    (B : ℕ → ℝ) (j : ℕ) : Set Omega :=
  {omega | ¬ trackBSquarefreeBlockSuccess base endpoint mesh B omega j}

/-- Moving-base version of the squarefree Brownian block event.  This matches
the stage construction where `U_j` and hence the base endpoint vary with `j`. -/
def trackBMovingSquarefreeBlockSuccess
    (base : ℕ → ℕ) (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ)
    (B : ℕ → ℝ) (omega : Omega) (j : ℕ) : Prop :=
  ∃ m ∈ Finset.Icc 1 (mesh j),
    B j ≤
      squarefreeCriticalSum omega (endpoint j m) -
        squarefreeCriticalSum omega (base j)

/-- Failure of the moving-base squarefree Brownian block event. -/
def trackBMovingSquarefreeBlockFailure
    (base : ℕ → ℕ) (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ)
    (B : ℕ → ℝ) (j : ℕ) : Set Omega :=
  {omega | ¬ trackBMovingSquarefreeBlockSuccess base endpoint mesh B omega j}

/-- The moving-base starting squarefree critical value is not too negative. -/
def trackBStartGood
    (base : ℕ → ℕ) (A : ℕ → ℝ) (omega : Omega) (j : ℕ) : Prop :=
  -A j ≤ squarefreeCriticalSum omega (base j)

/-- Failure of the moving-base start-value event. -/
def trackBStartFailure
    (base : ℕ → ℕ) (A : ℕ → ℝ) (j : ℕ) : Set Omega :=
  {omega | ¬ trackBStartGood base A omega j}

/-- The complete-to-squarefree error is small on the deterministic grid. -/
def trackBGridErrorGood
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) (A : ℕ → ℝ)
    (omega : Omega) (j : ℕ) : Prop :=
  ∀ m, m ∈ Finset.Icc 1 (mesh j) →
    |trackBError omega (endpoint j m)| ≤ A j

/-- Failure of the grid-error event. -/
def trackBGridErrorFailure
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) (A : ℕ → ℝ)
    (j : ℕ) : Set Omega :=
  {omega | ¬ trackBGridErrorGood endpoint mesh A omega j}

/-- Measurability of the fixed-base squarefree Brownian block success event. -/
theorem measurableSet_trackBSquarefreeBlockSuccess
    (base : ℕ) (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ)
    (B : ℕ → ℝ) (j : ℕ) :
    MeasurableSet
      {omega | trackBSquarefreeBlockSuccess base endpoint mesh B omega j} := by
  classical
  rw [show
      {omega | trackBSquarefreeBlockSuccess base endpoint mesh B omega j} =
        ⋃ m ∈ Finset.Icc 1 (mesh j),
          {omega |
            B j ≤
              squarefreeCriticalSum omega (endpoint j m) -
                squarefreeCriticalSum omega base} by
      ext omega
      simp [trackBSquarefreeBlockSuccess]]
  exact
    Finset.measurableSet_biUnion _ fun m _hm =>
      measurableSet_le measurable_const
        ((measurable_squarefreeCriticalSum (endpoint j m)).sub
          (measurable_squarefreeCriticalSum base))

/-- Measurability of the fixed-base squarefree Brownian block failure event. -/
theorem measurableSet_trackBSquarefreeBlockFailure
    (base : ℕ) (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ)
    (B : ℕ → ℝ) (j : ℕ) :
    MeasurableSet (trackBSquarefreeBlockFailure base endpoint mesh B j) := by
  rw [trackBSquarefreeBlockFailure]
  change
    MeasurableSet
      ({omega | trackBSquarefreeBlockSuccess base endpoint mesh B omega j}ᶜ)
  exact
    (measurableSet_trackBSquarefreeBlockSuccess base endpoint mesh B j).compl

/-- Measurability of the moving-base squarefree Brownian block success event. -/
theorem measurableSet_trackBMovingSquarefreeBlockSuccess
    (base : ℕ → ℕ) (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ)
    (B : ℕ → ℝ) (j : ℕ) :
    MeasurableSet
      {omega | trackBMovingSquarefreeBlockSuccess base endpoint mesh B omega j} := by
  classical
  rw [show
      {omega | trackBMovingSquarefreeBlockSuccess base endpoint mesh B omega j} =
        ⋃ m ∈ Finset.Icc 1 (mesh j),
          {omega |
            B j ≤
              squarefreeCriticalSum omega (endpoint j m) -
                squarefreeCriticalSum omega (base j)} by
      ext omega
      simp [trackBMovingSquarefreeBlockSuccess]]
  exact
    Finset.measurableSet_biUnion _ fun m _hm =>
      measurableSet_le measurable_const
        ((measurable_squarefreeCriticalSum (endpoint j m)).sub
          (measurable_squarefreeCriticalSum (base j)))

/-- Measurability of the moving-base squarefree Brownian block failure event. -/
theorem measurableSet_trackBMovingSquarefreeBlockFailure
    (base : ℕ → ℕ) (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ)
    (B : ℕ → ℝ) (j : ℕ) :
    MeasurableSet (trackBMovingSquarefreeBlockFailure base endpoint mesh B j) := by
  rw [trackBMovingSquarefreeBlockFailure]
  change
    MeasurableSet
      ({omega | trackBMovingSquarefreeBlockSuccess base endpoint mesh B omega j}ᶜ)
  exact
    (measurableSet_trackBMovingSquarefreeBlockSuccess base endpoint mesh B j).compl

/-- Measurability of the moving-base start-value good event. -/
theorem measurableSet_trackBStartGood
    (base : ℕ → ℕ) (A : ℕ → ℝ) (j : ℕ) :
    MeasurableSet {omega | trackBStartGood base A omega j} := by
  unfold trackBStartGood
  exact measurableSet_le measurable_const
    (measurable_squarefreeCriticalSum (base j))

/-- Measurability of the moving-base start-value failure event. -/
theorem measurableSet_trackBStartFailure
    (base : ℕ → ℕ) (A : ℕ → ℝ) (j : ℕ) :
    MeasurableSet (trackBStartFailure base A j) := by
  rw [trackBStartFailure]
  change MeasurableSet ({omega | trackBStartGood base A omega j}ᶜ)
  exact (measurableSet_trackBStartGood base A j).compl

/-- Measurability of the deterministic-grid error good event. -/
theorem measurableSet_trackBGridErrorGood
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) (A : ℕ → ℝ)
    (j : ℕ) :
    MeasurableSet {omega | trackBGridErrorGood endpoint mesh A omega j} := by
  classical
  rw [show
      {omega | trackBGridErrorGood endpoint mesh A omega j} =
        ⋂ m ∈ Finset.Icc 1 (mesh j),
          {omega | |trackBError omega (endpoint j m)| ≤ A j} by
      ext omega
      simp [trackBGridErrorGood]]
  exact
    Finset.measurableSet_biInter _ fun m _hm =>
      by
        rw [show
            {omega | |trackBError omega (endpoint j m)| ≤ A j} =
              ((fun omega : Omega => trackBError omega (endpoint j m)) ⁻¹'
                Set.Icc (-(A j)) (A j)) by
            ext omega
            simp [abs_le]]
        exact (measurable_trackBError (endpoint j m)) measurableSet_Icc

/-- Measurability of the deterministic-grid error failure event. -/
theorem measurableSet_trackBGridErrorFailure
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) (A : ℕ → ℝ)
    (j : ℕ) :
    MeasurableSet (trackBGridErrorFailure endpoint mesh A j) := by
  rw [trackBGridErrorFailure]
  change
    MeasurableSet
      ({omega | trackBGridErrorGood endpoint mesh A omega j}ᶜ)
  exact (measurableSet_trackBGridErrorGood endpoint mesh A j).compl

/-- Finite Markov/union-bound budget for the Track B grid error. -/
noncomputable def trackBGridSecondMomentBudget
    (_endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) (A : ℕ → ℝ)
    (errorSecond : ℕ → ℕ → ℝ) (j : ℕ) : ℝ≥0∞ :=
  ∑ m ∈ Finset.Icc 1 (mesh j),
    ENNReal.ofReal (errorSecond j m / (A j) ^ 2)

/-- One-point Markov bound for a real error using its second moment. -/
theorem measure_abs_error_gt_le_second
    (E : Omega → ℝ) (A V : ℝ)
    (hA : 0 < A)
    (hint : Integrable (fun omega => (E omega) ^ 2) mu)
    (hsecond : (∫ omega, (E omega) ^ 2 ∂mu) ≤ V) :
    mu {omega | A < |E omega|} ≤ ENNReal.ofReal (V / A ^ 2) := by
  let T : Set Omega := {omega | A ^ 2 ≤ (E omega) ^ 2}
  have hsubset : {omega | A < |E omega|} ⊆ T := by
    intro omega hlt
    have hAle : A ≤ |E omega| := le_of_lt hlt
    have hsquare : A ^ 2 ≤ |E omega| ^ 2 :=
      pow_le_pow_left₀ hA.le hAle 2
    rw [← abs_pow] at hsquare
    simpa [T, abs_of_nonneg (by positivity : 0 ≤ (E omega) ^ 2)] using hsquare
  have hnonneg : 0 ≤ᵐ[mu] fun omega => (E omega) ^ 2 :=
    ae_of_all _ fun omega => by positivity
  have hmarkov :=
    mul_meas_ge_le_integral_of_nonneg (μ := mu)
      (f := fun omega => (E omega) ^ 2)
      hnonneg hint (A ^ 2)
  have hTreal : mu.real T ≤ V / A ^ 2 := by
    have hmul : A ^ 2 * mu.real T ≤ V :=
      le_trans hmarkov hsecond
    rw [le_div_iff₀ (pow_pos hA 2)]
    simpa [mul_comm] using hmul
  have hEreal : mu.real {omega | A < |E omega|} ≤ V / A ^ 2 :=
    (measureReal_mono hsubset).trans hTreal
  rw [← ofReal_measureReal (μ := mu) (s := {omega | A < |E omega|})]
  exact ENNReal.ofReal_le_ofReal hEreal

/-- Track B transfer certificate.

The only analytic inputs are the squarefree Brownian block failure bound and
the grid-error failure bound.  The base point is fixed; its squarefree critical
value is finite for each `omega`, and `B j -> infinity` makes it negligible
eventually, pointwise. -/
structure TrackBSquarefreeBrownianCertificate where
  base : ℕ
  endpoint : ℕ → ℕ → ℕ
  mesh : ℕ → ℕ
  level : ℕ → ℝ
  B : ℕ → ℝ
  A : ℕ → ℝ
  failBrownian : ℕ → ℝ≥0∞
  failError : ℕ → ℝ≥0∞
  B_pos : ∀ j, 0 < B j
  A_le_quarter_B : ∀ j, A j ≤ B j / 4
  level_le_half_B : ∀ j, level j ≤ B j / 2
  endpoint_tendsto_atTop :
    ∀ N0 : ℕ, ∀ᶠ j in atTop,
      ∀ m, m ∈ Finset.Icc 1 (mesh j) → N0 ≤ endpoint j m
  level_tendsto_atTop : Tendsto level atTop atTop
  B_tendsto_atTop : Tendsto B atTop atTop
  fail_summable : (∑' j, (failBrownian j + failError j)) ≠ ⊤
  prob_brownian_fail :
    ∀ j,
      mu (trackBSquarefreeBlockFailure base endpoint mesh B j) ≤
        failBrownian j
  prob_error_fail :
    ∀ j,
      mu (trackBGridErrorFailure endpoint mesh A j) ≤ failError j

/-- Track B certificate where the grid error is supplied by pointwise second
moments on the deterministic grid.

This is the formal version of the elementary estimate
`P(E_j^c) <= sum_m E |E_{N_{j,m}}|^2 / A_j^2`. -/
structure TrackBSecondMomentCertificate where
  base : ℕ
  endpoint : ℕ → ℕ → ℕ
  mesh : ℕ → ℕ
  level : ℕ → ℝ
  B : ℕ → ℝ
  A : ℕ → ℝ
  failBrownian : ℕ → ℝ≥0∞
  errorSecond : ℕ → ℕ → ℝ
  B_pos : ∀ j, 0 < B j
  A_pos : ∀ j, 0 < A j
  A_le_quarter_B : ∀ j, A j ≤ B j / 4
  level_le_half_B : ∀ j, level j ≤ B j / 2
  endpoint_tendsto_atTop :
    ∀ N0 : ℕ, ∀ᶠ j in atTop,
      ∀ m, m ∈ Finset.Icc 1 (mesh j) → N0 ≤ endpoint j m
  level_tendsto_atTop : Tendsto level atTop atTop
  B_tendsto_atTop : Tendsto B atTop atTop
  error_second_integrable :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      Integrable
        (fun omega => (trackBError omega (endpoint j m)) ^ 2) mu
  error_second_upper :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      (∫ omega, (trackBError omega (endpoint j m)) ^ 2 ∂mu) ≤
        errorSecond j m
  fail_summable :
    (∑' j,
      (failBrownian j +
        trackBGridSecondMomentBudget endpoint mesh A errorSecond j)) ≠ ⊤
  prob_brownian_fail :
    ∀ j,
      mu (trackBSquarefreeBlockFailure base endpoint mesh B j) ≤
        failBrownian j

/-- Pointwise Markov plus a finite union bound controls the Track B grid error
from deterministic-grid second moments. -/
theorem measure_trackBGridErrorFailure_le_secondMomentBudget
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) (A : ℕ → ℝ)
    (errorSecond : ℕ → ℕ → ℝ)
    (hA_pos : ∀ j, 0 < A j)
    (herror_int :
      ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
        Integrable
          (fun omega => (trackBError omega (endpoint j m)) ^ 2) mu)
    (herror_second :
      ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
        (∫ omega, (trackBError omega (endpoint j m)) ^ 2 ∂mu) ≤
          errorSecond j m)
    (j : ℕ) :
    mu (trackBGridErrorFailure endpoint mesh A j) ≤
      trackBGridSecondMomentBudget endpoint mesh A errorSecond j := by
  classical
  let s : Finset ℕ := Finset.Icc 1 (mesh j)
  let point : ℕ → Set Omega := fun m =>
    {omega | A j < |trackBError omega (endpoint j m)|}
  have hsubset :
      trackBGridErrorFailure endpoint mesh A j ⊆
        ⋃ m ∈ s, point m := by
    intro omega hfail
    change ¬ trackBGridErrorGood endpoint mesh A omega j at hfail
    unfold trackBGridErrorGood at hfail
    push Not at hfail
    rcases hfail with ⟨m, hm, hbad⟩
    exact Set.mem_iUnion₂.mpr ⟨m, hm, hbad⟩
  calc
    mu (trackBGridErrorFailure endpoint mesh A j)
        ≤ mu (⋃ m ∈ s, point m) :=
          measure_mono hsubset
    _ ≤ ∑ m ∈ s, mu (point m) :=
          MeasureTheory.measure_biUnion_finset_le s point
    _ ≤
        ∑ m ∈ s,
          ENNReal.ofReal (errorSecond j m / (A j) ^ 2) := by
          exact Finset.sum_le_sum fun m hm =>
            measure_abs_error_gt_le_second
              (E := fun omega =>
                trackBError omega (endpoint j m))
              (A := A j)
              (V := errorSecond j m)
              (hA_pos j)
              (herror_int j m hm)
              (herror_second j m hm)
    _ =
        trackBGridSecondMomentBudget endpoint mesh A errorSecond j := by
          rfl

/-- Markov bound for the moving-base start-value bad event.  The center is
allowed to be any nonnegative deterministic quantity; in the intended proof it
is `1`, coming from the squarefree term `d = 1`. -/
theorem measure_trackBStartFailure_le_second
    (base : ℕ → ℕ) (A center startSecond : ℕ → ℝ)
    (hA_pos : ∀ j, 0 < A j)
    (hcenter_nonneg : ∀ j, 0 ≤ center j)
    (hstart_int :
      ∀ j,
        Integrable
          (fun omega =>
            (squarefreeCriticalSum omega (base j) - center j) ^ 2) mu)
    (hstart_second :
      ∀ j,
        (∫ omega,
          (squarefreeCriticalSum omega (base j) - center j) ^ 2 ∂mu) ≤
            startSecond j) :
    ∀ j,
      mu (trackBStartFailure base A j) ≤
        ENNReal.ofReal (startSecond j / (A j) ^ 2) := by
  intro j
  have hsubset :
      trackBStartFailure base A j ⊆
        {omega | A j <
          |squarefreeCriticalSum omega (base j) - center j|} := by
    intro omega hbad
    change ¬ trackBStartGood base A omega j at hbad
    unfold trackBStartGood at hbad
    have hlt : squarefreeCriticalSum omega (base j) < -A j :=
      not_le.mp hbad
    have hgap :
        A j < center j - squarefreeCriticalSum omega (base j) := by
      linarith [hcenter_nonneg j]
    have hle :
        center j - squarefreeCriticalSum omega (base j) ≤
          |squarefreeCriticalSum omega (base j) - center j| := by
      simpa [abs_sub_comm] using
        (le_abs_self (center j - squarefreeCriticalSum omega (base j)))
    exact lt_of_lt_of_le hgap hle
  calc
    mu (trackBStartFailure base A j)
        ≤ mu {omega | A j <
          |squarefreeCriticalSum omega (base j) - center j|} :=
          measure_mono hsubset
    _ ≤ ENNReal.ofReal (startSecond j / (A j) ^ 2) :=
          measure_abs_error_gt_le_second
            (E := fun omega => squarefreeCriticalSum omega (base j) - center j)
            (A := A j)
            (V := startSecond j)
            (hA_pos j)
            (hstart_int j)
            (hstart_second j)

/-- Moving-base Track B certificate where the start-value and grid-error
events are both supplied by second-moment estimates. -/
structure TrackBMovingBaseSecondMomentCertificate where
  base : ℕ → ℕ
  endpoint : ℕ → ℕ → ℕ
  mesh : ℕ → ℕ
  level : ℕ → ℝ
  B : ℕ → ℝ
  A : ℕ → ℝ
  startCenter : ℕ → ℝ
  startSecond : ℕ → ℝ
  failBrownian : ℕ → ℝ≥0∞
  errorSecond : ℕ → ℕ → ℝ
  A_pos : ∀ j, 0 < A j
  startCenter_nonneg : ∀ j, 0 ≤ startCenter j
  level_margin : ∀ j, level j + 2 * A j ≤ B j
  endpoint_tendsto_atTop :
    ∀ N0 : ℕ, ∀ᶠ j in atTop,
      ∀ m, m ∈ Finset.Icc 1 (mesh j) → N0 ≤ endpoint j m
  level_tendsto_atTop : Tendsto level atTop atTop
  start_second_integrable :
    ∀ j,
      Integrable
        (fun omega =>
          (squarefreeCriticalSum omega (base j) - startCenter j) ^ 2) mu
  start_second_upper :
    ∀ j,
      (∫ omega,
        (squarefreeCriticalSum omega (base j) - startCenter j) ^ 2 ∂mu) ≤
          startSecond j
  error_second_integrable :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      Integrable
        (fun omega => (trackBError omega (endpoint j m)) ^ 2) mu
  error_second_upper :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      (∫ omega, (trackBError omega (endpoint j m)) ^ 2 ∂mu) ≤
        errorSecond j m
  fail_summable :
    (∑' j,
      (failBrownian j +
        ENNReal.ofReal (startSecond j / (A j) ^ 2) +
        trackBGridSecondMomentBudget endpoint mesh A errorSecond j)) ≠ ⊤
  prob_brownian_fail :
    ∀ j,
      mu (trackBMovingSquarefreeBlockFailure base endpoint mesh B j) ≤
        failBrownian j

/-- Moving-base Track B second-moment certificates imply Erdős #1144. -/
theorem erdos1144_of_trackBMovingBaseSecondMomentCertificate
    (h : TrackBMovingBaseSecondMomentCertificate) :
    Erdos1144 := by
  let brownFail : ℕ → Set Omega :=
    trackBMovingSquarefreeBlockFailure h.base h.endpoint h.mesh h.B
  let startFail : ℕ → Set Omega :=
    trackBStartFailure h.base h.A
  let errFail : ℕ → Set Omega :=
    trackBGridErrorFailure h.endpoint h.mesh h.A
  let F : ℕ → Set Omega := fun j =>
    brownFail j ∪ (startFail j ∪ errFail j)
  have hstart_prob :
      ∀ j,
        mu (startFail j) ≤
          ENNReal.ofReal (h.startSecond j / (h.A j) ^ 2) :=
    measure_trackBStartFailure_le_second h.base h.A h.startCenter
      h.startSecond h.A_pos h.startCenter_nonneg
      h.start_second_integrable h.start_second_upper
  have herr_prob :
      ∀ j,
        mu (errFail j) ≤
          trackBGridSecondMomentBudget h.endpoint h.mesh h.A h.errorSecond j :=
    measure_trackBGridErrorFailure_le_secondMomentBudget
      h.endpoint h.mesh h.A h.errorSecond h.A_pos
      h.error_second_integrable h.error_second_upper
  have hprob :
      ∀ j,
        mu (F j) ≤
          h.failBrownian j +
            ENNReal.ofReal (h.startSecond j / (h.A j) ^ 2) +
            trackBGridSecondMomentBudget h.endpoint h.mesh h.A
              h.errorSecond j := by
    intro j
    calc
      mu (F j)
          ≤ mu (brownFail j) + mu (startFail j ∪ errFail j) :=
            measure_union_le _ _
      _ ≤ mu (brownFail j) + (mu (startFail j) + mu (errFail j)) :=
            add_le_add (le_refl _) (measure_union_le _ _)
      _ ≤
          h.failBrownian j +
            (ENNReal.ofReal (h.startSecond j / (h.A j) ^ 2) +
              trackBGridSecondMomentBudget h.endpoint h.mesh h.A
                h.errorSecond j) :=
            add_le_add
              (h.prob_brownian_fail j)
              (add_le_add (hstart_prob j) (herr_prob j))
      _ =
          h.failBrownian j +
            ENNReal.ofReal (h.startSecond j / (h.A j) ^ 2) +
            trackBGridSecondMomentBudget h.endpoint h.mesh h.A
              h.errorSecond j := by
          rw [add_assoc]
  have htsum : (∑' j, mu (F j)) ≠ ⊤ := by
    exact ne_top_of_le_ne_top h.fail_summable
      (ENNReal.tsum_le_tsum hprob)
  have hbc : mu (limsup F atTop) = 0 :=
    MeasureTheory.measure_limsup_atTop_eq_zero (μ := mu) (s := F) htsum
  have hnotlimsup : ∀ᵐ omega ∂mu, omega ∉ limsup F atTop := by
    rw [MeasureTheory.ae_iff]
    simpa using hbc
  filter_upwards [hnotlimsup] with omega homega A0
  have hgood_eventually : ∀ᶠ j : ℕ in atTop, omega ∉ F j := by
    rw [Filter.mem_limsup_iff_frequently_mem] at homega
    simpa [F, Filter.Frequently] using homega
  rw [Filter.Frequently]
  intro hbad
  rw [eventually_atTop] at hbad
  rcases hbad with ⟨N0, hN0⟩
  have hlevel_eventually : ∀ᶠ j : ℕ in atTop, A0 ≤ h.level j :=
    h.level_tendsto_atTop.eventually_ge_atTop A0
  have hend_eventually := h.endpoint_tendsto_atTop N0
  rcases (hgood_eventually.and (hlevel_eventually.and hend_eventually)).exists
    with ⟨j, hnotF, hlevel, hend⟩
  have hbrownian :
      trackBMovingSquarefreeBlockSuccess h.base h.endpoint h.mesh h.B omega j := by
    by_contra hno
    exact hnotF (Or.inl hno)
  have hstart :
      trackBStartGood h.base h.A omega j := by
    by_contra hno
    exact hnotF (Or.inr (Or.inl hno))
  have herror :
      trackBGridErrorGood h.endpoint h.mesh h.A omega j := by
    by_contra hno
    exact hnotF (Or.inr (Or.inr hno))
  rcases hbrownian with ⟨m, hm, hinc⟩
  let N := h.endpoint j m
  have hNlarge : N0 ≤ N := hend m hm
  have hRlarge :
      h.B j - h.A j ≤ squarefreeCriticalSum omega N := by
    dsimp [N]
    unfold trackBStartGood at hstart
    nlinarith
  have herr_abs : |trackBError omega N| ≤ h.A j := by
    exact herror m hm
  have herr_ge : -h.A j ≤ trackBError omega N :=
    (abs_le.mp herr_abs).1
  have hnorm_eq :
      normSum omega N =
        squarefreeCriticalSum omega N + trackBError omega N := by
    unfold trackBError
    ring
  have hnorm_ge : h.level j ≤ normSum omega N := by
    rw [hnorm_eq]
    have hmarg := h.level_margin j
    nlinarith
  exact hN0 N hNlarge (le_trans hlevel hnorm_ge)

/-- Convert a Track B second-moment grid-error certificate into the base
Track B transfer certificate. -/
noncomputable def trackBSquarefreeBrownianCertificate_of_secondMoment
    (h : TrackBSecondMomentCertificate) :
    TrackBSquarefreeBrownianCertificate where
  base := h.base
  endpoint := h.endpoint
  mesh := h.mesh
  level := h.level
  B := h.B
  A := h.A
  failBrownian := h.failBrownian
  failError := fun j =>
    trackBGridSecondMomentBudget h.endpoint h.mesh h.A h.errorSecond j
  B_pos := h.B_pos
  A_le_quarter_B := h.A_le_quarter_B
  level_le_half_B := h.level_le_half_B
  endpoint_tendsto_atTop := h.endpoint_tendsto_atTop
  level_tendsto_atTop := h.level_tendsto_atTop
  B_tendsto_atTop := h.B_tendsto_atTop
  fail_summable := h.fail_summable
  prob_brownian_fail := h.prob_brownian_fail
  prob_error_fail :=
    measure_trackBGridErrorFailure_le_secondMomentBudget
      h.endpoint h.mesh h.A h.errorSecond h.A_pos
      h.error_second_integrable h.error_second_upper

private theorem trackB_base_eventually_lower
    (h : TrackBSquarefreeBrownianCertificate) (omega : Omega) :
    ∀ᶠ j in atTop,
      -h.B j / 4 ≤ squarefreeCriticalSum omega h.base := by
  let C := squarefreeCriticalSum omega h.base
  have hB :
      ∀ᶠ j in atTop, max 0 (-4 * C) ≤ h.B j :=
    h.B_tendsto_atTop.eventually_ge_atTop (max 0 (-4 * C))
  filter_upwards [hB] with j hj
  have hge : -4 * C ≤ h.B j := le_trans (le_max_right _ _) hj
  nlinarith

/-- Track B squarefree Brownian certificates imply Erdős #1144 directly.

This proof deliberately does not package the result as `PositiveBlockOmega`:
the squarefree Brownian theorem starts from a fixed base point, and the base
value is disposed of pointwise using `B j -> infinity`, not by adding a third
summable probability budget. -/
theorem erdos1144_of_trackBSquarefreeBrownianCertificate
    (h : TrackBSquarefreeBrownianCertificate) :
    Erdos1144 := by
  let brownFail : ℕ → Set Omega :=
    trackBSquarefreeBlockFailure h.base h.endpoint h.mesh h.B
  let errFail : ℕ → Set Omega :=
    trackBGridErrorFailure h.endpoint h.mesh h.A
  let F : ℕ → Set Omega := fun j => brownFail j ∪ errFail j
  have hprob : ∀ j, mu (F j) ≤ h.failBrownian j + h.failError j := by
    intro j
    calc
      mu (F j) ≤ mu (brownFail j) + mu (errFail j) :=
        measure_union_le _ _
      _ ≤ h.failBrownian j + h.failError j :=
        add_le_add (h.prob_brownian_fail j) (h.prob_error_fail j)
  have htsum : (∑' j, mu (F j)) ≠ ⊤ := by
    exact ne_top_of_le_ne_top h.fail_summable
      (ENNReal.tsum_le_tsum hprob)
  have hbc : mu (limsup F atTop) = 0 :=
    MeasureTheory.measure_limsup_atTop_eq_zero (μ := mu) (s := F) htsum
  have hnotlimsup : ∀ᵐ omega ∂mu, omega ∉ limsup F atTop := by
    rw [MeasureTheory.ae_iff]
    simpa using hbc
  filter_upwards [hnotlimsup] with omega homega A0
  have hgood_eventually : ∀ᶠ j : ℕ in atTop, omega ∉ F j := by
    rw [Filter.mem_limsup_iff_frequently_mem] at homega
    simpa [F, Filter.Frequently] using homega
  rw [Filter.Frequently]
  intro hbad
  rw [eventually_atTop] at hbad
  rcases hbad with ⟨N0, hN0⟩
  have hbase_eventually := trackB_base_eventually_lower h omega
  have hlevel_eventually : ∀ᶠ j : ℕ in atTop, A0 ≤ h.level j :=
    h.level_tendsto_atTop.eventually_ge_atTop A0
  have hend_eventually := h.endpoint_tendsto_atTop N0
  rcases
    (hgood_eventually.and
      (hbase_eventually.and (hlevel_eventually.and hend_eventually))).exists
    with ⟨j, hnotF, hbase, hlevel, hend⟩
  have hbrownian :
      trackBSquarefreeBlockSuccess h.base h.endpoint h.mesh h.B omega j := by
    by_contra hno
    exact hnotF (Or.inl hno)
  have herror :
      trackBGridErrorGood h.endpoint h.mesh h.A omega j := by
    by_contra hno
    exact hnotF (Or.inr hno)
  rcases hbrownian with ⟨m, hm, hinc⟩
  let N := h.endpoint j m
  have hNlarge : N0 ≤ N := hend m hm
  have hRlarge :
      3 * h.B j / 4 ≤ squarefreeCriticalSum omega N := by
    dsimp [N]
    nlinarith
  have herr_abs : |trackBError omega N| ≤ h.A j := by
    exact herror m hm
  have herr_ge_negA : -h.A j ≤ trackBError omega N :=
    (abs_le.mp herr_abs).1
  have herr_ge :
      -h.B j / 4 ≤ trackBError omega N := by
    have hA := h.A_le_quarter_B j
    linarith
  have hnorm_eq :
      normSum omega N =
        squarefreeCriticalSum omega N + trackBError omega N := by
    unfold trackBError
    ring
  have hnorm_ge_half : h.B j / 2 ≤ normSum omega N := by
    rw [hnorm_eq]
    nlinarith
  have htarget : A0 ≤ normSum omega N :=
    le_trans hlevel (le_trans (h.level_le_half_B j) hnorm_ge_half)
  exact hN0 N hNlarge htarget

end Problem1144
end Erdos
