import Erdos.Problem1144.HarperIncrement
import Erdos.Problem1144.HarperAbundance
import Erdos.Problem1144.HarperWeightedProp3
import Mathlib.Analysis.PSeries

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-- The squarefree density constant appearing in the raw kernel asymptotic. -/
noncomputable def cSf : ℝ := 6 / Real.pi ^ 2

/-- Brownian covariance profile for the complete-model raw value vectors. -/
noncomputable def brownianI (a : ℝ) : ℝ :=
  a * Real.log a - a + 1

/-- Mean covariance kernel for the already-formalized complete-model
large-prime coefficient vectors. -/
noncomputable def largePrimeCovarianceMean (X M N : ℕ) : ℝ :=
  ∫ omega, largePrimeCovariance omega X M N ∂mu

/-- The variance combination associated to an increment, for an abstract
real-exponent raw kernel `K`. -/
noncomputable def kernelIncrementVariance
    (K : ℕ → ℝ → ℝ → ℝ) (X : ℕ) (a eta : ℝ) : ℝ :=
  K X (a + eta) (a + eta) + K X a a - 2 * K X a (a + eta)

/-- The covariance combination associated to two increments, for an abstract
real-exponent raw kernel `K`. -/
noncomputable def kernelIncrementCovariance
    (K : ℕ → ℝ → ℝ → ℝ) (X : ℕ)
    (a eta b theta : ℝ) : ℝ :=
  K X (a + eta) (b + theta) -
    K X (a + eta) b -
      K X a (b + theta) +
        K X a b

/-- Pointwise raw-kernel approximation by the nested Brownian main term. -/
def rawKernelApproxAt
    (K : ℕ → ℝ → ℝ → ℝ) (C : ℝ) (X : ℕ) (a b : ℝ) : Prop :=
  |K X a b - cSf * brownianI (min a b) * Real.log (X : ℝ)| ≤ C

/-- Lean-facing raw kernel asymptotic interface.

This is intentionally an analytic input: the square-kernel/PNT proof belongs
outside the first increment-geometry formalization pass. -/
structure RawKernelAsymptotic where
  K : ℕ → ℝ → ℝ → ℝ
  C : ℝ
  C_nonneg : 0 ≤ C
  aMin : ℝ
  aMax : ℝ
  eventually_bound :
    ∀ᶠ X in atTop,
      ∀ a b : ℝ,
        aMin ≤ a → a ≤ aMax →
        aMin ≤ b → b ≤ aMax →
          rawKernelApproxAt K C X a b

private theorem abs_variance_combo_le
    {A B Cc A₀ B₀ C₀ E : ℝ}
    (hA : |A - A₀| ≤ E)
    (hB : |B - B₀| ≤ E)
    (hC : |Cc - C₀| ≤ E) :
    |(A + B - 2 * Cc) - (A₀ + B₀ - 2 * C₀)| ≤ 4 * E := by
  let x := A - A₀
  let y := B - B₀
  let z := Cc - C₀
  have hrewrite :
      (A + B - 2 * Cc) - (A₀ + B₀ - 2 * C₀) = x + y - 2 * z := by
    ring
  rw [hrewrite]
  calc
    |x + y - 2 * z| ≤ |x| + |y| + 2 * |z| := by
      have h1 : |x + y - 2 * z| ≤ |x + y| + |2 * z| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (x + y) (-(2 * z))
      have h2 : |x + y| ≤ |x| + |y| := abs_add_le _ _
      have h3 : |2 * z| = 2 * |z| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith
    _ ≤ 4 * E := by nlinarith

private theorem abs_second_difference_le
    {A B Cc D A₀ B₀ C₀ D₀ E : ℝ}
    (hA : |A - A₀| ≤ E)
    (hB : |B - B₀| ≤ E)
    (hC : |Cc - C₀| ≤ E)
    (hD : |D - D₀| ≤ E)
    (hmain : A₀ - B₀ - C₀ + D₀ = 0) :
    |(A - B - Cc + D)| ≤ 4 * E := by
  let x := A - A₀
  let y := B - B₀
  let z := Cc - C₀
  let w := D - D₀
  have hrewrite :
      A - B - Cc + D = x - y - z + w := by
    nlinarith
  rw [hrewrite]
  calc
    |x - y - z + w| ≤ |x| + |y| + |z| + |w| := by
      have h1 : |x - y - z + w| ≤ |x - y - z| + |w| := abs_add_le _ _
      have h2 : |x - y - z| ≤ |x - y| + |z| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (x - y) (-z)
      have h3 : |x - y| ≤ |x| + |y| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)
      nlinarith
    _ ≤ 4 * E := by nlinarith

/-- Raw-kernel approximation gives the increment variance main term in exact
first-difference form. Taylor expansion to `cSf * log a * ell` is kept as a
separate analytic/numerical input. -/
theorem kernelIncrementVariance_approx
    {K : ℕ → ℝ → ℝ → ℝ} {C : ℝ} {X : ℕ} {a eta : ℝ}
    (heta_nonneg : 0 ≤ eta)
    (hAA : rawKernelApproxAt K C X (a + eta) (a + eta))
    (hA : rawKernelApproxAt K C X a a)
    (hCross : rawKernelApproxAt K C X a (a + eta)) :
    |kernelIncrementVariance K X a eta -
        cSf * (brownianI (a + eta) - brownianI a) *
          Real.log (X : ℝ)| ≤
      4 * C := by
  have hmin_cross : min a (a + eta) = a := by
    exact min_eq_left (by linarith)
  unfold rawKernelApproxAt at hAA hA hCross
  unfold kernelIncrementVariance
  have hmain :
      cSf * brownianI (a + eta) * Real.log (X : ℝ) +
        cSf * brownianI a * Real.log (X : ℝ) -
          2 * (cSf * brownianI a * Real.log (X : ℝ))
        =
      cSf * (brownianI (a + eta) - brownianI a) *
        Real.log (X : ℝ) := by
    ring
  have hcombo :=
    abs_variance_combo_le
      (A := K X (a + eta) (a + eta))
      (B := K X a a)
      (Cc := K X a (a + eta))
      (A₀ := cSf * brownianI (min (a + eta) (a + eta)) *
        Real.log (X : ℝ))
      (B₀ := cSf * brownianI (min a a) * Real.log (X : ℝ))
      (C₀ := cSf * brownianI (min a (a + eta)) * Real.log (X : ℝ))
      (E := C) hAA hA hCross
  simpa [min_self, hmin_cross, hmain] using hcombo

/-- If the Taylor/main-scale error is supplied separately, the increment
variance is close to `cSf * log a * ell`. -/
theorem kernelIncrementVariance_approx_scale
    {K : ℕ → ℝ → ℝ → ℝ} {C t : ℝ} {X : ℕ} {a eta ell : ℝ}
    (heta_nonneg : 0 ≤ eta)
    (hTaylor :
      |cSf * (brownianI (a + eta) - brownianI a) *
          Real.log (X : ℝ) -
        cSf * Real.log a * ell| ≤ t)
    (hAA : rawKernelApproxAt K C X (a + eta) (a + eta))
    (hA : rawKernelApproxAt K C X a a)
    (hCross : rawKernelApproxAt K C X a (a + eta)) :
    |kernelIncrementVariance K X a eta -
        cSf * Real.log a * ell| ≤ 4 * C + t := by
  have hfirst :=
    kernelIncrementVariance_approx
      (K := K) (C := C) (X := X) (a := a) (eta := eta)
      heta_nonneg hAA hA hCross
  calc
    |kernelIncrementVariance K X a eta - cSf * Real.log a * ell|
        =
        |(kernelIncrementVariance K X a eta -
            cSf * (brownianI (a + eta) - brownianI a) *
              Real.log (X : ℝ)) +
          (cSf * (brownianI (a + eta) - brownianI a) *
              Real.log (X : ℝ) -
            cSf * Real.log a * ell)| := by ring_nf
    _ ≤
        |kernelIncrementVariance K X a eta -
            cSf * (brownianI (a + eta) - brownianI a) *
              Real.log (X : ℝ)| +
          |cSf * (brownianI (a + eta) - brownianI a) *
              Real.log (X : ℝ) -
            cSf * Real.log a * ell| :=
          abs_add_le _ _
    _ ≤ 4 * C + t := by nlinarith

/-- For disjoint exponent increments, the nested Brownian main terms cancel in
the second difference. -/
theorem kernelIncrementCovariance_brownian_cancel
    {K : ℕ → ℝ → ℝ → ℝ} {C : ℝ} {X : ℕ}
    {a eta b theta : ℝ}
    (heta_nonneg : 0 ≤ eta)
    (htheta_nonneg : 0 ≤ theta)
    (hdisj : a + eta ≤ b)
    (hAQ : rawKernelApproxAt K C X (a + eta) (b + theta))
    (hAB : rawKernelApproxAt K C X (a + eta) b)
    (haQ : rawKernelApproxAt K C X a (b + theta))
    (haB : rawKernelApproxAt K C X a b) :
    |kernelIncrementCovariance K X a eta b theta| ≤ 4 * C := by
  have hb_le_btheta : b ≤ b + theta := by linarith
  have ha_le_aeta : a ≤ a + eta := by linarith
  have hminAQ : min (a + eta) (b + theta) = a + eta := by
    exact min_eq_left (by linarith)
  have hminAB : min (a + eta) b = a + eta := by
    exact min_eq_left hdisj
  have hminaQ : min a (b + theta) = a := by
    exact min_eq_left (by linarith)
  have hminaB : min a b = a := by
    exact min_eq_left (by linarith)
  unfold rawKernelApproxAt at hAQ hAB haQ haB
  unfold kernelIncrementCovariance
  have hcombo :=
    abs_second_difference_le
      (A := K X (a + eta) (b + theta))
      (B := K X (a + eta) b)
      (Cc := K X a (b + theta))
      (D := K X a b)
      (A₀ := cSf * brownianI (min (a + eta) (b + theta)) *
        Real.log (X : ℝ))
      (B₀ := cSf * brownianI (min (a + eta) b) *
        Real.log (X : ℝ))
      (C₀ := cSf * brownianI (min a (b + theta)) *
        Real.log (X : ℝ))
      (D₀ := cSf * brownianI (min a b) * Real.log (X : ℝ))
      (E := C) hAQ hAB haQ haB
      (by simp [hminAQ, hminAB, hminaQ, hminaB])
  simpa using hcombo

/-- Abstract growth and spacing requirements for the increment covariance
route. These are deliberately parameterized to avoid hard-coding a fragile
choice of `rho_j` or `ell_j`. -/
structure IncrementParameterConditions where
  X : ℕ → ℕ
  ell : ℕ → ℝ
  rho : ℕ → ℝ
  u : ℕ → ℝ
  V : ℕ → ℝ
  ell_tendsto_atTop : Tendsto ell atTop atTop
  ell_over_logX_tendsto_zero :
    Tendsto (fun j => ell j / Real.log (X j : ℝ)) atTop (nhds 0)
  rho_u_sq_summable : Summable fun j => rho j * (u j) ^ 2
  rho_V_tendsto_atTop : Tendsto (fun j => rho j * V j) atTop atTop

/-- Safe polynomial increment length. -/
noncomputable def safeIncrementEll (j : ℕ) : ℝ :=
  (((j + 1 : ℕ) : ℝ) ^ 6)

/-- Safe polynomial correlation ceiling. -/
noncomputable def safeIncrementRho (j : ℕ) : ℝ :=
  (((j + 1 : ℕ) : ℝ) ^ 4)⁻¹

/-- Safe polynomial threshold scale. -/
noncomputable def safeIncrementU (j : ℕ) : ℝ :=
  4 * ((j + 1 : ℕ) : ℝ)

/-- The elementary summable part of the safe polynomial choice:
`rho_j * u_j^2` is a constant multiple of `(j+1)^(-2)`. -/
theorem safeIncrement_rho_u_sq_summable :
    Summable fun j => safeIncrementRho j * (safeIncrementU j) ^ 2 := by
  have hbase : Summable fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
  have hshift :
      Summable fun j : ℕ => ((((j + 1 : ℕ) : ℝ) ^ (2 : ℝ)))⁻¹ := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) 1).mpr
        hbase
  refine (Summable.mul_left 16 hshift).congr ?_
  intro j
  have hj : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp [safeIncrementRho, safeIncrementU]
  field_simp [hj]
  ring

/-- Constructor for the safe polynomial parameter choice. The facts involving
`X_j` and `V_j` remain explicit hypotheses, since those are analytic
large-scale choices. -/
noncomputable def safePolynomialIncrementParameters
    (X : ℕ → ℕ) (V : ℕ → ℝ)
    (hell : Tendsto safeIncrementEll atTop atTop)
    (hell_log :
      Tendsto
        (fun j => safeIncrementEll j / Real.log (X j : ℝ))
        atTop (nhds 0))
    (hrhoV :
      Tendsto (fun j => safeIncrementRho j * V j) atTop atTop) :
    IncrementParameterConditions where
  X := X
  ell := safeIncrementEll
  rho := safeIncrementRho
  u := safeIncrementU
  V := V
  ell_tendsto_atTop := hell
  ell_over_logX_tendsto_zero := hell_log
  rho_u_sq_summable := safeIncrement_rho_u_sq_summable
  rho_V_tendsto_atTop := hrhoV

/-- Increment geometry good event: variances are comparable, increment
covariances are small, coefficients are flat, and the pruned mesh is large. -/
def incrementGeometryGood
    (cut : ℕ → ℕ)
    (leftEnd : ℕ → ℕ → ℕ)
    (rightEnd : ℕ → ℕ → ℕ)
    (indexSet : ℕ → Finset ℕ)
    (V : ℕ → ℝ)
    (rho : ℕ → ℝ)
    (flat : ℕ → ℝ)
    (K : ℕ → ℕ)
    (j : ℕ) : Set Omega :=
  {omega |
    K j ≤ (indexSet j).card ∧
      (∀ r ∈ indexSet j,
      (1 - (j + 1 : ℝ)⁻¹) * V j ≤
        largePrimeIncrementVariance omega (cut j) (leftEnd j r) (rightEnd j r) ∧
      largePrimeIncrementVariance omega (cut j) (leftEnd j r) (rightEnd j r) ≤
        (1 + (j + 1 : ℝ)⁻¹) * V j) ∧
    (∀ r ∈ indexSet j, ∀ s ∈ indexSet j, r ≠ s →
      |largePrimeIncrementCovariance omega (cut j)
        (leftEnd j r) (rightEnd j r) (leftEnd j s) (rightEnd j s)| ≤
          rho j * V j) ∧
    (∀ r ∈ indexSet j, ∀ p ∈ largePrimeIncrementSupport (cut j) (leftEnd j r) (rightEnd j r),
      |largePrimeIncrementCoeff omega (cut j) (leftEnd j r) (rightEnd j r) p| ≤ flat j)}

/-- Off-path increment geometry certificate. The analytic work is concentrated
in `prob_good`; downstream comparison and one-sided value recovery are kept as
separate interfaces. -/
structure HarperIncrementGeometryCertificate where
  cut : ℕ → ℕ
  leftEnd : ℕ → ℕ → ℕ
  rightEnd : ℕ → ℕ → ℕ
  indexSet : ℕ → Finset ℕ
  V : ℕ → ℝ
  rho : ℕ → ℝ
  flat : ℕ → ℝ
  K : ℕ → ℕ
  failGood : ℕ → ℝ≥0∞
  params : IncrementParameterConditions
  fail_summable : (∑' j, failGood j) ≠ ⊤
  prob_good :
    ∀ j,
      mu (incrementGeometryGood cut leftEnd rightEnd indexSet V rho flat K j)ᶜ ≤
        failGood j

/-- Increment threshold exceedance set for the large-prime increment process.
This is intentionally off-path: a separate endpoint/offset bridge is still
needed before increments can imply one-sided positive values. -/
noncomputable def incrementExceedanceSet
    (cut : ℕ → ℕ)
    (leftEnd : ℕ → ℕ → ℕ)
    (rightEnd : ℕ → ℕ → ℕ)
    (indexSet : ℕ → Finset ℕ)
    (threshold : ℕ → ℝ)
    (omega : Omega) (j : ℕ) : Finset ℕ := by
  classical
  exact
    (indexSet j).filter fun r =>
      threshold j ≤
        |largePrimeIncrementProcess omega (cut j) (leftEnd j r) (rightEnd j r)|

noncomputable def incrementExceedanceCountReal
    (cut : ℕ → ℕ)
    (leftEnd : ℕ → ℕ → ℕ)
    (rightEnd : ℕ → ℕ → ℕ)
    (indexSet : ℕ → Finset ℕ)
    (threshold : ℕ → ℝ)
    (j : ℕ) (omega : Omega) : ℝ :=
  ((incrementExceedanceSet cut leftEnd rightEnd indexSet threshold omega j).card : ℝ)

def incrementFewExceedances
    (cut : ℕ → ℕ)
    (leftEnd : ℕ → ℕ → ℕ)
    (rightEnd : ℕ → ℕ → ℕ)
    (indexSet : ℕ → Finset ℕ)
    (threshold : ℕ → ℝ)
    (r : ℕ → ℕ)
    (j : ℕ) : Set Omega :=
  {omega | (incrementExceedanceSet cut leftEnd rightEnd indexSet threshold omega j).card < r j}

/-- Count-moment abundance certificate for increment exceedances. This reuses
the Chebyshev abundance layer but deliberately does not yet imply
`PositiveBlockOmega`. -/
structure HarperIncrementAbundanceCertificate where
  cut : ℕ → ℕ
  leftEnd : ℕ → ℕ → ℕ
  rightEnd : ℕ → ℕ → ℕ
  indexSet : ℕ → Finset ℕ
  threshold : ℕ → ℝ
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
          (incrementExceedanceCountReal
              cut leftEnd rightEnd indexSet threshold j omega -
            ∫ omega',
              incrementExceedanceCountReal
                cut leftEnd rightEnd indexSet threshold j omega' ∂mu) ^ 2)
        mu
  count_mean_lower :
    ∀ j,
      countMean j ≤
        ∫ omega, incrementExceedanceCountReal cut leftEnd rightEnd indexSet threshold j omega ∂mu
  count_centered_second_upper :
    ∀ j,
      (∫ omega,
          (incrementExceedanceCountReal
              cut leftEnd rightEnd indexSet threshold j omega -
            ∫ omega',
              incrementExceedanceCountReal
                cut leftEnd rightEnd indexSet threshold j omega' ∂mu) ^ 2 ∂mu)
        ≤ countSecond j

/-- Increment abundance lower-tail bound. This is the same finite
second-moment mechanism used by the active threshold-abundance route, now
specialized to increment exceedances. -/
theorem measure_incrementFewExceedances_le
    (h : HarperIncrementAbundanceCertificate) (j : ℕ) :
    mu (incrementFewExceedances
      h.cut h.leftEnd h.rightEnd h.indexSet h.threshold h.r j)
      ≤ ENNReal.ofReal (4 * h.countSecond j / h.countMean j ^ 2) := by
  let R : Omega → ℝ :=
    incrementExceedanceCountReal h.cut h.leftEnd h.rightEnd h.indexSet h.threshold j
  let few : Set Omega :=
    incrementFewExceedances h.cut h.leftEnd h.rightEnd h.indexSet h.threshold h.r j
  have hfew_subset :
      few ⊆ {omega | R omega < h.countMean j / 2} := by
    intro omega hfew
    have hcard_lt :
        ((incrementExceedanceSet
            h.cut h.leftEnd h.rightEnd h.indexSet h.threshold omega j).card : ℝ)
          < (h.r j : ℝ) :=
      Nat.cast_lt.mpr hfew
    have hRdef :
        R omega =
          ((incrementExceedanceSet
            h.cut h.leftEnd h.rightEnd h.indexSet h.threshold omega j).card : ℝ) :=
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

/-- Off-path bridge from weighted Proposition 3 to the weighted bad-degree
event needed by increment covariance pruning.  This keeps the row high-moment
estimate separate from the increment-to-positive-value bridge. -/
theorem weightedBadDegree_of_weightedProp3_for_incrementGeometry
    (h : WeightedHarperProp3Certificate) :
    mu (weightedProp3BadDegreeEvent h)ᶜ ≤ h.fail :=
  prob_weightedProp3BadDegreeEvent_compl_le h

/-- Named placeholder interface for the remaining one-sided recovery step.
Large increment exceedances do not by themselves imply large positive values;
one must control endpoint offsets or prove a signed increment selector. -/
structure IncrementToPositiveValueBridge where
  description : Prop

end Problem1144
end Erdos
