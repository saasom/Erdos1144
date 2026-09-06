import Erdos.Problem1144.HarperBrownianBlock
import Mathlib.Data.Real.Sqrt

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-!
# Short-memory covariance certificate

This file records the finite covariance extraction suggested by the Track B
route.  The analytic proof first cuts away the part of a squarefree increment
whose small-prime component is too large.  After conditioning on those small
primes, the retained coefficients have short memory: intervals separated by
at least one full block cannot share the same fresh-prime component.

The purpose here is deliberately narrow:

* define the sharp coefficient covariance matrix;
* prove the exact finite implication from coefficient disjointness to zero
  covariance;
* prove the boundary-energy Cauchy--Schwarz estimate;
* package the remaining diagonal lower and boundary upper energy estimates as
  explicit analytic inputs.

No final theorem wiring is changed by this file.
-/

/-- Abstract normalized coefficient attached to a rough fresh component `b`.

In the paper notation this stands for `A_r(b) / sqrt b`; keeping the `1/sqrt b`
inside the coefficient makes the finite covariance and energy formulas cleaner.
-/
abbrev ShortMemoryCoeff := ℕ → ℕ → Omega → ℕ → ℝ

/-- Finite sharp covariance matrix for the retained short-memory coefficients. -/
noncomputable def shortMemorySharpCovariance
    (bSet : ℕ → Finset ℕ) (coeff : ShortMemoryCoeff)
    (j : ℕ) (omega : Omega) (r s : ℕ) : ℝ :=
  ∑ b ∈ bSet j, coeff j r omega b * coeff j s omega b

/-- Energy of one row of coefficients over a chosen finite set of fresh
components. -/
noncomputable def shortMemoryEnergyOn
    (S : Finset ℕ) (coeff : ShortMemoryCoeff)
    (j r : ℕ) (omega : Omega) : ℝ :=
  ∑ b ∈ S, (coeff j r omega b) ^ 2

/-- Covariance restricted to a chosen finite set of fresh components. -/
noncomputable def shortMemoryCovarianceOn
    (S : Finset ℕ) (coeff : ShortMemoryCoeff)
    (j : ℕ) (omega : Omega) (r s : ℕ) : ℝ :=
  ∑ b ∈ S, coeff j r omega b * coeff j s omega b

/-- Finite Cauchy--Schwarz for the covariance restricted to a finite fresh set. -/
theorem abs_shortMemoryCovarianceOn_le_sqrt_energy
    (S : Finset ℕ) (coeff : ShortMemoryCoeff)
    (j : ℕ) (omega : Omega) (r s : ℕ) :
    |shortMemoryCovarianceOn S coeff j omega r s| ≤
      Real.sqrt (shortMemoryEnergyOn S coeff j r omega) *
        Real.sqrt (shortMemoryEnergyOn S coeff j s omega) := by
  unfold shortMemoryCovarianceOn shortMemoryEnergyOn
  calc
    |((∑ b ∈ S, coeff j r omega b * coeff j s omega b) : ℝ)|
        ≤ ∑ b ∈ S, |coeff j r omega b * coeff j s omega b| :=
          Finset.abs_sum_le_sum_abs _ _
    _ =
        ∑ b ∈ S, |coeff j r omega b| * |coeff j s omega b| := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          rw [abs_mul]
    _ ≤
        Real.sqrt (∑ b ∈ S, (|coeff j r omega b|) ^ 2) *
          Real.sqrt (∑ b ∈ S, (|coeff j s omega b|) ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt S
            (fun b => |coeff j r omega b|)
            (fun b => |coeff j s omega b|)
    _ =
        Real.sqrt (∑ b ∈ S, (coeff j r omega b) ^ 2) *
          Real.sqrt (∑ b ∈ S, (coeff j s omega b) ^ 2) := by
          congr 2 <;>
            refine Finset.sum_congr rfl ?_ <;>
              intro b hb <;>
                rw [sq_abs]

/-- Boundary-row Cauchy bound: a covariance row is controlled by the
corresponding row of square-root energies. -/
theorem shortMemoryCovarianceRow_le_sqrtEnergyRow
    (S rowSet : Finset ℕ) (coeff : ShortMemoryCoeff)
    (j : ℕ) (omega : Omega) (r : ℕ) :
    Finset.sum rowSet
        (fun s => |shortMemoryCovarianceOn S coeff j omega r s|) ≤
      Finset.sum rowSet
        (fun s =>
          Real.sqrt (shortMemoryEnergyOn S coeff j r omega) *
            Real.sqrt (shortMemoryEnergyOn S coeff j s omega)) := by
  exact
    Finset.sum_le_sum fun s _hs =>
      abs_shortMemoryCovarianceOn_le_sqrt_energy S coeff j omega r s

/-- The same row Cauchy bound for the sharp covariance with a constant fresh
component set. -/
theorem shortMemorySharpCovarianceRow_le_sqrtEnergyRow
    (S rowSet : Finset ℕ) (coeff : ShortMemoryCoeff)
    (j : ℕ) (omega : Omega) (r : ℕ) :
    Finset.sum rowSet
        (fun s =>
          |shortMemorySharpCovariance (fun _ => S) coeff j omega r s|) ≤
      Finset.sum rowSet
        (fun s =>
          Real.sqrt (shortMemoryEnergyOn S coeff j r omega) *
            Real.sqrt (shortMemoryEnergyOn S coeff j s omega)) := by
  simpa [shortMemorySharpCovariance, shortMemoryCovarianceOn]
    using shortMemoryCovarianceRow_le_sqrtEnergyRow S rowSet coeff j omega r

/-- If every retained fresh component misses at least one of the two rows, the
sharp covariance vanishes. -/
theorem shortMemorySharpCovariance_eq_zero_of_disjoint
    (bSet : ℕ → Finset ℕ) (coeff : ShortMemoryCoeff)
    (j : ℕ) (omega : Omega) (r s : ℕ)
    (hdisj :
      ∀ b, b ∈ bSet j →
        coeff j r omega b = 0 ∨ coeff j s omega b = 0) :
    shortMemorySharpCovariance bSet coeff j omega r s = 0 := by
  unfold shortMemorySharpCovariance
  exact
    Finset.sum_eq_zero fun b hb => by
      rcases hdisj b hb with hzero | hzero
      · simp [hzero]
      · simp [hzero]

/-- Short-memory support condition: rows farther than one block apart have no
common retained fresh component. -/
def ShortMemoryTridiagonalSupport
    (mesh : ℕ → ℕ) (bSet : ℕ → Finset ℕ)
    (coeff : ShortMemoryCoeff) : Prop :=
  ∀ j omega r s b,
    r ∈ Finset.Icc 1 (mesh j) →
    s ∈ Finset.Icc 1 (mesh j) →
    (r + 1 < s ∨ s + 1 < r) →
    b ∈ bSet j →
      coeff j r omega b = 0 ∨ coeff j s omega b = 0

/-- Under the short-memory support condition, all non-neighboring sharp
covariances are exactly zero. -/
theorem shortMemorySharpCovariance_eq_zero_of_tridiagonalSupport
    (mesh : ℕ → ℕ) (bSet : ℕ → Finset ℕ)
    (coeff : ShortMemoryCoeff)
    (htri : ShortMemoryTridiagonalSupport mesh bSet coeff)
    {j r s : ℕ} {omega : Omega}
    (hr : r ∈ Finset.Icc 1 (mesh j))
    (hs : s ∈ Finset.Icc 1 (mesh j))
    (hfar : r + 1 < s ∨ s + 1 < r) :
    shortMemorySharpCovariance bSet coeff j omega r s = 0 :=
  shortMemorySharpCovariance_eq_zero_of_disjoint bSet coeff j omega r s
    fun b hb => htri j omega r s b hr hs hfar hb

/-- The diagonal covariance attached to one coefficient family is nonnegative. -/
theorem shortMemorySharpCovariance_diag_nonneg
    (bSet : ℕ → Finset ℕ) (coeff : ShortMemoryCoeff)
    (j : ℕ) (omega : Omega) (r : ℕ) :
    0 ≤ shortMemorySharpCovariance bSet coeff j omega r r := by
  unfold shortMemorySharpCovariance
  exact Finset.sum_nonneg fun b hb => by
    exact mul_self_nonneg (coeff j r omega b)

/-- Core-plus-boundary covariance matrix.  In the intended application the
core rows have disjoint supports, while the boundary rows are small in row
sum. -/
noncomputable def shortMemoryCoreBoundaryCovariance
    (bSet : ℕ → Finset ℕ) (core boundary : ShortMemoryCoeff)
    (j : ℕ) (omega : Omega) (r s : ℕ) : ℝ :=
  shortMemorySharpCovariance bSet core j omega r s +
    shortMemorySharpCovariance bSet boundary j omega r s

/-- If the pointwise coefficient splits as `core + boundary` and the two cross
covariance terms vanish, then the sharp covariance splits into a core
covariance plus a boundary covariance. -/
theorem shortMemorySharpCovariance_eq_coreBoundary_of_cross_zero
    (bSet : ℕ → Finset ℕ) (coeff core boundary : ShortMemoryCoeff)
    (j : ℕ) (omega : Omega) (r s : ℕ)
    (hcoeff :
      ∀ b, b ∈ bSet j →
        coeff j r omega b = core j r omega b + boundary j r omega b)
    (hcoeff_s :
      ∀ b, b ∈ bSet j →
        coeff j s omega b = core j s omega b + boundary j s omega b)
    (hcross₁ :
      ∀ b, b ∈ bSet j →
        core j r omega b * boundary j s omega b = 0)
    (hcross₂ :
      ∀ b, b ∈ bSet j →
        boundary j r omega b * core j s omega b = 0) :
    shortMemorySharpCovariance bSet coeff j omega r s =
      shortMemoryCoreBoundaryCovariance bSet core boundary j omega r s := by
  simp only [shortMemorySharpCovariance, shortMemoryCoreBoundaryCovariance]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro b hb
  rw [hcoeff b hb, hcoeff_s b hb]
  ring_nf
  all_goals simp [hcross₁ b hb, hcross₂ b hb]

/-- A lower/row-sum covariance target adapted to the short-memory argument.

Unlike `GoodCovMatrix`, this does not require concentration around a fixed
mean variance.  It only asks for a deterministic variance floor and a small
off-diagonal row mass relative to that floor. -/
structure ShortMemoryGoodCovMatrix
    (M : ℕ) (V rho : ℝ) (Sigma : ℕ → ℕ → ℝ) : Prop where
  diag_floor :
    ∀ r, r ∈ Finset.Icc 1 M → V ≤ Sigma r r
  row :
    ∀ r, r ∈ Finset.Icc 1 M →
      Finset.sum ((Finset.Icc 1 M).erase r) (fun s => |Sigma r s|) ≤
        rho * V

/-- Good-covariance event for the short-memory covariance matrix. -/
def shortMemoryGoodCovEvent
    (mesh : ℕ → ℕ) (V rho : ℕ → ℝ)
    (Sigma : ℕ → Omega → ℕ → ℕ → ℝ) (j : ℕ) : Set Omega :=
  {omega | ShortMemoryGoodCovMatrix (mesh j) (V j) (rho j) (Sigma j omega)}

/-- Analytic inputs left after the elementary short-memory geometry.

The fields `sharp_cov_eq`, `diag_lower`, and `row_bound` are the finite form of
the remaining energy estimates:

* diagonal lower energy `D_r >= V`;
* boundary upper energy and Cauchy give the row bound;
* the sharp conditional covariance is represented by the finite coefficient
  formula above.

The Rankin truncation, diagonal lower-tail, and boundary upper-tail estimates
are intended to prove these fields in later analytic modules. -/
structure ShortMemoryCovarianceCertificate where
  mesh : ℕ → ℕ
  bSet : ℕ → Finset ℕ
  coeff : ShortMemoryCoeff
  Sigma : ℕ → Omega → ℕ → ℕ → ℝ
  V : ℕ → ℝ
  rho : ℕ → ℝ
  errCov : ℕ → ℝ≥0∞
  sharp_cov_eq :
    ∀ j omega r s,
      Sigma j omega r s =
        shortMemorySharpCovariance bSet coeff j omega r s
  good_cov :
    ∀ j omega,
      ShortMemoryGoodCovMatrix (mesh j) (V j) (rho j) (Sigma j omega)
  prob_bad_cov :
    ∀ j, mu (shortMemoryGoodCovEvent mesh V rho Sigma j)ᶜ ≤ errCov j

/-- The certificate supplies the short-memory good-covariance event pointwise. -/
theorem ShortMemoryCovarianceCertificate.mem_goodCovEvent
    (h : ShortMemoryCovarianceCertificate)
    {j : ℕ} {omega : Omega} :
    omega ∈ shortMemoryGoodCovEvent h.mesh h.V h.rho h.Sigma j := by
  exact h.good_cov j omega

/-- Deterministic implication from explicit diagonal and row estimates to the
short-memory covariance predicate. -/
theorem shortMemoryGoodCovMatrix_of_diag_and_row
    {M : ℕ} {V rho : ℝ} {Sigma : ℕ → ℕ → ℝ}
    (hdiag : ∀ r, r ∈ Finset.Icc 1 M → V ≤ Sigma r r)
    (hrow :
      ∀ r, r ∈ Finset.Icc 1 M →
        Finset.sum ((Finset.Icc 1 M).erase r) (fun s => |Sigma r s|) ≤
          rho * V) :
    ShortMemoryGoodCovMatrix M V rho Sigma where
  diag_floor := hdiag
  row := hrow

/-- Exact diagonal core plus small boundary row sums imply the short-memory
good-covariance predicate.

This is the finite algebraic heart of the core/boundary extraction: the core
provides the variance floor and has zero off-diagonal covariance; the boundary
is allowed to contribute on and near the diagonal, but its off-diagonal row
mass is small. -/
theorem shortMemoryGoodCovMatrix_of_core_boundary
    (bSet : Finset ℕ) (core boundary : ShortMemoryCoeff)
    {M : ℕ} {V rho : ℝ} {j : ℕ} {omega : Omega}
    {Sigma : ℕ → ℕ → ℝ}
    (hSigma :
      ∀ r s,
        Sigma r s =
          shortMemoryCoreBoundaryCovariance
            (fun _ => bSet) core boundary j omega r s)
    (hcore_diag :
      ∀ r, r ∈ Finset.Icc 1 M →
        V ≤ shortMemorySharpCovariance (fun _ => bSet) core j omega r r)
    (hcore_offdiag :
      ∀ r, r ∈ Finset.Icc 1 M →
        ∀ s, s ∈ Finset.Icc 1 M → s ≠ r →
          shortMemorySharpCovariance (fun _ => bSet) core j omega r s = 0)
    (hboundary_row :
      ∀ r, r ∈ Finset.Icc 1 M →
        Finset.sum ((Finset.Icc 1 M).erase r)
          (fun s =>
            |shortMemorySharpCovariance
              (fun _ => bSet) boundary j omega r s|) ≤
          rho * V) :
    ShortMemoryGoodCovMatrix M V rho Sigma where
  diag_floor := by
    intro r hr
    rw [hSigma r r, shortMemoryCoreBoundaryCovariance]
    exact
      (hcore_diag r hr).trans
        (le_add_of_nonneg_right
          (shortMemorySharpCovariance_diag_nonneg
            (fun _ => bSet) boundary j omega r))
  row := by
    intro r hr
    calc
      Finset.sum ((Finset.Icc 1 M).erase r) (fun s => |Sigma r s|)
          =
          Finset.sum ((Finset.Icc 1 M).erase r)
            (fun s =>
              |shortMemorySharpCovariance
                (fun _ => bSet) boundary j omega r s|) := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            have hsI : s ∈ Finset.Icc 1 M := (Finset.mem_erase.mp hs).2
            have hsne : s ≠ r := (Finset.mem_erase.mp hs).1
            rw [hSigma r s, shortMemoryCoreBoundaryCovariance,
              hcore_offdiag r hr s hsI hsne, zero_add]
      _ ≤ rho * V := hboundary_row r hr

/-- Variant of `shortMemoryGoodCovMatrix_of_core_boundary` where the boundary
input is supplied as a square-root energy row bound. -/
theorem shortMemoryGoodCovMatrix_of_core_boundary_energy_row
    (bSet : Finset ℕ) (core boundary : ShortMemoryCoeff)
    {M : ℕ} {V rho : ℝ} {j : ℕ} {omega : Omega}
    {Sigma : ℕ → ℕ → ℝ}
    (hSigma :
      ∀ r s,
        Sigma r s =
          shortMemoryCoreBoundaryCovariance
            (fun _ => bSet) core boundary j omega r s)
    (hcore_diag :
      ∀ r, r ∈ Finset.Icc 1 M →
        V ≤ shortMemorySharpCovariance (fun _ => bSet) core j omega r r)
    (hcore_offdiag :
      ∀ r, r ∈ Finset.Icc 1 M →
        ∀ s, s ∈ Finset.Icc 1 M → s ≠ r →
          shortMemorySharpCovariance (fun _ => bSet) core j omega r s = 0)
    (hboundary_energy_row :
      ∀ r, r ∈ Finset.Icc 1 M →
        Finset.sum ((Finset.Icc 1 M).erase r)
          (fun s =>
            Real.sqrt (shortMemoryEnergyOn bSet boundary j r omega) *
              Real.sqrt (shortMemoryEnergyOn bSet boundary j s omega)) ≤
          rho * V) :
    ShortMemoryGoodCovMatrix M V rho Sigma :=
  shortMemoryGoodCovMatrix_of_core_boundary bSet core boundary
    hSigma hcore_diag hcore_offdiag
    (fun r hr =>
      (shortMemorySharpCovarianceRow_le_sqrtEnergyRow bSet
        ((Finset.Icc 1 M).erase r) boundary j omega r).trans
        (hboundary_energy_row r hr))

end Problem1144
end Erdos
