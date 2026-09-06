import Erdos.Problem1144.PositiveBlockCertificate

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-!
# Certificate-first Brownian block interface

This file is an off-path formalization layer for the Brownian-increment route.
It deliberately does not try to formalize Harper's argument linearly.  Instead
it records the finite certificates that the analytic work must eventually
prove:

* a conditional covariance matrix is close to `sigma2 * I` in a row-sum sense;
* a Gaussian/Rademacher replacement transfers the block crossing event to a
  Gaussian model, with explicit errors;
* a Gaussian crossing theorem bounds the Gaussian failure probability.

The theorem at the bottom is the checked downstream bridge from those
certificates to `PositiveBlockOmega`, hence to Erdős #1144 through the existing
spine.
-/

/-- Partial sums of a finite increment family inside one block. -/
noncomputable def brownianPartialSum
    (Z : ℕ → ℕ → Omega → ℝ) (j m : ℕ) (omega : Omega) : ℝ :=
  Finset.sum (Finset.Icc 1 m) fun r => Z j r omega

/-- The finite block crossing success event for an increment family. -/
def brownianCrossingSuccess
    (Z : ℕ → ℕ → Omega → ℝ) (mesh : ℕ → ℕ)
    (threshold : ℕ → ℝ) (omega : Omega) (j : ℕ) : Prop :=
  ∃ m ∈ Finset.Icc 1 (mesh j),
    threshold j ≤ brownianPartialSum Z j m omega

/-- Failure of the finite Brownian crossing event. -/
def brownianCrossingFailure
    (Z : ℕ → ℕ → Omega → ℝ) (mesh : ℕ → ℕ)
    (threshold : ℕ → ℝ) (j : ℕ) : Set Omega :=
  {omega | ¬ brownianCrossingSuccess Z mesh threshold omega j}

/-- A row-sum covariance certificate for a finite increment vector.

This is the matrix output we want from the number theory: diagonal entries are
close to `sigma2`, and each off-diagonal row has small total mass.  Gershgorin
then gives the corresponding operator control downstream, without reopening
the multiplicative-function proof. -/
structure GoodCovMatrix
    (M : ℕ) (sigma2 delta : ℝ) (Sigma : ℕ → ℕ → ℝ) : Prop where
  diag :
    ∀ r, r ∈ Finset.Icc 1 M →
      |Sigma r r - sigma2| ≤ delta * sigma2
  row :
    ∀ r, r ∈ Finset.Icc 1 M →
      Finset.sum ((Finset.Icc 1 M).erase r) (fun s => |Sigma r s|) ≤
        delta * sigma2

/-- The good-covariance event for block `j`. -/
def goodCovEvent
    (mesh : ℕ → ℕ) (sigma2 delta : ℕ → ℝ)
    (Sigma : ℕ → Omega → ℕ → ℕ → ℝ) (j : ℕ) : Set Omega :=
  {omega | GoodCovMatrix (mesh j) (sigma2 j) (delta j) (Sigma j omega)}

/-- The conditional covariance certificate.

The analytic target is to prove that the small-prime environment lands in
`goodCovEvent` except for a summable error. -/
structure BrownianCovarianceCertificate where
  mesh : ℕ → ℕ
  sigma2 : ℕ → ℝ
  delta : ℕ → ℝ
  Sigma : ℕ → Omega → ℕ → ℕ → ℝ
  errCov : ℕ → ℝ≥0∞
  prob_bad_cov :
    ∀ j, mu (goodCovEvent mesh sigma2 delta Sigma j)ᶜ ≤ errCov j

/-- Gaussian/Rademacher replacement certificate for the block crossing event.

This is where Perron truncation, cutoff errors, and finite-dimensional
Rademacher-to-Gaussian comparison are paid.  The Gaussian failure probability
is left as a finite number `gaussianFail j`, to be bounded by the crossing
certificate below. -/
structure BrownianGaussianReplacementCertificate
    (Z : ℕ → ℕ → Omega → ℝ) (mesh : ℕ → ℕ)
    (threshold : ℕ → ℝ) (good : ℕ → Set Omega) where
  gaussianFail : ℕ → ℝ≥0∞
  errPerron : ℕ → ℝ≥0∞
  errGauss : ℕ → ℝ≥0∞
  errCut : ℕ → ℝ≥0∞
  prob_crossing_failure_on_good :
    ∀ j,
      mu (good j ∩ brownianCrossingFailure Z mesh threshold j) ≤
        gaussianFail j + errPerron j + errGauss j + errCut j

/-- Gaussian crossing certificate.

The intended paper proof supplies the terms `etaTerm`, `meshTerm`, and
`perturbTerm`, corresponding to `C eta`, `C M^{-1/2}`, and the covariance
perturbation error. -/
structure BrownianGaussianCrossingCertificate
    (gaussianFail : ℕ → ℝ≥0∞) where
  etaTerm : ℕ → ℝ≥0∞
  meshTerm : ℕ → ℝ≥0∞
  perturbTerm : ℕ → ℝ≥0∞
  gaussian_failure_bound :
    ∀ j,
      gaussianFail j ≤ etaTerm j + meshTerm j + perturbTerm j

/-- The explicit error budget produced by covariance, replacement, and
Gaussian crossing certificates. -/
noncomputable def brownianAnalyticBudget
    (errCov etaTerm meshTerm perturbTerm errPerron errGauss errCut :
      ℕ → ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  errCov j +
    (etaTerm j + meshTerm j + perturbTerm j +
      errPerron j + errGauss j + errCut j)

/-- Full finite Brownian block certificate.

The field `crossing_implies_block` is the deterministic bridge from an
increment crossing to a positive normalized value at an endpoint in the block.
All number theory and Gaussian comparison is confined to the three certificate
fields. -/
structure BrownianBlockCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  endpoint : ℕ → ℕ → ℕ
  level : ℕ → ℝ
  threshold : ℕ → ℝ
  Z : ℕ → ℕ → Omega → ℝ
  cov : BrownianCovarianceCertificate
  replace :
    BrownianGaussianReplacementCertificate Z cov.mesh threshold
      (goodCovEvent cov.mesh cov.sigma2 cov.delta cov.Sigma)
  cross :
    BrownianGaussianCrossingCertificate replace.gaussianFail
  fail : ℕ → ℝ≥0∞
  endpoint_in_block :
    ∀ j m, m ∈ Finset.Icc 1 (cov.mesh j) →
      endpoint j m ∈ Finset.Icc (lo j) (hi j)
  crossing_implies_block :
    ∀ j omega m,
      m ∈ Finset.Icc 1 (cov.mesh j) →
      threshold j ≤ brownianPartialSum Z j m omega →
        level j ≤ normSum omega (endpoint j m)
  lo_tendsto_atTop : Tendsto lo atTop atTop
  level_tendsto_atTop : Tendsto level atTop atTop
  fail_bound :
    ∀ j,
      brownianAnalyticBudget
        cov.errCov cross.etaTerm cross.meshTerm cross.perturbTerm
        replace.errPerron replace.errGauss replace.errCut j ≤ fail j
  fail_summable : (∑' j, fail j) ≠ ⊤

private theorem blockFailure_subset_cov_or_crossingFailure
    (h : BrownianBlockCertificate) (j : ℕ) :
    blockFailure h.lo h.hi h.level j ⊆
      (goodCovEvent h.cov.mesh h.cov.sigma2 h.cov.delta h.cov.Sigma j)ᶜ ∪
        ((goodCovEvent h.cov.mesh h.cov.sigma2 h.cov.delta h.cov.Sigma j) ∩
          brownianCrossingFailure h.Z h.cov.mesh h.threshold j) := by
  intro omega hfail
  by_cases hgood :
      omega ∈ goodCovEvent h.cov.mesh h.cov.sigma2 h.cov.delta h.cov.Sigma j
  · right
    refine ⟨hgood, ?_⟩
    intro hcross
    rcases hcross with ⟨m, hm, hthreshold⟩
    have hblock : blockSuccess h.lo h.hi h.level omega j :=
      ⟨h.endpoint j m, h.endpoint_in_block j m hm,
        h.crossing_implies_block j omega m hm hthreshold⟩
    exact hfail hblock
  · left
    exact hgood

private theorem crossing_failure_on_good_le_budget
    (h : BrownianBlockCertificate) (j : ℕ) :
    mu
        (goodCovEvent h.cov.mesh h.cov.sigma2 h.cov.delta h.cov.Sigma j ∩
          brownianCrossingFailure h.Z h.cov.mesh h.threshold j) ≤
      h.cross.etaTerm j + h.cross.meshTerm j + h.cross.perturbTerm j +
        h.replace.errPerron j + h.replace.errGauss j + h.replace.errCut j := by
  calc
    mu
        (goodCovEvent h.cov.mesh h.cov.sigma2 h.cov.delta h.cov.Sigma j ∩
          brownianCrossingFailure h.Z h.cov.mesh h.threshold j)
        ≤
          h.replace.gaussianFail j +
            h.replace.errPerron j + h.replace.errGauss j + h.replace.errCut j :=
            h.replace.prob_crossing_failure_on_good j
    _ ≤
        (h.cross.etaTerm j + h.cross.meshTerm j + h.cross.perturbTerm j) +
          h.replace.errPerron j + h.replace.errGauss j + h.replace.errCut j := by
          have hle := add_le_add_right
            (add_le_add_right
              (add_le_add_right (h.cross.gaussian_failure_bound j)
                (h.replace.errPerron j))
              (h.replace.errGauss j))
            (h.replace.errCut j)
          simpa [add_assoc, add_comm, add_left_comm] using hle
    _ =
        h.cross.etaTerm j + h.cross.meshTerm j + h.cross.perturbTerm j +
          h.replace.errPerron j + h.replace.errGauss j + h.replace.errCut j := by
          ac_rfl

/-- Brownian block certificates imply the positive-block omega certificate. -/
noncomputable def positiveBlockOmega_of_brownianBlockCertificate
    (h : BrownianBlockCertificate) :
    PositiveBlockOmega where
  X := h.lo
  Y := h.hi
  M := h.level
  fail := h.fail
  X_tendsto := h.lo_tendsto_atTop
  M_tendsto := h.level_tendsto_atTop
  fail_summable := h.fail_summable
  prob_fail := by
    intro j
    let good :=
      goodCovEvent h.cov.mesh h.cov.sigma2 h.cov.delta h.cov.Sigma j
    let crossFail :=
      brownianCrossingFailure h.Z h.cov.mesh h.threshold j
    calc
      mu (blockFailure h.lo h.hi h.level j)
          ≤ mu (goodᶜ ∪ (good ∩ crossFail)) := by
            exact measure_mono
              (blockFailure_subset_cov_or_crossingFailure h j)
      _ ≤ mu goodᶜ + mu (good ∩ crossFail) :=
            measure_union_le _ _
      _ ≤
          h.cov.errCov j +
            (h.cross.etaTerm j + h.cross.meshTerm j +
              h.cross.perturbTerm j + h.replace.errPerron j +
                h.replace.errGauss j + h.replace.errCut j) := by
            exact add_le_add
              (h.cov.prob_bad_cov j)
              (crossing_failure_on_good_le_budget h j)
      _ =
          brownianAnalyticBudget
            h.cov.errCov h.cross.etaTerm h.cross.meshTerm
            h.cross.perturbTerm h.replace.errPerron h.replace.errGauss
            h.replace.errCut j := by
            rfl
      _ ≤ h.fail j := h.fail_bound j

/-- Direct closure from the finite Brownian block certificate. -/
theorem erdos1144_of_brownianBlockCertificate
    (h : BrownianBlockCertificate) :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    (positiveBlockOmega_of_brownianBlockCertificate h)

end Problem1144
end Erdos
