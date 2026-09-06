import Erdos.Problem1144.HarperCandidateGaussianSlepianIBP
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Finite-coordinate Gaussian integration by parts

The coordinate-splitting strategy was checked against Weihan Zhang's
`UnrestrictedGaussian/GaussianIBPFinite.lean`, commit
`3b9ffe3a46a55cbd49cd11d6aecbf0c20cdaaba3` of
https://github.com/WeihanZhang2001/cubic-root-gaussian-approximation-under-unrestricted-covariance.
The proof below uses this project's bounded scalar identity directly and
imports no donor declarations. No project-wide donor license was present at
that revision; the mathematical strategy is recorded for attribution.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-- Independent standard real Gaussian coordinates. -/
noncomputable abbrev candidatePiGaussian (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

/-- A single coordinate of a finite standard Gaussian vector is integrable. -/
theorem candidate_integrable_gaussian_coordinate {n : ℕ} (i : Fin n) :
    Integrable (fun x : Fin n → ℝ => x i) (candidatePiGaussian n) := by
  exact (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).integrable_comp_of_integrable
      ((memLp_id_gaussianReal (μ := 0) (v := 1) (1 : NNReal)).integrable (by norm_num))

/-- Integrability of a bounded measurable test under the finite Gaussian law. -/
theorem candidate_integrable_piGaussian_of_bounded {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) : Integrable f (candidatePiGaussian n) := by
  exact Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)

/-- A bounded measurable multiplier preserves Gaussian coordinate integrability. -/
theorem candidate_integrable_gaussian_coordinate_mul {n : ℕ} (i : Fin n)
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x => x i * f x) (candidatePiGaussian n) :=
  (candidate_integrable_gaussian_coordinate i).mul_bdd
    hf.aestronglyMeasurable (ae_of_all _ hC)

/-- A coordinate derivative, expressed using the exact finite-product split. -/
def CandidateHasCoordinateDeriv {n : ℕ} (i : Fin (n + 1))
    (f df : (Fin (n + 1) → ℝ) → ℝ) : Prop :=
  ∀ t (y : Fin n → ℝ), HasDerivAt
    (fun s => f ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) i).symm (s, y)))
    (df ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) i).symm (t, y))) t

/-- Actual integration by parts in any coordinate of a finite Gaussian vector.
All integrability follows from the displayed uniform bounds. -/
theorem candidate_piGaussian_integration_by_parts {n : ℕ} (i : Fin (n + 1))
    {f df : (Fin (n + 1) → ℝ) → ℝ}
    (hd : CandidateHasCoordinateDeriv i f df)
    (hf : Measurable f) (hdf : Measurable df) {B C : ℝ}
    (hB : ∀ x, ‖f x‖ ≤ B) (hC : ∀ x, ‖df x‖ ≤ C) :
    (∫ x, x i * f x ∂candidatePiGaussian (n + 1)) =
      ∫ x, df x ∂candidatePiGaussian (n + 1) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have he : MeasurePreserving e (candidatePiGaussian (n + 1))
      ((gaussianReal 0 1).prod (candidatePiGaussian n)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) i
  have hi := candidate_integrable_gaussian_coordinate_mul i hf hB
  have hdi := candidate_integrable_piGaussian_of_bounded hdf hC
  have his := he.symm.integrable_comp_of_integrable hi
  have hdis := he.symm.integrable_comp_of_integrable hdi
  simp only [Function.comp_def] at his hdis
  rw [← he.symm.integral_comp' (fun x => x i * f x),
    ← he.symm.integral_comp' df]
  rw [integral_prod_symm _ his, integral_prod_symm _ hdis]
  apply integral_congr_ae
  filter_upwards [] with y
  have hm : Measurable (fun t : ℝ => df (e.symm (t, y))) :=
    hdf.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
  have h := candidate_standardGaussian_integration_by_parts
    (fun t => hd t y) hm
    (fun t => show |f (e.symm (t, y))| ≤ B from hB _)
    (fun t => show |df (e.symm (t, y))| ≤ C from hC _)
  simpa [e] using h

/-- Conditional coordinate integration by parts with an arbitrary independent
parameter. The bounds may depend on that parameter. -/
theorem candidate_piGaussian_prod_integration_by_parts {n : ℕ}
    (i : Fin (n + 1)) {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [SFinite ν]
    {f df : (Fin (n + 1) → ℝ) × Ω → ℝ}
    (hd : ∀ y, CandidateHasCoordinateDeriv i (fun x => f (x, y))
      (fun x => df (x, y)))
    (hf : Measurable f) (hdf : Measurable df) {B C : Ω → ℝ}
    (hB : ∀ x y, ‖f (x, y)‖ ≤ B y) (hC : ∀ x y, ‖df (x, y)‖ ≤ C y)
    (hi : Integrable (fun z => z.1 i * f z) ((candidatePiGaussian (n + 1)).prod ν))
    (hdi : Integrable df ((candidatePiGaussian (n + 1)).prod ν)) :
    (∫ z, z.1 i * f z ∂((candidatePiGaussian (n + 1)).prod ν)) =
      ∫ z, df z ∂((candidatePiGaussian (n + 1)).prod ν) := by
  rw [integral_prod_symm _ hi, integral_prod_symm _ hdi]
  apply integral_congr_ae
  filter_upwards [] with y
  exact candidate_piGaussian_integration_by_parts i (hd y)
    (hf.comp (measurable_id.prodMk measurable_const))
    (hdf.comp (measurable_id.prodMk measurable_const)) (fun x => hB x y) (fun x => hC x y)

end Erdos.Problem1144
