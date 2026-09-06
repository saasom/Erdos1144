import Erdos.Problem1144.HarperCandidateGaussianSlepian
import Erdos.Problem1144.HarperCandidateGaussianLowerTail
import Erdos.Problem1144.HarperGaussianBallotLower

open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators Topology MatrixOrder

namespace Erdos.Problem1144

noncomputable section

/-- Exact lower-box probability for independent standard Gaussian coordinates. -/
theorem candidate_iidGaussian_box_probability (m : ℕ) (K : ℝ) :
    (candidatePiGaussian m).real {z | ∀ i, z i ≤ K} =
      ((gaussianReal 0 1).real (Iic K)) ^ m := by
  have he : {z : Fin m → ℝ | ∀ i, z i ≤ K} = Set.pi Set.univ (fun _ => Iic K) := by
    ext z
    simp only [mem_setOf_eq, mem_pi, mem_univ, true_implies, mem_Iic]
  rw [he, Measure.real, Measure.pi_pi]
  simp [ENNReal.toReal_prod, Measure.real]

/-- Exact upper-maximum probability for independent standard Gaussians. -/
theorem candidate_iidGaussian_max_probability (m : ℕ) (K : ℝ) :
    (candidatePiGaussian m).real {z | ∃ i, K < z i} =
      1 - ((gaussianReal 0 1).real (Iic K)) ^ m := by
  have hs : MeasurableSet {z : Fin m → ℝ | ∀ i, z i ≤ K} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i) measurable_const
  have he : {z : Fin m → ℝ | ∃ i, K < z i} = {z | ∀ i, z i ≤ K}ᶜ := by ext z; simp
  rw [he, measureReal_compl hs, probReal_univ, candidate_iidGaussian_box_probability]

/-- A nonnegative common Gaussian leaves half the independent crossing
probability. This is a literal product-law lower bound with no conditioning
or Gaussian-comparison premise. -/
theorem candidate_commonGaussian_max_lower (m : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℝ) :
    (1 / 2 : ℝ) * (1 - ((gaussianReal 0 1).real (Iic (K / Real.sqrt (1 - r)))) ^ m) ≤
      ((gaussianReal 0 1).prod (candidatePiGaussian m)).real
        {z | ∃ i, K < Real.sqrt r * z.1 + Real.sqrt (1 - r) * z.2 i} := by
  have hs : 0 < Real.sqrt (1 - r) := Real.sqrt_pos.mpr (by linarith)
  have hi : (Ioi (0 : ℝ)) ×ˢ {z : Fin m → ℝ | ∃ i, K / Real.sqrt (1 - r) < z i} ⊆
      {z : ℝ × (Fin m → ℝ) | ∃ i, K < Real.sqrt r * z.1 + Real.sqrt (1 - r) * z.2 i} := by
    rintro ⟨g, z⟩ ⟨hg, i, hi⟩
    have h := (div_lt_iff₀ hs).mp hi
    have hc := mul_nonneg (Real.sqrt_nonneg r) (le_of_lt hg)
    exact ⟨i, by nlinarith⟩
  have h := measureReal_mono (μ := (gaussianReal 0 1).prod (candidatePiGaussian m)) hi
  rw [measureReal_prod_prod, gaussianReal_zero_real_Ioi_zero_eq_half (by norm_num),
    candidate_iidGaussian_max_probability] at h
  exact h

/-- Unit-variance equicorrelation covariance. -/
def candidateEquicorrelation (m : ℕ) (r : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => r + if i = j then 1 - r else 0

/-- One common normal and one independent normal per coordinate. -/
def candidateEquicorrelationCoefficients (m : ℕ) (r : ℝ) : Matrix (Fin m) (Fin (m + 1)) ℝ :=
  fun i => Fin.cases (Real.sqrt r) (fun j => if i = j then Real.sqrt (1 - r) else 0)

/-- The common-noise realization has exactly the displayed equicorrelation
matrix, including correlation zero. -/
theorem candidate_equicorrelation_gram (m : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    candidateEquicorrelationCoefficients m r * (candidateEquicorrelationCoefficients m r)ᴴ =
      candidateEquicorrelation m r := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
    candidateEquicorrelationCoefficients, candidateEquicorrelation, ite_mul, mul_ite,
    ← pow_two, Real.sq_sqrt hr0, Real.sq_sqrt (sub_nonneg.mpr hr1)]

/-- Positive semidefiniteness comes from the explicit independent-noise Gram
representation. -/
theorem candidate_equicorrelation_posSemidef (m : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (candidateEquicorrelation m r).PosSemidef := by
  rw [← candidate_equicorrelation_gram m hr0 hr1]
  exact posSemidef_self_mul_conjTranspose _

/-- Exact common-noise realization of the canonical equicorrelation law. -/
theorem candidate_measurePreserving_commonGaussian (m : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    MeasurePreserving
      (fun z : ℝ × (Fin m → ℝ) => WithLp.toLp 2
        (fun i => Real.sqrt r * z.1 + Real.sqrt (1 - r) * z.2 i))
      ((gaussianReal 0 1).prod (candidatePiGaussian m))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (candidateEquicorrelation m r)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have he : MeasurePreserving e (candidatePiGaussian (m + 1))
      ((gaussianReal 0 1).prod (candidatePiGaussian m)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => gaussianReal 0 1) 0
  have h := (candidate_measurePreserving_pi_gaussian_linear
    (candidateEquicorrelationCoefficients m r)).comp he.symm
  rw [candidate_equicorrelation_gram m hr0 hr1] at h
  convert h using 1
  funext z
  ext i
  simp [e, candidateEquicorrelationCoefficients, Fin.sum_univ_succ,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Function.comp_def]

/-- Explicit maximum lower bound for an equicorrelated Gaussian vector. -/
theorem candidate_equicorrelatedGaussian_max_lower (m : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℝ) :
    (1 / 2 : ℝ) * (1 - ((gaussianReal 0 1).real (Iic (K / Real.sqrt (1 - r)))) ^ m) ≤
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (candidateEquicorrelation m r)).real {z | ∃ i, K < z i} := by
  have hset : MeasurableSet {z : EuclideanSpace ℝ (Fin m) | ∃ i, K < z i} := by
    simp only [setOf_exists]
    exact MeasurableSet.iUnion fun i => measurableSet_lt measurable_const (by fun_prop)
  have h := (candidate_measurePreserving_commonGaussian m hr0 hr1.le).measureReal_preimage
    hset.nullMeasurableSet
  rw [← h]
  exact candidate_commonGaussian_max_lower m hr0 hr1 K

/-- Explicit lower bound for every unit-variance Gaussian vector whose
pairwise correlations are at most `r < 1`. This is the finite Gaussian input
needed after selecting a set with small correlations. -/
theorem candidate_unitGaussian_max_lower {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef)
    (hdiag : ∀ i, A i i = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hcov : ∀ i j, i ≠ j → A i j ≤ r) (K : ℝ) :
    (1 / 2 : ℝ) * (1 - ((gaussianReal 0 1).real (Iic (K / Real.sqrt (1 - r)))) ^ m) ≤
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) A).real {z | ∃ i, K < z i} := by
  refine (candidate_equicorrelatedGaussian_max_lower m hr0 hr1 K).trans ?_
  apply candidate_gaussianSlepian_max A (candidateEquicorrelation m r) hA
    (candidate_equicorrelation_posSemidef m hr0 hr1.le)
  · intro i
    simp [candidateEquicorrelation, hdiag]
  · intro i j hij
    simpa [candidateEquicorrelation, hij] using hcov i j hij

/-- A fully explicit exponential form of the Gaussian maximum lower bound. -/
theorem candidate_unitGaussian_max_lower_exp {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef)
    (hdiag : ∀ i, A i i = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hcov : ∀ i j, i ≠ j → A i j ≤ r) {K : ℝ} (hK : 0 ≤ K) :
    (1 / 2 : ℝ) * (1 - Real.exp (-(m : ℝ) *
      gaussianPDFReal 0 1 (K / Real.sqrt (1 - r) + 1))) ≤
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) A).real {z | ∃ i, K < z i} := by
  have h := candidate_gaussianReal_Iic_pow_le_exp (K / Real.sqrt (1 - r))
    (div_nonneg hK (Real.sqrt_nonneg _)) m
  refine (mul_le_mul_of_nonneg_left (sub_le_sub_left h 1) (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans ?_
  exact candidate_unitGaussian_max_lower A hA hdiag hr0 hr1 hcov K

/-- A concrete deterministic size criterion yields a universal positive
maximum-crossing probability. -/
theorem candidate_unitGaussian_max_ge_quarter {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef)
    (hdiag : ∀ i, A i i = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hcov : ∀ i j, i ≠ j → A i j ≤ r) {K : ℝ} (hK : 0 ≤ K)
    (hsize : Real.log 2 ≤ (m : ℝ) * gaussianPDFReal 0 1 (K / Real.sqrt (1 - r) + 1)) :
    (1 / 4 : ℝ) ≤
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) A).real {z | ∃ i, K < z i} := by
  have hexp : Real.exp (-(m : ℝ) * gaussianPDFReal 0 1 (K / Real.sqrt (1 - r) + 1)) ≤
      (1 / 2 : ℝ) := by
    calc
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have h := candidate_unitGaussian_max_lower_exp A hA hdiag hr0 hr1 hcov hK
  linarith

/-- Correlations at most one half admit a fixed scalar density criterion,
independent of their precise value. -/
theorem candidate_unitGaussian_max_ge_quarter_of_half_correlation {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef)
    (hdiag : ∀ i, A i i = 1) {r : ℝ} (hr0 : 0 ≤ r) (hrhalf : r ≤ 1 / 2)
    (hcov : ∀ i j, i ≠ j → A i j ≤ r) {K : ℝ} (hK : 0 ≤ K)
    (hsize : Real.log 2 ≤ (m : ℝ) * gaussianPDFReal 0 1 (Real.sqrt 2 * K + 1)) :
    (1 / 4 : ℝ) ≤
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) A).real {z | ∃ i, K < z i} := by
  have hr1 : r < 1 := by linarith
  have hs : 0 < Real.sqrt (1 - r) := Real.sqrt_pos.mpr (by linarith)
  have hroot : 1 ≤ Real.sqrt 2 * Real.sqrt (1 - r) := by
    calc
      1 = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (2 * (1 - r)) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _
  have hq : K / Real.sqrt (1 - r) ≤ Real.sqrt 2 * K := by
    apply (div_le_iff₀ hs).mpr
    have h := mul_le_mul_of_nonneg_left hroot hK
    nlinarith
  apply candidate_unitGaussian_max_ge_quarter A hA hdiag hr0 hr1 hcov hK
  refine hsize.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  exact candidate_gaussianPDFReal_antitone_nonneg
    (by positivity : 0 ≤ K / Real.sqrt (1 - r) + 1) (by linarith)

end

end Erdos.Problem1144
