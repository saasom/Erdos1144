import Erdos.Problem1144.HarperCandidateGaussianNormalization
import Erdos.Problem1144.HarperCandidateGaussianLowerMaximum
import Erdos.Problem1144.HarperCandidateGaussianThinning
import Erdos.Problem1144.HarperCandidateGaussianRealization
import Mathlib.Data.Finset.Sort

open MeasureTheory ProbabilityTheory Matrix WithLp Set
open scoped BigOperators

namespace Erdos.Problem1144

noncomputable section

local instance candidateSelectedLowerMatrixMeasurableSpace {ι : Type*} :
    MeasurableSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → ι → ℝ))

/-- A variance floor and small absolute covariances give a positive maximum
probability under the literal Gaussian law. The variances need not agree. -/
theorem candidate_gaussian_max_ge_quarter_of_variance_floor {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef)
    {v K : ℝ} (hv : 0 < v) (hK : 0 ≤ K)
    (hdiag : ∀ i, v ≤ A i i)
    (hcov : ∀ i j, i ≠ j → |A i j| ≤ v / 2)
    (hsize : Real.log 2 ≤ (m : ℝ) *
      gaussianPDFReal 0 1 (Real.sqrt 2 * (K / Real.sqrt v) + 1)) :
    (1 / 4 : ℝ) ≤
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) A).real
        {x | ∃ i, K < x i} := by
  let r : Fin m → ℝ := fun i => (Real.sqrt (A i i))⁻¹
  let B := candidateCovarianceDiagonal r A
  have hs (i : Fin m) : 0 < Real.sqrt (A i i) :=
    Real.sqrt_pos.mpr (hv.trans_le (hdiag i))
  have hvroot : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hB : B.PosSemidef := candidateCovarianceDiagonal_posSemidef hA r
  have hBd (i : Fin m) : B i i = 1 := by
    dsimp [B, candidateCovarianceDiagonal, r]
    field_simp [ne_of_gt (hs i)]
    exact (Real.sq_sqrt (hv.le.trans (hdiag i))).symm
  have hBc (i j : Fin m) (hij : i ≠ j) : B i j ≤ (1 / 2 : ℝ) := by
    have hprod : v ≤ Real.sqrt (A i i) * Real.sqrt (A j j) := by
      calc
        v = Real.sqrt v * Real.sqrt v := (Real.mul_self_sqrt hv.le).symm
        _ ≤ _ := mul_le_mul (Real.sqrt_le_sqrt (hdiag i))
          (Real.sqrt_le_sqrt (hdiag j)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hnum := (le_abs_self (A i j)).trans (hcov i j hij)
    have he : B i j = A i j / (Real.sqrt (A i i) * Real.sqrt (A j j)) := by
      dsimp [B, candidateCovarianceDiagonal, r]
      ring
    rw [he, div_le_iff₀ (mul_pos (hs i) (hs j))]
    linarith
  have h := candidate_unitGaussian_max_ge_quarter_of_half_correlation B hB hBd
    (by norm_num : (0 : ℝ) ≤ 1 / 2) le_rfl hBc
    (div_nonneg hK hvroot.le) hsize
  have hm : MeasurableSet {x : EuclideanSpace ℝ (Fin m) |
      ∃ i, K / Real.sqrt v < x i} := by
    simp only [setOf_exists]
    exact MeasurableSet.iUnion fun i => measurableSet_lt measurable_const (by fun_prop)
  rw [← (candidate_measurePreserving_gaussian_diagonal hA r).measureReal_preimage
    hm.nullMeasurableSet] at h
  refine h.trans (measureReal_mono ?_)
  rintro x ⟨i, hi⟩
  refine ⟨i, ?_⟩
  change K / Real.sqrt v < (Real.sqrt (A i i))⁻¹ * x i at hi
  have hq : K / Real.sqrt (A i i) ≤ K / Real.sqrt v :=
    div_le_div_of_nonneg_left hK hvroot (Real.sqrt_le_sqrt (hdiag i))
  have hi' : K / Real.sqrt (A i i) < x i / Real.sqrt (A i i) := by
    simpa only [div_eq_mul_inv, mul_comm] using hq.trans_lt hi
  exact (div_lt_div_iff_of_pos_right (hs i)).mp hi'

/-- The literal retained-set bad-degree estimate suffices for a Gaussian
crossing probability of one quarter. The thinner set is chosen only inside
this pointwise proof, so no measurable choice of a thinner is required. -/
theorem candidate_gaussian_selected_max_ge_quarter_of_bad_degree {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosSemidef)
    (s : Finset (Fin N)) (d : ℕ) {v K : ℝ} (hv : 0 < v) (hK : 0 ≤ K)
    (hdiag : ∀ i ∈ s, v ≤ A i i)
    (hdegree : ∀ i ∈ s, (s.filter fun j => j ≠ i ∧ v / 2 < |A i j|).card ≤ d)
    (hsize : Real.log 2 ≤ ((s.card : ℝ) / (d + 1)) *
      gaussianPDFReal 0 1 (Real.sqrt 2 * (K / Real.sqrt v) + 1)) :
    (1 / 4 : ℝ) ≤
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin N)) A).real
        {x | ∃ i ∈ s, K < x i} := by
  classical
  obtain ⟨J, hJs, hpair, hcard⟩ :=
    candidate_exists_large_weakly_correlated_subset s A
      (fun i j => by simpa using (hA.isHermitian.apply j i)) (v / 2) d
      (fun i hi => by
        convert hdegree i hi using 1
        congr 1
        ext j
        simp)
  let e := J.orderEmbOfFin rfl
  have he (i : Fin J.card) : e i ∈ J := J.orderEmbOfFin_mem rfl i
  have hc : (s.card : ℝ) / (d + 1) ≤ (J.card : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < d + 1)).mpr
    exact_mod_cast (by simpa [Nat.mul_comm] using hcard)
  have hsz : Real.log 2 ≤ (J.card : ℝ) *
      gaussianPDFReal 0 1 (Real.sqrt 2 * (K / Real.sqrt v) + 1) :=
    hsize.trans (mul_le_mul_of_nonneg_right hc (gaussianPDFReal_nonneg _ _ _))
  have h := candidate_gaussian_max_ge_quarter_of_variance_floor
    (A.submatrix e e) (hA.submatrix e) hv hK
    (fun i => hdiag (e i) (hJs (he i)))
    (fun i j hij => hpair (he i) (he j) (e.injective.ne hij)) hsz
  have hm : MeasurableSet {x : EuclideanSpace ℝ (Fin J.card) | ∃ i, K < x i} := by
    simp only [setOf_exists]
    exact MeasurableSet.iUnion fun i => measurableSet_lt measurable_const (by fun_prop)
  rw [← (candidate_measurePreserving_gaussian_coordinates hA e).measureReal_preimage
    hm.nullMeasurableSet] at h
  refine h.trans (measureReal_mono ?_)
  rintro x ⟨i, hi⟩
  exact ⟨e i, hJs (he i), hi⟩

/-- A retained geometry event of mass `q` yields averaged absolute Gaussian
crossing mass at least `q/4`, under any probability law including a fixed
prime cylinder. The Gaussian probabilities are integrable by construction. -/
theorem candidate_integral_gaussian_selected_ge_quarter_of_bad_degree
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (A : Ω → Matrix (Fin N) (Fin N) ℝ) (hA : Measurable A)
    (hpos : ∀ ω, (A ω).PosSemidef)
    (s : Ω → Finset (Fin N)) (hs : ∀ i, MeasurableSet {ω | i ∈ s ω})
    (G : Set Ω) (hG : MeasurableSet G) (d : Ω → ℕ) (v : Ω → ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hv : ∀ ω ∈ G, 0 < v ω)
    (hdiag : ∀ ω ∈ G, ∀ i ∈ s ω, v ω ≤ A ω i i)
    (hdegree : ∀ ω ∈ G, ∀ i ∈ s ω,
      ((s ω).filter fun j => j ≠ i ∧ v ω / 2 < |A ω i j|).card ≤ d ω)
    (hsize : ∀ ω ∈ G, Real.log 2 ≤ ((s ω).card : ℝ) / (d ω + 1) *
      gaussianPDFReal 0 1 (Real.sqrt 2 * (K / Real.sqrt (v ω)) + 1)) :
    Q.real G / 4 ≤ ∫ ω,
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin N)) (A ω)).real
        {x | ∃ i ∈ s ω, K < |x i|} ∂Q := by
  have hi := candidate_integrable_gaussian_selected_probability Q hA hpos s hs K
  have hbound : ∀ ω, G.indicator (fun _ => (1 / 4 : ℝ)) ω ≤
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin N)) (A ω)).real
        {x | ∃ i ∈ s ω, K < |x i|} := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [indicator_of_mem hω]
      have h := candidate_gaussian_selected_max_ge_quarter_of_bad_degree
        (A ω) (hpos ω) (s ω) (d ω) (hv ω hω) hK
        (hdiag ω hω) (hdegree ω hω) (hsize ω hω)
      refine h.trans (measureReal_mono ?_)
      rintro x ⟨i, his, hxi⟩
      exact ⟨i, his, hxi.trans_le (le_abs_self _)⟩
    · rw [indicator_of_notMem hω]
      exact measureReal_nonneg
  have h := integral_mono ((integrable_const (1 / 4 : ℝ)).indicator hG) hi hbound
  simpa [integral_indicator_const _ hG, smul_eq_mul, div_eq_mul_inv] using h

end

end Erdos.Problem1144
