import Erdos.Problem1144.HarperCandidateGaussianLinear
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace Erdos.Problem1144

local instance {ι : Type*} : MeasurableSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → ι → ℝ))

local instance {ι : Type*} [Fintype ι] [DecidableEq ι] : BorelSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (BorelSpace (ι → ι → ℝ))

private theorem candidate_cfcHom_isometry
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : IsSelfAdjoint A) : Isometry (cfcHom hA (R := ℝ)) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro f
  rw [Matrix.IsHermitian.cfcHom_eq_cfcAux hA.isHermitian, Matrix.IsHermitian.cfcAux_apply,
    Unitary.conjStarAlgAut_apply, mul_assoc, CStarRing.norm_coe_unitary_mul,
    ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, Matrix.l2_opNorm_diagonal]
  change ‖(fun i => f ⟨hA.isHermitian.eigenvalues i,
    hA.isHermitian.eigenvalues_mem_spectrum_real i⟩)‖ = ‖f‖
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr fun i => f.norm_coe_le_norm _
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro x
    have hxmem : x.val ∈ Set.range hA.isHermitian.eigenvalues := by
      rw [← hA.isHermitian.spectrum_real_eq_range_eigenvalues]
      exact x.property
    obtain ⟨i, hi⟩ := hxmem
    have hx : (⟨hA.isHermitian.eigenvalues i,
        hA.isHermitian.eigenvalues_mem_spectrum_real i⟩ : spectrum ℝ A) = x :=
      Subtype.ext hi
    rw [← hx]
    exact norm_le_pi_norm (fun j => f ⟨hA.isHermitian.eigenvalues j,
      hA.isHermitian.eigenvalues_mem_spectrum_real j⟩) i

local instance {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsometricContinuousFunctionalCalculus ℝ (Matrix ι ι ℝ) IsSelfAdjoint where
  isometric := candidate_cfcHom_isometry

/-- Square roots of a measurable family of PSD covariance matrices are
measurable, including at singular matrices. -/
theorem candidate_measurable_covariance_sqrt
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {A : Ω → Matrix ι ι ℝ} (hA : Measurable A) (hpos : ∀ ω, (A ω).PosSemidef) :
    Measurable (fun ω => CFC.sqrt (A ω)) := by
  have hsub : Measurable (fun ω => (⟨A ω, (hpos ω).nonneg⟩ :
      {B : Matrix ι ι ℝ | 0 ≤ B})) := hA.subtype_mk
  have hc : Continuous (fun B : {B : Matrix ι ι ℝ | 0 ≤ B} => CFC.sqrt B.val) :=
    continuousOn_iff_continuous_restrict.mp CFC.continuousOn_sqrt
  exact hc.measurable.comp hsub

/-- A measurable covariance family has an explicit joint Gaussian
realization with one independent standard vector. This avoids assuming the
existence or measurability of a conditional Gaussian kernel. -/
noncomputable def candidateConditionalGaussian
    {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Ω → Matrix ι ι ℝ) (z : Ω × EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  candidateGaussianLinear (CFC.sqrt (A z.1)) z.2

theorem candidate_measurable_conditionalGaussian
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {A : Ω → Matrix ι ι ℝ} (hA : Measurable A) (hpos : ∀ ω, (A ω).PosSemidef) :
    Measurable (candidateConditionalGaussian A) := by
  have hs : Measurable (fun z : Ω × EuclideanSpace ℝ ι => CFC.sqrt (A z.1)) :=
    (candidate_measurable_covariance_sqrt hA hpos).comp measurable_fst
  unfold candidateConditionalGaussian candidateGaussianLinear
  apply (show Continuous (toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) by fun_prop).measurable.comp
  apply measurable_pi_lambda
  intro i
  exact Finset.measurable_sum _ fun j _ =>
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hs)).mul
      ((measurable_pi_apply j).comp (by fun_prop))

/-- At every fixed environment the realization has exactly the prescribed
Gaussian covariance, rather than merely the same diagonal moments. -/
theorem candidate_conditionalGaussian_map
    {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Ω → Matrix ι ι ℝ) (hpos : ∀ ω, (A ω).PosSemidef) (ω : Ω) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1).map
      (fun ξ => candidateConditionalGaussian A (ω, ξ)) = multivariateGaussian 0 (A ω) := by
  have h := (candidate_measurePreserving_gaussian_linear (CFC.sqrt (A ω))).map_eq
  have hs : (CFC.sqrt (A ω))ᴴ = CFC.sqrt (A ω) := (CFC.sqrt_nonneg _).isSelfAdjoint
  rw [hs, CFC.sqrt_mul_sqrt_self _ (hpos ω).nonneg] at h
  exact h

/-- Measurable random kernels produce a measurable covariance matrix.
Entry integrability is not needed for this measurability statement. -/
theorem candidate_measurable_random_gram
    {Ω V ι : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    [Fintype ι] [DecidableEq ι] (ν : Measure V) [SFinite ν]
    (f : ι → Ω → V → ℝ) (hf : ∀ i, Measurable (Function.uncurry (f i))) :
    Measurable (fun ω => candidateWeightedGram ν (fun i v => f i ω v) (fun _ => 1)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hF : StronglyMeasurable (Function.uncurry (fun ω v => f i ω v * f j ω v)) :=
    ((hf i).mul (hf j)).stronglyMeasurable
  have h := (hF.integral_prod_right (ν := ν)).measurable
  simpa only [candidateWeightedGram, one_mul, Function.uncurry_apply_pair] using h

/-- Conditional selected-event probabilities for the explicit realization
are measurable and integrable under every probability law. -/
theorem candidate_integrable_conditionalGaussian_selected_probability
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    {A : Ω → Matrix ι ι ℝ} (hA : Measurable A) (hpos : ∀ ω, (A ω).PosSemidef)
    (J : Ω → Finset ι) (hJ : ∀ i, MeasurableSet {ω | i ∈ J ω}) (K : ℝ) :
    Integrable (fun ω => (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1).real
      {ξ | ∃ i ∈ J ω, K < |candidateConditionalGaussian A (ω, ξ) i|}) Q := by
  have hE : MeasurableSet {z : Ω × EuclideanSpace ℝ ι |
      ∃ i ∈ J z.1, K < |candidateConditionalGaussian A z i|} := by
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    exact ((hJ i).preimage measurable_fst).inter
      (measurableSet_lt measurable_const
        ((by fun_prop : Measurable (fun x : EuclideanSpace ℝ ι => x i)).comp
          (candidate_measurable_conditionalGaussian hA hpos)).abs)
  exact Measure.integrable_measure_prodMk_left hE (by finiteness)

/-- The selected crossing probability of the realization is exactly the
corresponding covariance-law probability at each fixed environment. -/
theorem candidate_conditionalGaussian_selected_probability
    {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Ω → Matrix ι ι ℝ) (hpos : ∀ ω, (A ω).PosSemidef)
    (J : Ω → Finset ι) (K : ℝ) (ω : Ω) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1).real
      {ξ | ∃ i ∈ J ω, K < |candidateConditionalGaussian A (ω, ξ) i|} =
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) (A ω)).real
      {x | ∃ i ∈ J ω, K < |x i|} := by
  have hE : MeasurableSet {x : EuclideanSpace ℝ ι | ∃ i ∈ J ω, K < |x i|} := by
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    by_cases hi : i ∈ J ω
    · simpa only [hi, true_and] using
        (measurableSet_lt (f := fun _ : EuclideanSpace ℝ ι => K)
          (g := fun x => |x i|) measurable_const (by fun_prop))
    · simp [hi]
  rw [← candidate_conditionalGaussian_map A hpos ω]
  change _ = (((multivariateGaussian (0 : EuclideanSpace ℝ ι) 1).map
    (fun ξ => candidateConditionalGaussian A (ω, ξ))) _).toReal
  have hm : Measurable (fun ξ : EuclideanSpace ℝ ι =>
      candidateConditionalGaussian A (ω, ξ)) :=
    (candidateGaussianLinear (CFC.sqrt (A ω))).measurable
  rw [Measure.map_apply hm hE]
  rfl

/-- The conditional covariance-law probabilities used in the Gaussian
comparisons are integrable, with no conditional-kernel measurability premise. -/
theorem candidate_integrable_gaussian_selected_probability
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    {A : Ω → Matrix ι ι ℝ} (hA : Measurable A) (hpos : ∀ ω, (A ω).PosSemidef)
    (J : Ω → Finset ι) (hJ : ∀ i, MeasurableSet {ω | i ∈ J ω}) (K : ℝ) :
    Integrable (fun ω => (multivariateGaussian (0 : EuclideanSpace ℝ ι) (A ω)).real
      {x | ∃ i ∈ J ω, K < |x i|}) Q := by
  have hi := candidate_integrable_conditionalGaussian_selected_probability Q hA hpos J hJ K
  simp_rw [candidate_conditionalGaussian_selected_probability A hpos J K] at hi
  exact hi

/-- The kernel-distance comparison survives averaging over an arbitrary
external probability law, including any fixed prime cylinder. All Gaussian
probability measurability follows from the explicit realization above. -/
theorem candidate_integral_gaussian_gram_selected_crossing_le
    {Ω V ι : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    [Fintype ι] [DecidableEq ι] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (ν : Measure V) [SFinite ν] (f g : ι → Ω → V → ℝ)
    (hf : ∀ i, Measurable (Function.uncurry (f i)))
    (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (hf2 : ∀ ω i, MemLp (f i ω) 2 ν) (hg2 : ∀ ω i, MemLp (g i ω) 2 ν)
    (J : Ω → Finset ι) (hJ : ∀ i, MeasurableSet {ω | i ∈ J ω})
    (hE : Integrable (fun ω => ∑ i, ∫ v, (f i ω v - g i ω v) ^ 2 ∂ν) Q)
    (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ ω, (multivariateGaussian (0 : EuclideanSpace ℝ ι)
      (candidateWeightedGram ν (fun i v => g i ω v) (fun _ => 1))).real
        {x | ∃ i ∈ J ω, K + ε < |x i|} ∂Q) ≤
    (∫ ω, (multivariateGaussian (0 : EuclideanSpace ℝ ι)
      (candidateWeightedGram ν (fun i v => f i ω v) (fun _ => 1))).real
        {x | ∃ i ∈ J ω, K < |x i|} ∂Q) +
      (∫ ω, ∑ i, ∫ v, (f i ω v - g i ω v) ^ 2 ∂ν ∂Q) / ε ^ 2 := by
  have hFpos (ω : Ω) : (candidateWeightedGram ν (fun i v => f i ω v)
      (fun _ => 1)).PosSemidef :=
    candidateWeightedGram_posSemidef ν _ _
      (fun i j => by simpa only [one_mul] using (hf2 ω i).integrable_mul (hf2 ω j))
      (ae_of_all _ fun _ => Or.inl zero_le_one)
  have hGpos (ω : Ω) : (candidateWeightedGram ν (fun i v => g i ω v)
      (fun _ => 1)).PosSemidef :=
    candidateWeightedGram_posSemidef ν _ _
      (fun i j => by simpa only [one_mul] using (hg2 ω i).integrable_mul (hg2 ω j))
      (ae_of_all _ fun _ => Or.inl zero_le_one)
  have hiF := candidate_integrable_gaussian_selected_probability Q
    (candidate_measurable_random_gram ν f hf) hFpos J hJ K
  have hiG := candidate_integrable_gaussian_selected_probability Q
    (candidate_measurable_random_gram ν g hg) hGpos J hJ (K + ε)
  have h := integral_mono hiG (hiF.add (hE.div_const (ε ^ 2)))
    (fun ω => candidate_gaussian_gram_selected_crossing_le ν
      (fun i v => f i ω v) (fun i v => g i ω v) (hf2 ω) (hg2 ω) (J ω) K hε)
  simp only [Pi.add_apply] at h
  rw [integral_add hiF (hE.div_const (ε ^ 2)), integral_div] at h
  exact h

end Erdos.Problem1144
