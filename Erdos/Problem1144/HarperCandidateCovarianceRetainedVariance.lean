import Erdos.Problem1144.HarperCandidateCovarianceRetainedComparison
import Erdos.Problem1144.HarperCandidateCovarianceVarianceTransfer
import Erdos.Problem1144.HarperCandidateGaussianVarianceLower
import Erdos.Problem1144.HarperCandidateGaussianWhiteGeometry

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Erdos.Problem1144
noncomputable section

/-- The simultaneous variance floor for the actual retained white kernels. -/
def candidateRetainedWhiteVarianceFloor {ι : Type*} (y start N depth M : ℕ)
    (W : ℝ) (s : Finset ℕ) (u : ι → ℝ) (T B v : ℝ) : Set Omega :=
  {ω | ∀ i, v ≤ candidateWeightedGram volume
    (fun i => candidateEulerScreenWhiteKernel y ω
      (candidateCovarianceRetainedFrequencySet start N depth M W s ω) T B (u i))
    (fun _ => 1) i i}

theorem candidate_measurableSet_retainedWhiteVarianceFloor
    {ι : Type*} [Fintype ι] [DecidableEq ι] (y start N depth M : ℕ)
    (W : ℝ) (s : Finset ℕ) (u : ι → ℝ) (T B v : ℝ) :
    MeasurableSet (candidateRetainedWhiteVarianceFloor y start N depth M W s u T B v) := by
  have hm := candidate_measurable_random_gram volume
    (fun i ω => candidateEulerScreenWhiteKernel y ω
      (candidateCovarianceRetainedFrequencySet start N depth M W s ω) T B (u i))
    (fun i => candidate_measurable_eulerScreenWhiteKernel_joint y _
      (candidate_measurableSet_retainedFrequencyGraph start N depth M W s) T B (u i))
  simp only [candidateRetainedWhiteVarianceFloor, setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le measurable_const
    ((measurable_pi_apply i).comp ((measurable_pi_apply i).comp hm))

/-- One actual retained-error budget plus the finite total Perron error
controls every retained-to-squarefree white kernel distance on the common mesh. -/
theorem candidate_retainedWhiteKernel_squarefree_distance_le
    {ι : Type*} [Fintype ι] (y start N depth M : ℕ) (W : ℝ) (s : Finset ℕ)
    (u : ι → ℝ) {ω : Omega} (hω : ω ∈ candidateCovarianceCommonMeshEvent start N M W)
    {H T : ℝ} (hH : (M : ℝ) ≤ H) (hT : 0 < T) (B : ℝ) (i : ι) :
    (∫ r, (candidateEulerScreenWhiteKernel y ω
      (candidateCovarianceRetainedFrequencySet start N depth M W s ω) T B (u i) r -
      candidateSquarefreeWhiteKernel ω (u i) T r) ^ 2) ≤
      2 * candidateCovarianceRetainedError y start N depth M W T s ω +
        2 * candidateEulerBandWhiteTotalError y u H T B ω := by
  classical
  let f := candidateEulerScreenWhiteKernel y ω
    (candidateCovarianceRetainedFrequencySet start N depth M W s ω) T B (u i)
  let g := candidateEulerBandWhiteKernel y ω H T B (u i)
  let w := candidateSquarefreeWhiteKernel ω (u i) T
  have hf : MemLp f 2 := candidate_memLp_eulerScreenWhiteKernel y ω
    (candidate_measurableSet_retainedFrequencySet start N depth M W s ω) H
    (candidate_retainedFrequencySet_subset_band start N depth M W s ω hH) B (u i) hT
  have hg : MemLp g 2 := candidate_memLp_eulerBandWhiteKernel y ω H B (u i) hT
  have hw : MemLp w 2 := candidate_memLp_squarefreeWhiteKernel ω (u i) hT
  have hi := integral_mono (hf.sub hw).integrable_sq
    (((hf.sub hg).integrable_sq.const_mul 2).add ((hg.sub hw).integrable_sq.const_mul 2))
    (fun r => by
      change (f r - w r) ^ 2 ≤ 2 * (f r - g r) ^ 2 + 2 * (g r - w r) ^ 2
      nlinarith [sq_nonneg (f r - 2 * g r + w r)])
  simp only [Pi.add_apply] at hi
  rw [integral_add ((hf.sub hg).integrable_sq.const_mul 2)
    ((hg.sub hw).integrable_sq.const_mul 2)] at hi
  simp only [integral_const_mul] at hi
  have hret := candidate_retainedWhiteKernel_distance_le y start N depth M W s hω hH hT B (u i)
  have htotal : (∫ r, (g r - w r) ^ 2) ≤ candidateEulerBandWhiteTotalError y u H T B ω := by
    dsimp only [candidateEulerBandWhiteTotalError, g, w]
    exact Finset.single_le_sum
      (f := fun j : ι => ∫ r, (candidateEulerBandWhiteKernel y ω H T B (u j) r -
        candidateSquarefreeWhiteKernel ω (u j) T r) ^ 2)
      (fun j _ => integral_nonneg fun r => sq_nonneg _) (Finset.mem_univ i)
  exact hi.trans (add_le_add (mul_le_mul_of_nonneg_left hret (by norm_num))
    (mul_le_mul_of_nonneg_left htotal (by norm_num)))

/-- The actual full white variance floor transfers coordinatewise on the
common mesh whenever the sum of the two literal errors is at most `v/8`. -/
theorem candidate_mem_retainedWhiteVarianceFloor_of_white_floor
    {n : ℕ} (y start N depth M : ℕ) (W : ℝ) (s : Finset ℕ) (u : Fin n → ℝ)
    {ω : Omega} (hω : ω ∈ candidateCovarianceCommonMeshEvent start N M W)
    {H T : ℝ} (hH : (M : ℝ) ≤ H) (hT : 0 < T) (B : ℝ) (v : ℝ)
    (hv : ∀ i, v ≤ candidateWhiteCovariance (harperCandidateSquarefreeLogProcess ω) u T i i)
    (he : candidateCovarianceRetainedError y start N depth M W T s ω +
      candidateEulerBandWhiteTotalError y u H T B ω ≤ v / 8) :
    ω ∈ candidateRetainedWhiteVarianceFloor y start N depth M W s u T B (v / 4) := by
  intro i
  apply candidate_gram_diagonal_ge_quarter_of_squared_distance volume
    (fun i => candidateEulerScreenWhiteKernel y ω
      (candidateCovarianceRetainedFrequencySet start N depth M W s ω) T B (u i))
    (fun i => candidateSquarefreeWhiteKernel ω (u i) T) i
    (candidate_memLp_eulerScreenWhiteKernel y ω
      (candidate_measurableSet_retainedFrequencySet start N depth M W s ω) H
      (candidate_retainedFrequencySet_subset_band start N depth M W s ω hH) B (u i) hT)
    (candidate_memLp_squarefreeWhiteKernel ω (u i) hT)
  · simpa only [candidate_squarefreeWhiteKernel_gram_eq_whiteCovariance ω u hT] using hv i
  · exact candidate_retainedWhiteKernel_squarefree_distance_le y start N depth M W s u hω hH hT B i
  · linarith

/-- The actual retained variance-floor probability loses only one mesh
failure and the Markov cost of the two proved common error budgets. -/
theorem candidate_retainedWhiteVariance_probability_ge
    {n : ℕ} (q : Finset ℕ) (η : q → Bool) (y start N depth M : ℕ)
    (W : ℝ) (s : Finset ℕ) (u : Fin n → ℝ) {H T : ℝ}
    (hH : (M : ℝ) ≤ H) (hH0 : 0 < H) (hT : 0 < T) (B : ℝ)
    (hu : ∀ i, u i ≤ B) (hy : ∀ i, ⌊Real.exp (u i - T)⌋₊ ≤ y)
    {v : ℝ} (hv : 0 < v) :
    (candidateCylinderLaw q η).real
      {ω | ∀ i, v ≤ candidateWhiteCovariance (harperCandidateSquarefreeLogProcess ω) u T i i} -
      (candidateCylinderLaw q η).real (candidateCovarianceCommonMeshEvent start N M W)ᶜ -
      (8 / v) *
        ((∫ ω, candidateCovarianceRetainedError y start N depth M W T s ω ∂mu) +
          ∫ ω, candidateEulerBandWhiteTotalError y u H T B ω ∂mu) /
        mu.real (candidateCylinder q η) ≤
      (candidateCylinderLaw q η).real
        (candidateRetainedWhiteVarianceFloor y start N depth M W s u T B (v / 4)) := by
  let Q := candidateCylinderLaw q η
  let E := {ω | ∀ i, v ≤ candidateWhiteCovariance (harperCandidateSquarefreeLogProcess ω) u T i i}
  let R := candidateRetainedWhiteVarianceFloor y start N depth M W s u T B (v / 4)
  let A := candidateCovarianceCommonMeshEvent start N M W
  let F := fun ω => candidateCovarianceRetainedError y start N depth M W T s ω +
    candidateEulerBandWhiteTotalError y u H T B ω
  let D := {ω | v / 8 ≤ F ω}
  have hiR := candidate_integrable_retainedError y start N depth M W T s
  have hiP := candidate_integrable_eulerBandWhiteTotalError y u hH0 hT B hu hy
  have hF : ∀ ω, 0 ≤ F ω := fun ω => add_nonneg
    (candidate_retainedError_nonneg y start N depth M W hT.le s ω)
    (candidate_eulerBandWhiteTotalError_nonneg y u H T B ω)
  have hc := candidateCylinderLaw_integral_nonneg_le q η (hiR.add hiP) hF
  have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hF) hc.1 (v / 8)
  have hmarkov := (le_div_iff₀' (by positivity : 0 < v / 8)).mpr (hm.trans hc.2)
  have hmarkov' : Q.real D ≤ (8 / v) *
      ((∫ ω, candidateCovarianceRetainedError y start N depth M W T s ω ∂mu) +
        ∫ ω, candidateEulerBandWhiteTotalError y u H T B ω ∂mu) /
        mu.real (candidateCylinder q η) := by
    have he : (∫ ω, F ω ∂mu) =
        (∫ ω, candidateCovarianceRetainedError y start N depth M W T s ω ∂mu) +
          ∫ ω, candidateEulerBandWhiteTotalError y u H T B ω ∂mu := integral_add hiR hiP
    change Q.real D ≤ (∫ ω, F ω ∂mu) / mu.real (candidateCylinder q η) / (v / 8) at hmarkov
    rw [he] at hmarkov
    exact hmarkov.trans_eq (by ring)
  have hsub : E ⊆ R ∪ (Aᶜ ∪ D) := by
    intro ω hω
    by_cases ha : ω ∈ A
    · by_cases hd : ω ∈ D
      · exact Or.inr (Or.inr hd)
      · apply Or.inl
        exact candidate_mem_retainedWhiteVarianceFloor_of_white_floor y start N depth M W s u
          ha hH hT B v hω (le_of_lt (lt_of_not_ge hd))
    · exact Or.inr (Or.inl ha)
  have hmE := (measureReal_mono (μ := Q) hsub).trans
    ((measureReal_union_le R (Aᶜ ∪ D)).trans
      (add_le_add le_rfl (measureReal_union_le Aᶜ D)))
  change Q.real E - Q.real Aᶜ - _ ≤ Q.real R
  linarith

end
end Erdos.Problem1144
