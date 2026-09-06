import Erdos.Problem1144.HarperCandidateLogScreen
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

/-- A weighted real Gram matrix, with scalar integrals as its entries. -/
noncomputable def candidateWeightedGram
    {ι Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ι → Ω → ℝ) (w : Ω → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∫ v, w v * f i v * f j v ∂μ

/-- Exact quadratic-form identity for a finite weighted Gram matrix. -/
theorem candidateWeightedGram_quadratic
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ι → Ω → ℝ) (w : Ω → ℝ)
    (hi : ∀ i j, Integrable (fun v => w v * f i v * f j v) μ)
    (x : ι → ℝ) :
    dotProduct (star x) (Matrix.mulVec (candidateWeightedGram μ f w) x) =
      ∫ v, w v * (∑ i, x i * f i v) ^ 2 ∂μ := by
  classical
  have heq : (fun v => w v * (∑ i, x i * f i v) ^ 2) =
      (fun v => ∑ i, ∑ j, x i * (w v * f i v * f j v) * x j) := by
    funext v
    simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hinner (i : ι) :
      (∫ v, ∑ j, x i * (w v * f i v * f j v) * x j ∂μ) =
        ∑ j, x i * (∫ v, w v * f i v * f j v ∂μ) * x j := by
    rw [integral_finset_sum Finset.univ
      (fun j _ => ((hi i j).const_mul (x i)).mul_const (x j))]
    simp only [integral_mul_const, integral_const_mul]
  rw [heq, integral_finset_sum]
  · simp_rw [hinner]
    simp [candidateWeightedGram, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  · intro i _
    exact integrable_finset_sum _ fun j _ => ((hi i j).const_mul _).mul_const _

/-- A nonnegative scalar weight on the active feature support gives a positive
semidefinite Gram matrix. No probabilistic comparison is assumed. -/
theorem candidateWeightedGram_posSemidef
    {ι Ω : Type*} [Finite ι] [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ι → Ω → ℝ) (w : Ω → ℝ)
    (hi : ∀ i j, Integrable (fun v => w v * f i v * f j v) μ)
    (hw : ∀ᵐ v ∂μ, 0 ≤ w v ∨ ∀ i, f i v = 0) :
    (candidateWeightedGram μ f w).PosSemidef := by
  letI := Fintype.ofFinite ι
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial, candidateWeightedGram]
    apply integral_congr_ae
    filter_upwards [] with v
    ring
  · intro x
    rw [candidateWeightedGram_quadratic μ f w hi x]
    apply integral_nonneg_of_ae
    filter_upwards [hw] with v hv
    rcases hv with hv | hv
    · exact mul_nonneg hv (sq_nonneg _)
    · simp [hv]

/-- Pointwise comparison of scalar weights yields actual matrix PSD
comparison, even if the comparison is only true on the feature support. -/
theorem candidateWeightedGram_sub_posSemidef
    {ι Ω : Type*} [Finite ι] [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ι → Ω → ℝ) (w₀ w₁ : Ω → ℝ)
    (hi₀ : ∀ i j, Integrable (fun v => w₀ v * f i v * f j v) μ)
    (hi₁ : ∀ i j, Integrable (fun v => w₁ v * f i v * f j v) μ)
    (hw : ∀ᵐ v ∂μ, w₀ v ≤ w₁ v ∨ ∀ i, f i v = 0) :
    (candidateWeightedGram μ f w₁ - candidateWeightedGram μ f w₀).PosSemidef := by
  have heq : candidateWeightedGram μ f w₁ - candidateWeightedGram μ f w₀ =
      candidateWeightedGram μ f (fun v => w₁ v - w₀ v) := by
    ext i j
    simp only [candidateWeightedGram, Matrix.sub_apply]
    rw [← integral_sub (hi₁ i j) (hi₀ i j)]
    apply integral_congr_ae
    filter_upwards [] with v
    ring
  rw [heq]
  apply candidateWeightedGram_posSemidef
  · intro i j
    simpa only [sub_mul] using (hi₁ i j).sub (hi₀ i j)
  · filter_upwards [hw] with v hv
    exact hv.imp sub_nonneg.mpr id

/-- Restricting the integration domain is the same as inserting its indicator
into the scalar weight. -/
theorem candidateWeightedGram_restrict
    {ι Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ι → Ω → ℝ) (w : Ω → ℝ) {S : Set Ω} (hS : MeasurableSet S) :
    candidateWeightedGram (μ.restrict S) f w =
      candidateWeightedGram μ f (S.indicator w) := by
  classical
  ext i j
  unfold candidateWeightedGram
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [] with v
  by_cases hv : v ∈ S <;> simp [hv]

/-- Multiplying a scalar covariance weight scales its whole Gram matrix. -/
theorem candidateWeightedGram_const_mul
    {ι Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ι → Ω → ℝ) (w : Ω → ℝ) (c : ℝ) :
    candidateWeightedGram μ f (fun v => c * w v) = c • candidateWeightedGram μ f w := by
  ext i j
  simp only [candidateWeightedGram, Matrix.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  ring

/-- Diagonal rescaling of covariance entries, written without any inverse
matrix convention. -/
noncomputable def candidateCovarianceDiagonal {ι : Type*}
    (r : ι → ℝ) (C : Matrix ι ι ℝ) : Matrix ι ι ℝ := fun i j => r i * C i j * r j

theorem candidateWeightedGram_diagonal
    {ι Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ι → Ω → ℝ) (w : Ω → ℝ) (r : ι → ℝ) :
    candidateCovarianceDiagonal r (candidateWeightedGram μ f w) =
      candidateWeightedGram μ (fun i v => r i * f i v) w := by
  ext i j
  simp only [candidateCovarianceDiagonal, candidateWeightedGram]
  rw [← integral_const_mul, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with v
  ring

/-- Exact exponential reweighting behind the stationary diagonal comparisons. -/
theorem candidateWeightedGram_exponential_shift
    {ι : Type*} (μ : Measure ℝ) (a : ℝ → ℝ) (u : ι → ℝ) (σ c L : ℝ) :
    candidateWeightedGram μ
      (fun i v => a (u i - v) * Real.exp (-σ * (u i - v))) (fun _ => 1 / L) =
    candidateWeightedGram μ
      (fun i v => Real.exp (-σ * (u i - c)) * a (u i - v))
      (fun v => Real.exp (2 * σ * (v - c)) / L) := by
  ext i j
  unfold candidateWeightedGram
  apply integral_congr_ae
  filter_upwards [] with v
  have hexp (i : ι) : Real.exp (-σ * (u i - v)) =
      Real.exp (-σ * (u i - c)) * Real.exp (σ * (v - c)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he : Real.exp (2 * σ * (v - c)) = Real.exp (σ * (v - c)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp i, hexp j, he]
  ring

/-- The stationary covariance (14), or (18) when `L=T`. -/
noncomputable def candidateStationaryCovariance {ι : Type*}
    (a : ℝ → ℝ) (u : ι → ℝ) (σ L : ℝ) : Matrix ι ι ℝ :=
  candidateWeightedGram volume
    (fun i v => a (u i - v) * Real.exp (-σ * (u i - v))) (fun _ => 1 / L)

/-- The white-noise covariance with reciprocal-prime-time scalar weight. -/
noncomputable def candidateWhiteCovariance {ι : Type*}
    (a : ℝ → ℝ) (u : ι → ℝ) (T : ℝ) : Matrix ι ι ℝ :=
  candidateWeightedGram (volume.restrict (Ici T)) (fun i v => a (u i - v))
    (fun v => 1 / v)

/-- Candidate equation (16), as an actual PSD difference of the stationary
covariance and the diagonally rescaled Harper white-noise covariance.
The hypotheses only assert that the displayed covariance entries exist. -/
theorem candidate_stationary_squarefree_covariance_domination
    {ι : Type*} [Finite ι] (a : ℝ → ℝ) (u : ι → ℝ)
    {σ V : ℝ} (hσ : 0 ≤ σ) (hV : 0 < V)
    (hiQ : ∀ i j, Integrable (fun v =>
      Real.exp (2 * σ * (v - V)) / V *
        (Real.exp (-σ * (u i - V)) * a (u i - v)) *
        (Real.exp (-σ * (u j - V)) * a (u j - v))))
    (hiC : ∀ i j, IntegrableOn (fun v =>
      (1 / v) * (Real.exp (-σ * (u i - V)) * a (u i - v)) *
        (Real.exp (-σ * (u j - V)) * a (u j - v))) (Ici V)) :
    (candidateStationaryCovariance a u σ V -
      candidateCovarianceDiagonal (fun i => Real.exp (-σ * (u i - V)))
        (candidateWhiteCovariance a u V)).PosSemidef := by
  classical
  unfold candidateStationaryCovariance candidateWhiteCovariance
  rw [candidateWeightedGram_exponential_shift _ _ _ σ V V,
    candidateWeightedGram_diagonal, candidateWeightedGram_restrict _ _ _ measurableSet_Ici]
  apply candidateWeightedGram_sub_posSemidef
  · intro i j
    have hi := (integrable_indicator_iff measurableSet_Ici).mpr (hiC i j)
    convert hi using 1
    funext v
    by_cases hv : v ∈ Ici V <;> simp [hv]
  · exact hiQ
  · filter_upwards [] with v
    left
    by_cases hv : v ∈ Ici V
    · rw [indicator_of_mem hv]
      have hvpos : 0 < v := hV.trans_le hv
      have he : 1 ≤ Real.exp (2 * σ * (v - V)) :=
        Real.one_le_exp_iff.mpr (mul_nonneg (by positivity) (sub_nonneg.mpr hv))
      calc
        1 / v ≤ 1 / V := one_div_le_one_div_of_le hV hv
        _ ≤ Real.exp (2 * σ * (v - V)) / V := div_le_div_of_nonneg_right he hV.le
    · rw [indicator_of_notMem hv]
      positivity

/-- Candidate equation (26) in its exact rescaled integral form. The
comparison is required only where some process feature is active; all
features vanish beyond the last grid endpoint. -/
theorem candidate_complete_white_covariance_domination
    {ι : Type*} [Finite ι] (a : ℝ → ℝ) (u : ι → ℝ)
    {T σ β t₀ D : ℝ} (hT : 0 < T) (hσ : 0 ≤ σ)
    (huβ : ∀ i, u i ≤ β * T) (huD : ∀ i, u i ≤ t₀ + D)
    (hazero : ∀ x < 0, a x = 0)
    (hiQ : ∀ i j, IntegrableOn (fun v =>
      Real.exp (2 * σ * (v - t₀)) / T * a (u i - v) * a (u j - v)) (Ici T))
    (hiC : ∀ i j, IntegrableOn (fun v => (1 / v) * a (u i - v) * a (u j - v)) (Ici T)) :
    ((β * Real.exp (2 * σ * D)) • candidateWhiteCovariance a u T -
      candidateWeightedGram (volume.restrict (Ici T)) (fun i v => a (u i - v))
        (fun v => Real.exp (2 * σ * (v - t₀)) / T)).PosSemidef := by
  unfold candidateWhiteCovariance
  rw [← candidateWeightedGram_const_mul]
  apply candidateWeightedGram_sub_posSemidef
  · exact hiQ
  · intro i j
    convert (hiC i j).const_mul (β * Real.exp (2 * σ * D)) using 1
    funext v
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with v hv
    by_cases hall : ∀ i, a (u i - v) = 0
    · exact Or.inr hall
    · left
      push Not at hall
      obtain ⟨i, hi⟩ := hall
      have hvi : v ≤ u i := by
        by_contra hh
        exact hi (hazero _ (sub_neg.mpr (lt_of_not_ge hh)))
      have hvT : 0 < v := hT.trans_le hv
      have hE : Real.exp (2 * σ * (v - t₀)) ≤ Real.exp (2 * σ * D) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (by linarith [huD i]) (by positivity)
      have hrec : 1 / T ≤ β / v := by
        apply (div_le_div_iff₀ hT hvT).mpr
        simpa only [one_mul] using hvi.trans (huβ i)
      calc
        _ ≤ Real.exp (2 * σ * D) / T := div_le_div_of_nonneg_right hE hT.le
        _ ≤ Real.exp (2 * σ * D) * (β / v) := by
          simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hrec (Real.exp_pos _).le
        _ = _ := by ring

/-- The rescaled covariance in equation (26) is exactly the integrated
scalar-weight form used above. This identifies both diagonal factors without
any approximation or matrix-inverse side condition. -/
theorem candidate_truncated_covariance_rescale_eq
    {ι : Type*} (a : ℝ → ℝ) (u : ι → ℝ) (T σ t₀ : ℝ) :
    candidateCovarianceDiagonal (fun i => Real.exp (σ * (u i - t₀)))
      (candidateWeightedGram (volume.restrict (Ici T))
        (fun i v => a (u i - v) * Real.exp (-σ * (u i - v))) (fun _ => 1 / T)) =
      candidateWeightedGram (volume.restrict (Ici T)) (fun i v => a (u i - v))
        (fun v => Real.exp (2 * σ * (v - t₀)) / T) := by
  rw [candidateWeightedGram_diagonal]
  ext i j
  unfold candidateWeightedGram
  apply integral_congr_ae
  filter_upwards [] with v
  have he (i : ι) : Real.exp (σ * (u i - t₀)) *
      (a (u i - v) * Real.exp (-σ * (u i - v))) =
      a (u i - v) * Real.exp (σ * (v - t₀)) := by
    calc
      _ = a (u i - v) *
          (Real.exp (σ * (u i - t₀)) * Real.exp (-σ * (u i - v))) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring
  have hexp : Real.exp (2 * σ * (v - t₀)) = Real.exp (σ * (v - t₀)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he i, he j, hexp]
  ring

end Erdos.Problem1144

#print axioms Erdos.Problem1144.candidateWeightedGram_sub_posSemidef
#print axioms Erdos.Problem1144.candidate_stationary_squarefree_covariance_domination
#print axioms Erdos.Problem1144.candidate_complete_white_covariance_domination
#print axioms Erdos.Problem1144.candidate_truncated_covariance_rescale_eq
