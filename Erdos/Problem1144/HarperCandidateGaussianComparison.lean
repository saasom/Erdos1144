import Erdos.Problem1144.HarperCandidateReflection
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators RealInnerProductSpace

namespace Erdos.Problem1144

/-!
# A reflection substitute for Anderson's Gaussian comparison

The final cylinder argument only requires a fixed positive crossing
probability. Adding an independent symmetric vector preserves at least half
the probability of an absolute maximum crossing. Realizing a positive
semidefinite covariance difference as an independent Gaussian residual
therefore supplies every PSD comparison needed by the candidate, with a
factor of two instead of Anderson's sharper constant one.
-/

section Covariance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Independent centered Gaussian vectors add their covariance matrices. -/
theorem candidate_multivariateGaussian_conv
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (multivariateGaussian 0 A).conv (multivariateGaussian 0 B) =
      multivariateGaussian 0 (A + B) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_conv, charFun_multivariateGaussian hA,
    charFun_multivariateGaussian hB, charFun_multivariateGaussian (hA.add hB),
    ← Complex.exp_add]
  congr 1
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub,
    Matrix.add_mulVec, dotProduct_add, Complex.ofReal_add]
  ring

/-- Negation preserves every centered multivariate Gaussian, including
singular covariance matrices. -/
theorem candidate_measurePreserving_neg_multivariateGaussian
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    MeasurePreserving (fun x : EuclideanSpace ℝ ι ↦ -x)
      (multivariateGaussian 0 A) (multivariateGaussian 0 A) := by
  refine ⟨by fun_prop, ?_⟩
  apply Measure.ext_of_charFun
  ext t
  have hmap := charFun_map_smul (μ := multivariateGaussian (0 : EuclideanSpace ℝ ι) A)
    (-1 : ℝ) t
  simp only [neg_one_smul] at hmap
  rw [hmap, charFun_multivariateGaussian hA, charFun_multivariateGaussian hA]
  simp [Matrix.mulVec_neg]

/-- Gaussian covariance domination preserves a fixed positive probability
of every selected absolute-maximum crossing. The subset is arbitrary and
may be fixed after conditioning on any external randomness. -/
theorem candidate_multivariateGaussian_selected_absolute_ge_half
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hBA : (B - A).PosSemidef)
    (J : Finset ι) (K : ℝ) :
    (multivariateGaussian 0 A).real {x | ∃ i ∈ J, K < |x i|} / 2 ≤
      (multivariateGaussian 0 B).real {x | ∃ i ∈ J, K < |x i|} := by
  classical
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ ι) A
  let ν := multivariateGaussian (0 : EuclideanSpace ℝ ι) (B - A)
  let E : Set (EuclideanSpace ℝ ι) := {x | ∃ i ∈ J, K < |x i|}
  have hE : MeasurableSet E := by
    rw [show E = ⋃ i ∈ J, {x : EuclideanSpace ℝ ι | K < |x i|} by ext; simp [E]]
    exact Finset.measurableSet_biUnion J fun i _ ↦
      measurableSet_lt measurable_const (by fun_prop)
  have hτ : MeasurePreserving
      (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ (z.1, -z.2))
      (μ.prod ν) (μ.prod ν) :=
    (MeasurePreserving.id μ).prod (candidate_measurePreserving_neg_multivariateGaussian hBA)
  have htwice := candidate_measureReal_le_two_of_reflection_cover hτ
    (E := E ×ˢ Set.univ)
    (P := {z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι | z.1 + z.2 ∈ E})
    (by
      rintro ⟨x, y⟩ ⟨⟨i, hi, hx⟩, _⟩
      by_cases hp : K < |x i + y i|
      · exact Or.inl ⟨i, hi, hp⟩
      · right
        refine ⟨i, hi, ?_⟩
        change K < |x i + -y i|
        by_contra hn
        have htri := abs_add_le (x i + y i) (x i + -y i)
        rw [show (x i + y i) + (x i + -y i) = 2 * x i by ring,
          abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
        linarith)
  have hsrc : (μ.prod ν).real (E ×ˢ Set.univ) = μ.real E := by
    rw [measureReal_prod_prod]
    simp
  have hsum : μ.conv ν = multivariateGaussian 0 B := by
    have h := candidate_multivariateGaussian_conv hA hBA
    simpa [μ, ν] using h
  have htarget :
      (μ.prod ν).real {z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι | z.1 + z.2 ∈ E} =
      (multivariateGaussian 0 B).real E := by
    rw [← hsum]
    change _ = (((μ.prod ν).map (fun z ↦ z.1 + z.2)) E).toReal
    rw [Measure.map_apply (by fun_prop) hE]
    rfl
  rw [hsrc, htarget] at htwice
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by simpa [mul_comm] using htwice)

end Covariance

end Erdos.Problem1144
