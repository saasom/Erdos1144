import Erdos.Problem1144.HarperCandidateCovariance
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory

namespace Erdos.Problem1144

/-- A squared kernel-distance bound transfers a diagonal second moment
without requiring an entrywise covariance comparison. -/
theorem candidate_integral_square_le_two_add_two_distance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, g x ^ 2 ∂μ) ≤
      2 * (∫ x, f x ^ 2 ∂μ) + 2 * ∫ x, (f x - g x) ^ 2 ∂μ := by
  have hi := integral_mono hg.integrable_sq
    ((hf.integrable_sq.const_mul 2).add ((hf.sub hg).integrable_sq.const_mul 2))
    (fun x => by
      change g x ^ 2 ≤ 2 * f x ^ 2 + 2 * (f x - g x) ^ 2
      nlinarith [sq_nonneg (2 * f x - g x)])
  simpa only [Pi.add_apply, integral_add (hf.integrable_sq.const_mul 2)
    ((hf.sub hg).integrable_sq.const_mul 2), integral_const_mul] using hi

/-- The same bound stated on the literal real Gram diagonal. -/
theorem candidate_gram_diagonal_le_two_add_two_distance
    {ι Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : ι → Ω → ℝ) (i : ι) (hf : MemLp (f i) 2 μ) (hg : MemLp (g i) 2 μ) :
    candidateWeightedGram μ g (fun _ => 1) i i ≤
      2 * candidateWeightedGram μ f (fun _ => 1) i i +
        2 * ∫ x, (f i x - g i x) ^ 2 ∂μ := by
  simpa only [candidateWeightedGram, one_mul, ← pow_two] using
    candidate_integral_square_le_two_add_two_distance μ hf hg

/-- A full-kernel variance floor `v` and common squared-distance error at
most `v/4` give the retained-kernel variance floor `v/4`. -/
theorem candidate_gram_diagonal_ge_quarter_of_squared_distance
    {ι Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : ι → Ω → ℝ) (i : ι) (hf : MemLp (f i) 2 μ) (hg : MemLp (g i) 2 μ)
    {v E : ℝ} (hv : v ≤ candidateWeightedGram μ g (fun _ => 1) i i)
    (hd : (∫ x, (f i x - g i x) ^ 2 ∂μ) ≤ E) (hE : E ≤ v / 4) :
    v / 4 ≤ candidateWeightedGram μ f (fun _ => 1) i i := by
  have h := candidate_gram_diagonal_le_two_add_two_distance μ f g i hf hg
  linarith

end Erdos.Problem1144
