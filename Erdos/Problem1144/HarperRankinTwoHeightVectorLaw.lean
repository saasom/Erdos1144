import Erdos.Problem1144.HarperRankinTwoHeightCharacteristic
import Erdos.Problem1144.HarperTwoHeightVectorLaw

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ComplexConjugate ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# The shifted two-height block as a bivariate law
-/

noncomputable def harperRankinTwoHeightPrimeBlockVector
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t s : ℝ) (eta : Problem520.HarperPrimeCube y) : ℝ × ℝ :=
  (∑ p ∈ S, harperRankinTwoHeightPrimeFluctuation p.1 a t s t (eta p),
    ∑ p ∈ S, harperRankinTwoHeightPrimeFluctuation p.1 a t s s (eta p))

theorem harperTwoHeightProjection_rankinBlockVector
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t s v w : ℝ) (eta : Problem520.HarperPrimeCube y) :
    harperTwoHeightProjection v w
        (harperRankinTwoHeightPrimeBlockVector y S a t s eta) =
      harperRankinTwoHeightProjectedPrimeBlockSum y S a t s v w eta := by
  simp only [harperTwoHeightProjection_apply,
    harperRankinTwoHeightPrimeBlockVector,
    harperRankinTwoHeightProjectedPrimeBlockSum,
    harperRankinTwoHeightProjectedPrimeIncrement]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

noncomputable def harperRankinTwoHeightPrimeBlockVectorLaw
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s : ℝ) : Measure (ℝ × ℝ) :=
  Measure.map (harperRankinTwoHeightPrimeBlockVector y S a t s)
    (harperRankinTwoHeightCubeLaw y a ha t s)

instance harperRankinTwoHeightPrimeBlockVectorLaw_isProbabilityMeasure
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s : ℝ) :
    IsProbabilityMeasure
      (harperRankinTwoHeightPrimeBlockVectorLaw y S a ha t s) := by
  unfold harperRankinTwoHeightPrimeBlockVectorLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_of_finite _).aemeasurable

theorem charFunDual_harperRankinTwoHeightPrimeBlockVectorLaw
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s v w : ℝ) :
    charFunDual (harperRankinTwoHeightPrimeBlockVectorLaw
        y S a ha t s) (harperTwoHeightProjection v w) =
      harperRankinTwoHeightProjectedCubeCharacteristic
        y S a ha t s v w := by
  rw [charFunDual_apply]
  unfold harperRankinTwoHeightPrimeBlockVectorLaw
  rw [integral_map (measurable_of_finite _).aemeasurable (by fun_prop)]
  unfold harperRankinTwoHeightProjectedCubeCharacteristic
  apply integral_congr_ae
  exact ae_of_all _ fun eta ↦ by
    change
      Complex.exp
          (((harperTwoHeightProjection v w
            (harperRankinTwoHeightPrimeBlockVector y S a t s eta) : ℝ) :
              ℂ) * Complex.I) =
        Complex.exp
          (((harperRankinTwoHeightProjectedPrimeBlockSum
            y S a t s v w eta : ℝ) : ℂ) * Complex.I)
    rw [harperTwoHeightProjection_rankinBlockVector]

theorem norm_charFunDual_harperRankinTwoHeightScheduledVectorLaw_sub_gaussian_le
    (y j : ℕ) (a : ℝ) (ha : 0 ≤ a) (t s v w : ℝ)
    (hfrequency :
      2 * (|v| + |w|) ≤
        Real.sqrt (Problem520.harperBlockEndpoint j : ℝ)) :
    ‖charFunDual
          (harperRankinTwoHeightPrimeBlockVectorLaw y
            (Problem520.harperScheduledPrimeBlock y j)
            a ha t s)
          (harperTwoHeightProjection v w) -
        Complex.exp
          (-((harperRankinTwoHeightProjectedBlockVariance y
            (Problem520.harperScheduledPrimeBlock y j)
            a ha t s v w / 2 : ℝ) : ℂ))‖ ≤
      (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ *
        (16 * (|v| + |w|) ^ 3 +
          2 * (|v| + |w|) ^ 4) := by
  rw [charFunDual_harperRankinTwoHeightPrimeBlockVectorLaw]
  exact
    norm_harperRankinTwoHeightScheduledProjectedCubeCharacteristic_sub_gaussian_le
      y j a ha t s v w hfrequency

#print axioms Erdos.Problem1144.harperTwoHeightProjection_rankinBlockVector
#print axioms Erdos.Problem1144.charFunDual_harperRankinTwoHeightPrimeBlockVectorLaw
#print axioms Erdos.Problem1144.norm_charFunDual_harperRankinTwoHeightScheduledVectorLaw_sub_gaussian_le

end

end Problem1144
end Erdos
