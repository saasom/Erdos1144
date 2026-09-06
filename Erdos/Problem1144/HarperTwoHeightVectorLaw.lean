import Erdos.Problem1144.HarperOverlapShell

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ComplexConjugate ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# The actual two-height block as a bivariate law

The characteristic estimate was first proved in scalar Cramer--Wold form.
This module packages the underlying pair as an honest probability measure on
`Real × Real` and identifies every continuous-linear projection of its
Banach-space characteristic function with that estimate.

This is the law-level interface needed by a two-dimensional Fejer--Esseen
inversion theorem.  In particular, the remaining inversion work no longer
has to know anything about the finite prime cube.
-/

/-- The centered two-height increment pair over a finite prime block. -/
noncomputable def harperTwoHeightPrimeBlockVector
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) (eta : Problem520.HarperPrimeCube y) : Real × Real :=
  (∑ p ∈ S, harperTwoHeightPrimeFluctuation p.1 t s t (eta p),
    ∑ p ∈ S, harperTwoHeightPrimeFluctuation p.1 t s s (eta p))

/-- The functional `(x,y) ↦ v*x + w*y`. -/
noncomputable def harperTwoHeightProjection (v w : Real) :
    StrongDual Real (Real × Real) :=
  v • ContinuousLinearMap.fst Real Real Real +
    w • ContinuousLinearMap.snd Real Real Real

@[simp] theorem harperTwoHeightProjection_apply
    (v w : Real) (x : Real × Real) :
    harperTwoHeightProjection v w x = v * x.1 + w * x.2 := by
  simp [harperTwoHeightProjection]

/-- Projecting the vector block gives exactly the scalar block sum used in
the characteristic calculation. -/
theorem harperTwoHeightProjection_blockVector
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s v w : Real) (eta : Problem520.HarperPrimeCube y) :
    harperTwoHeightProjection v w
        (harperTwoHeightPrimeBlockVector y S t s eta) =
      harperTwoHeightProjectedPrimeBlockSum y S t s v w eta := by
  simp only [harperTwoHeightProjection_apply,
    harperTwoHeightPrimeBlockVector,
    harperTwoHeightProjectedPrimeBlockSum,
    harperTwoHeightProjectedPrimeIncrement]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- The actual bivariate block law under the two-height tilt. -/
noncomputable def harperTwoHeightPrimeBlockVectorLaw
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) : Measure (Real × Real) :=
  Measure.map (harperTwoHeightPrimeBlockVector y S t s)
    (harperTwoHeightCubeLaw y t s)

instance harperTwoHeightPrimeBlockVectorLaw_isProbabilityMeasure
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) :
    IsProbabilityMeasure (harperTwoHeightPrimeBlockVectorLaw y S t s) := by
  unfold harperTwoHeightPrimeBlockVectorLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_of_finite _).aemeasurable

/-- The Banach-space characteristic function of the vector law is exactly
the previously estimated projected cube characteristic. -/
theorem charFunDual_harperTwoHeightPrimeBlockVectorLaw
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s v w : Real) :
    charFunDual (harperTwoHeightPrimeBlockVectorLaw y S t s)
        (harperTwoHeightProjection v w) =
      harperTwoHeightProjectedCubeCharacteristic y S t s v w := by
  rw [charFunDual_apply]
  unfold harperTwoHeightPrimeBlockVectorLaw
  rw [integral_map (measurable_of_finite _).aemeasurable (by fun_prop)]
  unfold harperTwoHeightProjectedCubeCharacteristic
  apply integral_congr_ae
  exact ae_of_all _ fun eta ↦ by
    change
      Complex.exp
          (((harperTwoHeightProjection v w
            (harperTwoHeightPrimeBlockVector y S t s eta) : Real) :
              Complex) * Complex.I) =
        Complex.exp
          (((harperTwoHeightProjectedPrimeBlockSum y S t s v w eta :
            Real) : Complex) * Complex.I)
    rw [harperTwoHeightProjection_blockVector]

/-- Law-level scheduled Cramer--Wold estimate.  This is now phrased entirely
in terms of the actual bivariate probability law and its exact covariance
quadratic form. -/
theorem norm_charFunDual_harperTwoHeightScheduledVectorLaw_sub_gaussian_le
    (y j : Nat) (t s v w : Real)
    (hfrequency :
      2 * (|v| + |w|) ≤
        Real.sqrt (Problem520.harperBlockEndpoint j : Real)) :
    ‖charFunDual
          (harperTwoHeightPrimeBlockVectorLaw y
            (Problem520.harperScheduledPrimeBlock y j) t s)
          (harperTwoHeightProjection v w) -
        Complex.exp
          (-((harperTwoHeightProjectedBlockVariance y
            (Problem520.harperScheduledPrimeBlock y j) t s v w / 2 :
              Real) : Complex))‖ ≤
      (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
        (16 * (|v| + |w|) ^ (3 : Nat) +
          2 * (|v| + |w|) ^ (4 : Nat)) := by
  rw [charFunDual_harperTwoHeightPrimeBlockVectorLaw]
  exact
    norm_harperTwoHeightScheduledProjectedCubeCharacteristic_sub_gaussian_le
      y j t s v w hfrequency

end
end Problem1144
end Erdos

#print axioms Erdos.Problem1144.harperTwoHeightProjection_blockVector
#print axioms Erdos.Problem1144.charFunDual_harperTwoHeightPrimeBlockVectorLaw
#print axioms Erdos.Problem1144.norm_charFunDual_harperTwoHeightScheduledVectorLaw_sub_gaussian_le
