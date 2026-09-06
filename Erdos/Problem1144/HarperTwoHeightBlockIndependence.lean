import Erdos.Problem1144.HarperTwoHeightVectorLaw
import Erdos.Problem520.HarperBlockIndependence

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Independence of the two-height scheduled block vectors

The explicit two-height tilt remains a product over prime signs.  Grouping
the signs into disjoint scheduled prime blocks therefore makes the centered
bivariate block increments mutually independent.  This file records both
the independence statement and the exact product-law identity needed by the
path replacement argument.
-/

/-- The bivariate centered increments over consecutive scheduled blocks are
mutually independent under the explicit two-height tilted cube law. -/
theorem iIndepFun_harperTwoHeightScheduledBlockVectors
    (y start n : Nat) (t s : Real) :
    iIndepFun
      (fun j : Fin n ↦ fun eta : Problem520.HarperPrimeCube y ↦
        harperTwoHeightPrimeBlockVector y
          (Problem520.harperScheduledPrimeBlock y (start + j.val)) t s eta)
      (harperTwoHeightCubeLaw y t s) := by
  let block : Fin n → Finset (Problem520.HarperPrimeIndex y) :=
    fun j ↦ Problem520.harperScheduledPrimeBlock y (start + j.val)
  let κ : Fin n → Type _ :=
    fun j ↦ {p : Problem520.HarperPrimeIndex y // p ∈ block j}
  let embed : (q : (j : Fin n) × κ j) →
      Problem520.HarperPrimeIndex y := fun q ↦ q.2.1
  have hembed : Function.Injective embed := by
    rintro ⟨i, p⟩ ⟨j, q⟩ hpq
    change p.1 = q.1 at hpq
    by_cases hij : i = j
    · subst j
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext hpq))
    · exfalso
      have hdisj : Disjoint (block i) (block j) := by
        dsimp only [block]
        apply Problem520.disjoint_harperScheduledPrimeBlock y
        intro hindex
        apply hij
        apply Fin.ext
        omega
      apply (Finset.disjoint_left.mp hdisj) p.2
      rw [hpq]
      exact q.2
  have hflat : iIndepFun
      (fun q : (j : Fin n) × κ j ↦
        fun eta : Problem520.HarperPrimeCube y ↦ eta (embed q))
      (harperTwoHeightCubeLaw y t s) :=
    (iIndepFun_harperTwoHeightCube_coordinates y t s).precomp hembed
  have hgroup : iIndepFun
      (fun j : Fin n ↦ fun eta : Problem520.HarperPrimeCube y ↦
        fun p : κ j ↦ eta p.1)
      (harperTwoHeightCubeLaw y t s) := by
    exact Problem520.iIndepFun_piCurry_of_iIndepFun
      (fun q : (j : Fin n) × κ j ↦
        fun eta : Problem520.HarperPrimeCube y ↦ eta (embed q))
      (fun _q ↦ measurable_of_finite _) hflat
  let blockVector : (j : Fin n) → (κ j → Bool) → Real × Real :=
    fun j z ↦
      (∑ p : κ j,
          harperTwoHeightPrimeFluctuation p.1.1 t s t (z p),
        ∑ p : κ j,
          harperTwoHeightPrimeFluctuation p.1.1 t s s (z p))
  have hcomp := hgroup.comp blockVector
    (fun _j ↦ measurable_of_finite _)
  apply hcomp.congr
  intro j
  exact ae_of_all (harperTwoHeightCubeLaw y t s) fun eta ↦ by
    unfold blockVector harperTwoHeightPrimeBlockVector
    change
      (∑ p : κ j,
          harperTwoHeightPrimeFluctuation p.1.1 t s t (eta p.1),
        ∑ p : κ j,
          harperTwoHeightPrimeFluctuation p.1.1 t s s (eta p.1)) =
      (∑ p ∈ Problem520.harperScheduledPrimeBlock y (start + j.val),
          harperTwoHeightPrimeFluctuation p.1 t s t (eta p),
        ∑ p ∈ Problem520.harperScheduledPrimeBlock y (start + j.val),
          harperTwoHeightPrimeFluctuation p.1 t s s (eta p))
    apply Prod.ext
    · exact Finset.sum_coe_sort
        (Problem520.harperScheduledPrimeBlock y (start + j.val))
        (fun p ↦ harperTwoHeightPrimeFluctuation p.1 t s t (eta p))
    · exact Finset.sum_coe_sort
        (Problem520.harperScheduledPrimeBlock y (start + j.val))
        (fun p ↦ harperTwoHeightPrimeFluctuation p.1 t s s (eta p))

/-- The full vector of consecutive two-height block increments has exactly
the finite product of its individual bivariate block laws. -/
theorem map_harperTwoHeightScheduledBlockVectors_eq_pi
    (y start n : Nat) (t s : Real) :
    Measure.map
        (fun eta : Problem520.HarperPrimeCube y ↦ fun j : Fin n ↦
          harperTwoHeightPrimeBlockVector y
            (Problem520.harperScheduledPrimeBlock y (start + j.val)) t s eta)
        (harperTwoHeightCubeLaw y t s) =
      Measure.pi (fun j : Fin n ↦
        harperTwoHeightPrimeBlockVectorLaw y
          (Problem520.harperScheduledPrimeBlock y (start + j.val)) t s) := by
  have hmeas : ∀ j : Fin n, Measurable
      (fun eta : Problem520.HarperPrimeCube y ↦
        harperTwoHeightPrimeBlockVector y
          (Problem520.harperScheduledPrimeBlock y (start + j.val)) t s eta) :=
    fun _j ↦ measurable_of_finite _
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (fun j ↦ (hmeas j).aemeasurable)).mp
      (iIndepFun_harperTwoHeightScheduledBlockVectors y start n t s)
  simpa only [harperTwoHeightPrimeBlockVectorLaw] using h

/-- Measurable path events can be evaluated either on the two-height cube or
under the exact product of scheduled bivariate block laws. -/
theorem harperTwoHeightCubeLaw_real_preimage_scheduledBlockVectors_eq_pi
    (y start n : Nat) (t s : Real)
    (A : Set (Fin n → Real × Real)) (hA : MeasurableSet A) :
    (harperTwoHeightCubeLaw y t s).real
        ((fun eta : Problem520.HarperPrimeCube y ↦ fun j : Fin n ↦
          harperTwoHeightPrimeBlockVector y
            (Problem520.harperScheduledPrimeBlock y (start + j.val))
              t s eta) ⁻¹' A) =
      (Measure.pi (fun j : Fin n ↦
        harperTwoHeightPrimeBlockVectorLaw y
          (Problem520.harperScheduledPrimeBlock y (start + j.val)) t s)).real
        A := by
  let F : Problem520.HarperPrimeCube y → Fin n → Real × Real :=
    fun eta j ↦
      harperTwoHeightPrimeBlockVector y
        (Problem520.harperScheduledPrimeBlock y (start + j.val)) t s eta
  have hF : Measurable F :=
    measurable_pi_iff.mpr fun _j ↦ measurable_of_finite _
  have hmap := map_measureReal_apply
    (μ := harperTwoHeightCubeLaw y t s)
    hF hA
  rw [map_harperTwoHeightScheduledBlockVectors_eq_pi] at hmap
  simpa only [F] using hmap.symm

#print axioms Erdos.Problem1144.iIndepFun_harperTwoHeightScheduledBlockVectors
#print axioms Erdos.Problem1144.map_harperTwoHeightScheduledBlockVectors_eq_pi
#print axioms Erdos.Problem1144.harperTwoHeightCubeLaw_real_preimage_scheduledBlockVectors_eq_pi

end

end Problem1144
end Erdos
