import Erdos.Problem1144.HarperRankinTwoHeightVectorLaw
import Erdos.Problem520.HarperBlockIndependence

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Independence of shifted two-height scheduled block vectors
-/

theorem iIndepFun_harperRankinTwoHeightScheduledBlockVectors
    (y start n : ℕ) (a : ℝ) (ha : 0 ≤ a) (t s : ℝ) :
    iIndepFun
      (fun j : Fin n ↦ fun eta : Problem520.HarperPrimeCube y ↦
        harperRankinTwoHeightPrimeBlockVector y
          (Problem520.harperScheduledPrimeBlock y (start + j.val))
          a t s eta)
      (harperRankinTwoHeightCubeLaw y a ha t s) := by
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
      (harperRankinTwoHeightCubeLaw y a ha t s) :=
    (iIndepFun_harperRankinTwoHeightCube_coordinates y a ha t s).precomp
      hembed
  have hgroup : iIndepFun
      (fun j : Fin n ↦ fun eta : Problem520.HarperPrimeCube y ↦
        fun p : κ j ↦ eta p.1)
      (harperRankinTwoHeightCubeLaw y a ha t s) := by
    exact Problem520.iIndepFun_piCurry_of_iIndepFun
      (fun q : (j : Fin n) × κ j ↦
        fun eta : Problem520.HarperPrimeCube y ↦ eta (embed q))
      (fun _q ↦ measurable_of_finite _) hflat
  let blockVector : (j : Fin n) → (κ j → Bool) → ℝ × ℝ :=
    fun j z ↦
      (∑ p : κ j,
          harperRankinTwoHeightPrimeFluctuation
            p.1.1 a t s t (z p),
        ∑ p : κ j,
          harperRankinTwoHeightPrimeFluctuation
            p.1.1 a t s s (z p))
  have hcomp := hgroup.comp blockVector
    (fun _j ↦ measurable_of_finite _)
  apply hcomp.congr
  intro j
  exact ae_of_all (harperRankinTwoHeightCubeLaw y a ha t s) fun eta ↦ by
    unfold blockVector harperRankinTwoHeightPrimeBlockVector
    change
      (∑ p : κ j,
          harperRankinTwoHeightPrimeFluctuation
            p.1.1 a t s t (eta p.1),
        ∑ p : κ j,
          harperRankinTwoHeightPrimeFluctuation
            p.1.1 a t s s (eta p.1)) =
      (∑ p ∈ Problem520.harperScheduledPrimeBlock y (start + j.val),
          harperRankinTwoHeightPrimeFluctuation
            p.1 a t s t (eta p),
        ∑ p ∈ Problem520.harperScheduledPrimeBlock y (start + j.val),
          harperRankinTwoHeightPrimeFluctuation
            p.1 a t s s (eta p))
    apply Prod.ext
    · exact Finset.sum_coe_sort
        (Problem520.harperScheduledPrimeBlock y (start + j.val))
        (fun p ↦ harperRankinTwoHeightPrimeFluctuation
          p.1 a t s t (eta p))
    · exact Finset.sum_coe_sort
        (Problem520.harperScheduledPrimeBlock y (start + j.val))
        (fun p ↦ harperRankinTwoHeightPrimeFluctuation
          p.1 a t s s (eta p))

theorem map_harperRankinTwoHeightScheduledBlockVectors_eq_pi
    (y start n : ℕ) (a : ℝ) (ha : 0 ≤ a) (t s : ℝ) :
    Measure.map
        (fun eta : Problem520.HarperPrimeCube y ↦ fun j : Fin n ↦
          harperRankinTwoHeightPrimeBlockVector y
            (Problem520.harperScheduledPrimeBlock y (start + j.val))
            a t s eta)
        (harperRankinTwoHeightCubeLaw y a ha t s) =
      Measure.pi (fun j : Fin n ↦
        harperRankinTwoHeightPrimeBlockVectorLaw y
          (Problem520.harperScheduledPrimeBlock y (start + j.val))
          a ha t s) := by
  have hmeas : ∀ j : Fin n, Measurable
      (fun eta : Problem520.HarperPrimeCube y ↦
        harperRankinTwoHeightPrimeBlockVector y
          (Problem520.harperScheduledPrimeBlock y (start + j.val))
          a t s eta) := fun _j ↦ measurable_of_finite _
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (fun j ↦ (hmeas j).aemeasurable)).mp
      (iIndepFun_harperRankinTwoHeightScheduledBlockVectors
        y start n a ha t s)
  simpa only [harperRankinTwoHeightPrimeBlockVectorLaw] using h

theorem harperRankinTwoHeightCubeLaw_real_preimage_scheduledBlockVectors_eq_pi
    (y start n : ℕ) (a : ℝ) (ha : 0 ≤ a) (t s : ℝ)
    (A : Set (Fin n → ℝ × ℝ)) (hA : MeasurableSet A) :
    (harperRankinTwoHeightCubeLaw y a ha t s).real
        ((fun eta : Problem520.HarperPrimeCube y ↦ fun j : Fin n ↦
          harperRankinTwoHeightPrimeBlockVector y
            (Problem520.harperScheduledPrimeBlock y (start + j.val))
              a t s eta) ⁻¹' A) =
      (Measure.pi (fun j : Fin n ↦
        harperRankinTwoHeightPrimeBlockVectorLaw y
          (Problem520.harperScheduledPrimeBlock y (start + j.val))
            a ha t s)).real A := by
  let F : Problem520.HarperPrimeCube y → Fin n → ℝ × ℝ :=
    fun eta j ↦ harperRankinTwoHeightPrimeBlockVector y
      (Problem520.harperScheduledPrimeBlock y (start + j.val))
      a t s eta
  have hF : Measurable F :=
    measurable_pi_iff.mpr fun _j ↦ measurable_of_finite _
  have hmap := map_measureReal_apply
    (μ := harperRankinTwoHeightCubeLaw y a ha t s) hF hA
  rw [map_harperRankinTwoHeightScheduledBlockVectors_eq_pi] at hmap
  simpa only [F] using hmap.symm

#print axioms Erdos.Problem1144.iIndepFun_harperRankinTwoHeightScheduledBlockVectors
#print axioms Erdos.Problem1144.map_harperRankinTwoHeightScheduledBlockVectors_eq_pi
#print axioms Erdos.Problem1144.harperRankinTwoHeightCubeLaw_real_preimage_scheduledBlockVectors_eq_pi

end
end Problem1144
end Erdos
