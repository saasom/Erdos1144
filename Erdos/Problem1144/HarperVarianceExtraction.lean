import Erdos.Problem1144.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset
open scoped BigOperators

namespace Erdos
namespace Problem1144

/-!
# Extracting many variance-good points from an averaged lower bound

The Harperized endpoint-screen argument only needs an averaged prime-sampling
estimate.  Once the endpoint screen supplies a uniform upper bound, the
elementary reverse-averaging inequality below forces many points above a
chosen variance threshold.
-/

/-- A lower bound for a finite nonnegative average, together with a uniform
upper bound, forces many entries above any smaller threshold.  The statement
is deliberately real-valued so it can be used without rounding losses in the
later cardinality budget. -/
theorem card_filter_ge_lower_of_sum_lower_of_le
    {ι : Type*}
    (s : Finset ι) (f : ι → ℝ) {E v U : ℝ}
    (hUv : v < U)
    (hupper : ∀ i ∈ s, f i ≤ U)
    (hsum : E ≤ ∑ i ∈ s, f i) :
    (E - (s.card : ℝ) * v) / (U - v) ≤
      ((s.filter fun i => v ≤ f i).card : ℝ) := by
  classical
  let good : Finset ι := s.filter fun i => v ≤ f i
  have hpoint (i : ι) (hi : i ∈ s) :
      f i ≤ v + if v ≤ f i then U - v else 0 := by
    by_cases hgood : v ≤ f i
    · simp [hgood, hupper i hi]
    · simp [hgood, le_of_not_ge hgood]
  have havg :
      E ≤ (s.card : ℝ) * v + (good.card : ℝ) * (U - v) := by
    calc
      E ≤ ∑ i ∈ s, f i := hsum
      _ ≤ ∑ i ∈ s, (v + if v ≤ f i then U - v else 0) :=
        Finset.sum_le_sum fun i hi => hpoint i hi
      _ = (s.card : ℝ) * v + (good.card : ℝ) * (U - v) := by
        rw [Finset.sum_add_distrib]
        rw [← Finset.sum_filter]
        simp [good, mul_comm]
        ring
  rw [div_le_iff₀ (sub_pos.mpr hUv)]
  nlinarith

/-- Average form: if the mean is at least `a`, then at least the displayed
fraction of the points have value at least `v`. -/
theorem card_filter_ge_lower_of_average
    {ι : Type*}
    (s : Finset ι) (f : ι → ℝ) {a v U : ℝ}
    (hUv : v < U)
    (hupper : ∀ i ∈ s, f i ≤ U)
    (haverage : (s.card : ℝ) * a ≤ ∑ i ∈ s, f i) :
    (s.card : ℝ) * ((a - v) / (U - v)) ≤
      ((s.filter fun i => v ≤ f i).card : ℝ) := by
  have h := card_filter_ge_lower_of_sum_lower_of_le
    s f hUv hupper haverage
  calc
    (s.card : ℝ) * ((a - v) / (U - v)) =
        ((s.card : ℝ) * a - (s.card : ℝ) * v) / (U - v) := by ring
    _ ≤ ((s.filter fun i => v ≤ f i).card : ℝ) := h

end Problem1144
end Erdos
