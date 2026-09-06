import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Martingale.BorelCantelli

open MeasureTheory Filter
open scoped ENNReal

namespace Erdos
namespace Problem1144

/-!
# Positive probability plus zero-one

The localized large-fluctuation argument does not need summably small failure
probabilities once its limsup success event is known to be a tail event.  A
uniform positive lower bound for the individual success probabilities already
gives the limsup event positive probability; a zero-one law then upgrades this
to probability one.
-/

/-- No independence is needed: if every event has measure at least `c`, then
the event that infinitely many of them occur also has measure at least `c`. -/
theorem measure_limsup_atTop_ge_of_uniform_lower
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (s : ℕ → Set α) (hs : ∀ n, MeasurableSet (s n)) {c : ℝ≥0∞}
    (hlower : ∀ n, c ≤ μ (s n)) :
    c ≤ μ (limsup s atTop) := by
  let U : ℕ → Set α := fun n => ⋃ i ≥ n, s i
  have hUmeas : ∀ n, MeasurableSet (U n) := by
    intro n
    exact MeasurableSet.iUnion fun i =>
      MeasurableSet.iUnion fun hi => hs i
  have hUanti : Antitone U := by
    intro n m hnm x hx
    simp only [U, Set.mem_iUnion] at hx ⊢
    rcases hx with ⟨i, hi, hxi⟩
    exact ⟨i, hnm.trans hi, hxi⟩
  have hUlower : ∀ n, c ≤ μ (U n) := by
    intro n
    refine (hlower n).trans (measure_mono ?_)
    intro x hx
    simp only [U, Set.mem_iUnion]
    exact ⟨n, le_rfl, hx⟩
  have htendsto := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => (hUmeas n).nullMeasurableSet) hUanti
    ⟨0, measure_ne_top μ (U 0)⟩
  have hinter : c ≤ μ (⋂ n, U n) :=
    ge_of_tendsto htendsto (Eventually.of_forall hUlower)
  simpa only [limsup_eq_iInf_iSup_of_nat, U] using hinter

/-- A zero-one law turns the preceding positive lower bound into full
measure. -/
theorem measure_limsup_atTop_eq_one_of_uniform_lower_of_zero_one
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    (s : ℕ → Set α) (hs : ∀ n, MeasurableSet (s n)) {c : ℝ≥0∞}
    (hc : c ≠ 0) (hlower : ∀ n, c ≤ μ (s n))
    (hzeroOne : μ (limsup s atTop) = 0 ∨ μ (limsup s atTop) = 1) :
    μ (limsup s atTop) = 1 := by
  rcases hzeroOne with hzero | hone
  · have hpositive := measure_limsup_atTop_ge_of_uniform_lower s hs hlower
    rw [hzero] at hpositive
    exact (hc (nonpos_iff_eq_zero.mp hpositive)).elim
  · exact hone

/-- Conditional positive probability is enough for infinitely many successes.
This is the uniform-lower-bound corollary of Lévy's generalized
Borel--Cantelli theorem. -/
theorem ae_mem_limsup_atTop_of_condExp_indicator_uniform_lower
    {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) (s : ℕ → Set α)
    (hs : ∀ n, MeasurableSet[ℱ n] (s n)) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ n, ∀ᵐ omega ∂μ,
      c ≤ (μ[(s (n + 1)).indicator (1 : α → ℝ) | ℱ n]) omega) :
    ∀ᵐ omega ∂μ, omega ∈ limsup s atTop := by
  have hlevy := MeasureTheory.ae_mem_limsup_atTop_iff μ hs
  have hall : ∀ᵐ omega ∂μ, ∀ n,
      c ≤ (μ[(s (n + 1)).indicator (1 : α → ℝ) | ℱ n]) omega :=
    ae_all_iff.mpr hlower
  filter_upwards [hlevy, hall] with omega homega hlowerOmega
  apply homega.mpr
  refine Filter.tendsto_atTop_mono' atTop
    (f₁ := fun n : ℕ => (n : ℝ) * c) ?_ ?_
  · filter_upwards [] with n
    calc
      (n : ℝ) * c = ∑ _k ∈ Finset.range n, c := by
        simp [nsmul_eq_mul]
      _ ≤ ∑ k ∈ Finset.range n,
          (μ[(s (k + 1)).indicator (1 : α → ℝ) | ℱ k]) omega :=
        Finset.sum_le_sum fun k _hk => hlowerOmega k
  · simpa [mul_comm] using
      tendsto_natCast_atTop_atTop.const_mul_atTop hc

end Problem1144
end Erdos
