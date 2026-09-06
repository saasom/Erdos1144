import Erdos.Problem1144.Targets
import Erdos.Problem1144.PositiveProbabilityLimsup
import Mathlib.Probability.Martingale.BorelCantelli

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-- A block contains a positive normalized value at level `M j`. -/
def blockSuccess (X Y : ℕ → ℕ) (M : ℕ → ℝ) (omega : Omega) (j : ℕ) : Prop :=
  ∃ N ∈ Finset.Icc (X j) (Y j), M j ≤ normSum omega N

/-- Failure of the positive block event. -/
def blockFailure (X Y : ℕ → ℕ) (M : ℕ → ℝ) (j : ℕ) : Set Omega :=
  {omega | ¬ blockSuccess X Y M omega j}

/-- A checkable positive-block omega certificate.

If the block thresholds `M j` tend to infinity and the failure probabilities
are summable, then Borel-Cantelli turns block successes into the `Frequently`
form of Erdős #1144.
-/
structure PositiveBlockOmega where
  X : ℕ → ℕ
  Y : ℕ → ℕ
  M : ℕ → ℝ
  fail : ℕ → ℝ≥0∞
  X_tendsto : Tendsto X atTop atTop
  M_tendsto : Tendsto M atTop atTop
  fail_summable : (∑' j, fail j) ≠ ⊤
  prob_fail :
    ∀ j, mu (blockFailure X Y M j) ≤ fail j

/-- Positive block certificates imply Erdős #1144.

This is the pure measure/filter layer: the only probability input is the
summable bound on block failures, handled by the first Borel-Cantelli lemma.
-/
theorem erdos1144_of_positiveBlockOmega
    (h : PositiveBlockOmega) :
    Erdos1144 := by
  let F : ℕ → Set Omega := blockFailure h.X h.Y h.M
  have htsum : (∑' j, mu (F j)) ≠ ⊤ := by
    exact ne_top_of_le_ne_top h.fail_summable (ENNReal.tsum_le_tsum h.prob_fail)
  have hbc : mu (limsup F atTop) = 0 :=
    MeasureTheory.measure_limsup_atTop_eq_zero (μ := mu) (s := F) htsum
  have hnotlimsup : ∀ᵐ omega ∂mu, omega ∉ limsup F atTop := by
    rw [MeasureTheory.ae_iff]
    simpa using hbc
  filter_upwards [hnotlimsup] with omega homega A
  have hsucc_eventually :
      ∀ᶠ j : ℕ in atTop, blockSuccess h.X h.Y h.M omega j := by
    rw [Filter.mem_limsup_iff_frequently_mem] at homega
    simpa [F, blockFailure, Filter.Frequently] using homega
  rw [Filter.Frequently]
  intro hbad
  rw [eventually_atTop] at hbad
  rcases hbad with ⟨N0, hN0⟩
  have hMev : ∀ᶠ j : ℕ in atTop, A ≤ h.M j :=
    h.M_tendsto.eventually_ge_atTop A
  have hXev : ∀ᶠ j : ℕ in atTop, N0 ≤ h.X j :=
    h.X_tendsto.eventually_ge_atTop N0
  rcases (hsucc_eventually.and (hMev.and hXev)).exists with
    ⟨j, hsucc, hMj, hXj⟩
  rcases hsucc with ⟨N, hNmem, hMle⟩
  have hXleN : h.X j ≤ N := (Finset.mem_Icc.mp hNmem).1
  exact hN0 N (le_trans hXj hXleN) (le_trans hMj hMle)

/-! ## Conditional positive-probability closure -/

/-- A positive block-success event is measurable in the ambient product
sigma-algebra. -/
theorem measurableSet_blockSuccess
    (X Y : ℕ → ℕ) (M : ℕ → ℝ) (j : ℕ) :
    MeasurableSet {omega : Omega | blockSuccess X Y M omega j} := by
  rw [show {omega : Omega | blockSuccess X Y M omega j} =
      ⋃ N ∈ Finset.Icc (X j) (Y j),
        {omega : Omega | M j ≤ normSum omega N} by
    ext omega
    simp [blockSuccess]]
  exact Finset.measurableSet_biUnion _ fun N _hN =>
    measurableSet_le measurable_const (measurable_normSum N)

/-- Infinitely many successful positive blocks imply the pointwise target. -/
theorem positiveErdos1144Point_of_frequently_blockSuccess
    (X Y : ℕ → ℕ) (M : ℕ → ℝ)
    (hX : Tendsto X atTop atTop) (hM : Tendsto M atTop atTop)
    (omega : Omega)
    (hsuccess : ∃ᶠ j : ℕ in atTop, blockSuccess X Y M omega j) :
    ∀ A : ℝ, ∃ᶠ N : ℕ in atTop, A ≤ normSum omega N := by
  intro A
  rw [Filter.Frequently]
  intro hbad
  rw [eventually_atTop] at hbad
  rcases hbad with ⟨N₀, hN₀⟩
  have hMevent : ∀ᶠ j : ℕ in atTop, A ≤ M j :=
    hM.eventually_ge_atTop A
  have hXevent : ∀ᶠ j : ℕ in atTop, N₀ ≤ X j :=
    hX.eventually_ge_atTop N₀
  rcases (hsuccess.and_eventually (hMevent.and hXevent)).exists with
    ⟨j, hblock, hAj, hXj⟩
  rcases hblock with ⟨N, hNmem, hlarge⟩
  have hN₀N : N₀ ≤ N := hXj.trans (Finset.mem_Icc.mp hNmem).1
  exact hN₀ N hN₀N (hAj.trans hlarge)

/-- Lean-facing endpoint for the simplified fresh-block strategy.  Instead of
summably small failure, every next block only needs a fixed positive
conditional success probability given the current filtration. -/
structure ConditionalPositiveBlockOmega where
  X : ℕ → ℕ
  Y : ℕ → ℕ
  M : ℕ → ℝ
  ℱ : Filtration ℕ (inferInstance : MeasurableSpace Omega)
  lower : ℝ
  lower_pos : 0 < lower
  X_tendsto : Tendsto X atTop atTop
  M_tendsto : Tendsto M atTop atTop
  success_measurable :
    ∀ j, MeasurableSet[ℱ j]
      {omega : Omega | blockSuccess X Y M omega j}
  condExp_success_lower :
    ∀ j, ∀ᵐ omega ∂mu,
      lower ≤
        (mu[({omega : Omega | blockSuccess X Y M omega (j + 1)}).indicator
          (1 : Omega → ℝ) | ℱ j]) omega

/-- Lévy's conditional Borel--Cantelli theorem turns a conditional positive
block certificate directly into the one-sided Erdős #1144 target. -/
theorem erdos1144_of_conditionalPositiveBlockOmega
    (h : ConditionalPositiveBlockOmega) :
    Erdos1144 := by
  let E : ℕ → Set Omega :=
    fun j => {omega : Omega | blockSuccess h.X h.Y h.M omega j}
  have hsuccess : ∀ᵐ omega ∂mu, omega ∈ limsup E atTop :=
    ae_mem_limsup_atTop_of_condExp_indicator_uniform_lower
      h.ℱ E h.success_measurable h.lower_pos h.condExp_success_lower
  filter_upwards [hsuccess] with omega homega
  rw [Filter.mem_limsup_iff_frequently_mem] at homega
  exact positiveErdos1144Point_of_frequently_blockSuccess
    h.X h.Y h.M h.X_tendsto h.M_tendsto omega homega

end Problem1144
end Erdos
