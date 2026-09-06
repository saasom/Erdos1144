import Erdos.Problem1144.HarperCandidateGaussianConditional
import Erdos.Problem1144.HarperCandidateScheduleAssembly
import Mathlib.Data.Finset.Sort

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-- The common fresh-prime union on one literal scheduled grid. -/
noncomputable def candidateScheduledFreshPrimes (α κ T : ℝ) (k : ℕ) (shift : ℝ) :
    Finset ℕ :=
  candidateGridFreshPrimes (candidateScheduleX T)
    (fun i : Fin (candidateScheduleM κ T) =>
      ⌊Real.exp (candidateSchedulePoint α κ T k i shift)⌋₊)

/-- Increasing enumeration fixes the finite Gaussian noise coordinates
without making any choices dependent on the old sign world. -/
noncomputable def candidateScheduledFreshPrime (α κ T : ℝ) (k : ℕ) (shift : ℝ) :
    Fin (candidateScheduledFreshPrimes α κ T k shift).card ↪o ℕ :=
  (candidateScheduledFreshPrimes α κ T k shift).orderEmbOfFin rfl

theorem candidateScheduledFreshPrime_image (α κ T : ℝ) (k : ℕ) (shift : ℝ) :
    Finset.univ.image (candidateScheduledFreshPrime α κ T k shift) =
      candidateScheduledFreshPrimes α κ T k shift :=
  Finset.image_orderEmbOfFin_univ _ rfl

/-- The Gaussianized complete fresh field on the actual candidate grid. -/
noncomputable def candidateScheduledGaussianFresh
    (omega : Omega) (α κ T : ℝ) (k : ℕ) (shift : ℝ)
    (v : Fin (candidateScheduledFreshPrimes α κ T k shift).card → ℝ)
    (i : Fin (candidateScheduleM κ T)) : ℝ :=
  ∑ p, (S omega (⌊Real.exp (candidateSchedulePoint α κ T k i shift)⌋₊ /
      candidateScheduledFreshPrime α κ T k shift p) /
      Real.exp (candidateSchedulePoint α κ T k i shift / 2)) * v p

/-- The precise remaining Gaussian crossing input. The finite noise law and
all coefficients are literal; the selector is the actual old-field selector.
The fixed-cylinder lower mass is uniform over deterministic blocks and shifts. -/
def CandidateScheduledGaussianRobustCrossingStatement (α β κ ρ p0 : ℝ) : Prop :=
  ∀ (s : Finset ℕ) (eta : s → Bool) (b K ε : ℝ), 0 < K → 0 < ε →
    ∀ᶠ T : ℝ in atTop, ∀ k < candidateScheduleN α β κ T,
      ∀ shift ∈ Ioc (0 : ℝ) (2 * Real.pi),
      p0 - ε ≤ ∫ omega,
        (Measure.pi (fun _ : Fin (candidateScheduledFreshPrimes α κ T k shift).card =>
          gaussianReal 0 1)).real
          {v | ∃ i ∈ candidateRetainedIndices
            (fun omega (i : Fin (candidateScheduleM κ T)) =>
              harperCandidateLogOld omega (candidateScheduleX T)
                (candidateSchedulePoint α κ T k i shift)) b ρ omega,
            K ≤ |candidateScheduledGaussianFresh omega α κ T k shift v i|}
          ∂candidateCylinderLaw s eta

/-- The schedule has at most a linear number of grid points eventually.
This follows from its exact floor once the slowly growing weight exceeds one. -/
theorem candidateScheduleM_eventually_le_time {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, (candidateScheduleM κ T : ℝ) ≤ T := by
  filter_upwards [(candidateScheduleW_tendsto hκ).eventually_ge_atTop 1,
    eventually_ge_atTop (0 : ℝ)] with T hW hT
  have hD : 0 ≤ candidateScheduleD κ T := by unfold candidateScheduleD; positivity
  calc
    _ ≤ candidateScheduleD κ T / (2 * Real.pi) :=
      Nat.floor_le (by positivity)
    _ ≤ candidateScheduleD κ T := div_le_self hD (by linarith [Real.pi_gt_three])
    _ ≤ T := div_le_self hT (by nlinarith [sq_nonneg (candidateScheduleW κ T - 1)])

/-- The proved multivariate replacement error vanishes on the actual
schedule; its cubic grid factor is absorbed by the strict exponent gap. -/
theorem candidateSchedule_gaussian_replacement_error_tendsto_zero
    {κ β : ℝ} (hκ : 0 < κ) (hβ : β < 4 / 3) (C : ℝ) :
    Tendsto (fun T => C * (candidateScheduleM κ T : ℝ) ^ 3 *
      Real.exp ((3 * β / 2 - 2) * T)) atTop (𝓝 0) := by
  have hz : Tendsto (fun T => (candidateScheduleM κ T : ℝ) ^ 3 *
      Real.exp ((3 * β / 2 - 2) * T)) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (candidate_polynomial_cubic_budget_tendsto_zero hβ 3)
    · exact Eventually.of_forall fun T => by positivity
    · filter_upwards [candidateScheduleM_eventually_le_time hκ] with T hT
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hT 3) (Real.exp_pos _).le
  simpa only [mul_zero, mul_assoc] using hz.const_mul C

/-- The closed replacement chain transfers the scheduled Gaussian lower
mass with no fixed loss. Half of the requested error is assigned to Gaussian
crossing and half to the vanishing replacement error. -/
theorem candidateScheduledRobustCrossing_of_gaussian
    {α β κ ρ p0 : ℝ} (hα : 1 < α) (hαβ : α < β) (hβ : β < 4 / 3)
    (hκ : 0 < κ)
    (hGaussian : CandidateScheduledGaussianRobustCrossingStatement α β κ ρ p0) :
    CandidateScheduledRobustCrossingStatement α β κ ρ p0 := by
  intro s eta b K ε hK hε
  obtain ⟨C, _, hcompare⟩ :=
    candidate_conditional_logFresh_max_comparison hK (δ := 1) (by norm_num)
  have herror := (candidateSchedule_gaussian_replacement_error_tendsto_zero hκ hβ C).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
  filter_upwards [hGaussian s eta b (K + 1) (ε / 2) (by linarith) (by positivity),
    herror, candidateSchedule_eventually_prefix s,
    candidateSchedule_eventually_cutoff_square (show β < 2 by linarith),
    eventually_ge_atTop (Real.log 2), eventually_ge_atTop (0 : ℝ)]
    with T hG hErr hs hcut hT hT0
  intro k hk shift hshift
  let u : Fin (candidateScheduleM κ T) → ℝ :=
    fun i => candidateSchedulePoint α κ T k i shift
  let q := candidateScheduledFreshPrime α κ T k shift
  have hpoints (i : Fin (candidateScheduleM κ T)) :
      u i ∈ Ioc (α * T) (β * T) := by
    exact candidate_grid_point_mem_window (by positivity)
      (candidateSchedule_cover hαβ.le hT0) hk i.isLt hshift
  have hu (i : Fin (candidateScheduleM κ T)) : u i ≤ β * T := (hpoints i).2
  have hposcut (i : Fin (candidateScheduleM κ T)) :
      0 ≤ u i ∧ ⌊Real.exp (u i)⌋₊ < ⌊Real.exp T⌋₊ ^ 2 :=
    ⟨(mul_nonneg (by linarith : 0 ≤ α) hT0).trans (hpoints i).1.le,
      hcut (u i) (hu i)⟩
  have hc := hcompare (candidateScheduledFreshPrimes α κ T k shift).card
    (candidateScheduleM κ T) s eta u q T β b ρ q.injective hT hs
    (candidateScheduledFreshPrime_image α κ T k shift) hposcut hu
  have hg := hG k hk shift hshift
  have hchain := hg.trans hc
  dsimp only [u, candidateScheduleX] at hchain ⊢
  linarith

/-- The cylinder reduction, sign replacement, and schedule steps are closed.
The remaining analytic hypothesis is the explicitly stated robust Gaussian
crossing for the actual fresh-coefficient process. -/
theorem erdos1144_of_candidateScheduledGaussianRobustCrossing
    {α β κ ρ p0 : ℝ} (hα : 1 < α) (hαβ : α < β) (hβ : β < 4 / 3)
    (hκ : 0 < κ) (hρ : ρ < 1) (hp0 : 0 < p0)
    (hGaussian : CandidateScheduledGaussianRobustCrossingStatement α β κ ρ p0) :
    Erdos1144 :=
  erdos1144_of_candidateScheduledRobustCrossing hα hαβ hβ hκ hρ hp0
    (candidateScheduledRobustCrossing_of_gaussian hα hαβ hβ hκ hGaussian)

end Erdos.Problem1144
