import Erdos.Problem1144.HarperCandidateCovarianceBarrierTailTilted
import Erdos.Problem1144.HarperCandidateCovarianceBarrierMoments
import Erdos.Problem1144.HarperCandidateCovarianceBarrierDeletionGaussian
import Erdos.Problem1144.HarperTwoHeightDeterministic
import Erdos.Problem1144.HarperLogBarrierBallot
import Erdos.Problem520.HarperMovingHeightUniformConstants

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

noncomputable section

/-!
# Literal Euler-prefix barriers

These events use the actual product over a consecutive prime range. Uniform
arithmetic drift and Taylor bounds translate them to the centered path to
which the proved tilted Gaussian comparison applies.
-/

/-- Log amplitude of the literal prime-prefix product, minus its tilted
linear drift `n log 2`. The square in each Euler factor accounts for `1/2`.
-/
def candidateEulerPrefixLog (y start n : ℕ) (t : ℝ)
    (η : Problem520.HarperPrimeCube y) : ℝ :=
  (1 / 2 : ℝ) * Real.log
    (∏ p ∈ Problem520.harperScheduledPrimeRangeFrom y start n,
      Problem520.harperCoordinateFactor p.1 t (η p)) - (n : ℝ) * Real.log 2

/-- Weak upper barriers at every prefix, together with a violation at prefix `j`
of a stronger upper barrier `x-r`. No centered random variable occurs here.
-/
def candidateEulerInternalBarrierEvent (y start n j : ℕ) (t x r : ℝ) :
    Set (Problem520.HarperPrimeCube y) :=
  {η | (∀ k : Fin n, candidateEulerPrefixLog y start (k.val + 1) t η ≤ x) ∧
    x - r ≤ candidateEulerPrefixLog y start j t η}

/-- Exact conversion of the finite Euler product to its sum of log factors. -/
theorem candidateEulerPrefixLog_eq (y start n : ℕ) (t : ℝ)
    (η : Problem520.HarperPrimeCube y) :
    candidateEulerPrefixLog y start n t η =
      Problem520.harperLogBlockSum y
        (Problem520.harperScheduledPrimeRangeFrom y start n) t η -
          (n : ℝ) * Real.log 2 := by
  unfold candidateEulerPrefixLog
  rw [Problem520.log_harperEulerBlockEnergy_eq_two_mul_logBlockSum]
  ring

private theorem taylorAllowance_le_one (start : ℕ) :
    (4 / 3 : ℝ) * (Real.sqrt (Problem520.harperBlockEndpoint start : ℝ))⁻¹ ≤ 1 := by
  have he : (16 : ℝ) ≤ Problem520.harperBlockEndpoint start := by
    exact_mod_cast Problem520.harperBlockEndpoint_ge_sixteen start
  have hs : (4 : ℝ) ≤ Real.sqrt (Problem520.harperBlockEndpoint start : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact Problem520.harperBlockEndpoint_ge_sixteen start
  have hpos : 0 < Real.sqrt (Problem520.harperBlockEndpoint start : ℝ) := by linarith
  rw [← div_eq_mul_inv, div_le_iff₀ hpos]
  linarith

private theorem prefixLog_close_of_drift (y start n : ℕ) (t D : ℝ)
    (hD : ∀ k : Fin n,
      |Problem520.harperLogMainBlockMean y
        (Problem520.harperScheduledPrimeRangeFrom y start (k.val + 1)) t t -
          ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤ D)
    (η : Problem520.HarperPrimeCube y) (k : Fin n) :
    |candidateEulerPrefixLog y start (k.val + 1) t η -
      Problem520.harperPathPartialSum
        (Problem520.harperScheduledCenteredBlockVectorVarying y start n t (fun _ => t) η) k| ≤
      D + 1 := by
  have hTaylor := (Problem520.abs_harperLogRangeFrom_sub_centered_add_mean_le
    y start (k.val + 1) t t η).trans (taylorAllowance_le_one start)
  rw [harper1144_centeredRangeFrom_eq_pathPartialSum y start n t η k] at hTaylor
  rw [candidateEulerPrefixLog_eq]
  have hd := hD k
  rw [abs_le] at hTaylor hd ⊢
  constructor <;> linarith [hTaylor.1, hTaylor.2, hd.1, hd.2]

/-- One numerical error constant controls the actual log-product path at
all moving noncentral heights and all shrinking central bands. The only
height loss is the explicit initial-block shift already proved in #520. -/
theorem candidate_exists_eulerPrefixLog_centered_close :
    ∃ C ≥ 0, ∃ J : ℕ,
      (∀ M start n y : ℕ, J + Nat.clog 2 (M + 1) ≤ start →
        Problem520.harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
        ∀ η : Problem520.HarperPrimeCube y, ∀ k : Fin n,
          |candidateEulerPrefixLog y start (k.val + 1) t η -
            Problem520.harperPathPartialSum
              (Problem520.harperScheduledCenteredBlockVectorVarying y start n t (fun _ => t) η) k| ≤ C) ∧
      (∀ d start n y : ℕ, J + d ≤ start →
        Problem520.harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, (1 / 2 : ℝ) ^ (d + 1) < |t| → |t| ≤ (1 / 2 : ℝ) ^ d →
        ∀ η : Problem520.HarperPrimeCube y, ∀ k : Fin n,
          |candidateEulerPrefixLog y start (k.val + 1) t η -
            Problem520.harperPathPartialSum
              (Problem520.harperScheduledCenteredBlockVectorVarying y start n t (fun _ => t) η) k| ≤ C) := by
  obtain ⟨E, hE, D, hD, J, hnoncentral, hcentral⟩ :=
    Problem520.exists_harperScheduledMovingAndCentralVerticalCumulativeUniformConstants
  obtain ⟨Jclose, hclose⟩ := exists_harperScheduledVerticalCumulativeDrift_diagonal_close
  refine ⟨D + 9 / 64 + 1, by positivity, max J Jclose, ?_, ?_⟩
  · intro M start n y hstart hy t htlo hthi η k
    apply prefixLog_close_of_drift y start n t (D + 9 / 64) ?_ η k
    intro i
    have hd := (hnoncentral M start n y (by omega) hy t htlo hthi i).2
    have hc := hclose start n y (by omega) hy t i
    rw [abs_le] at hd hc ⊢
    constructor <;> linarith [hd.1, hd.2, hc.1, hc.2]
  · intro d start n y hstart hy t htlo hthi η k
    apply prefixLog_close_of_drift y start n t (D + 9 / 64) ?_ η k
    intro i
    have hd := (hcentral d start n y (by omega) hy t htlo hthi i).2
    have hc := hclose start n y (by omega) hy t i
    rw [abs_le] at hd hc ⊢
    constructor <;> linarith [hd.1, hd.2, hc.1, hc.2]


/-- The prime-range product is exactly the ratio of the two full cutoff
Euler densities on the original sign space. -/
theorem candidateEulerPrefixLog_eq_full_density_ratio
    (y start n : ℕ) (hy : Problem520.harperBlockEndpoint (start + n) ≤ y)
    (ω : Problem520.Omega) (t : ℝ) :
    candidateEulerPrefixLog y start n t (Problem520.harperPrimeRestriction y ω) =
      (1 / 2 : ℝ) *
        (Real.log (Problem520.harperEulerDensity (Problem520.harperBlockEndpoint (start + n)) ω t) -
          Real.log (Problem520.harperEulerDensity (Problem520.harperBlockEndpoint start) ω t)) -
      (n : ℝ) * Real.log 2 := by
  classical
  let b := Problem520.harperBlockEndpoint start
  let c := Problem520.harperBlockEndpoint (start + n)
  have hbc : b ≤ c := Problem520.monotone_harperBlockEndpoint (by omega)
  let S : Finset (Problem520.HarperPrimeIndex y) := Finset.univ.filter (fun p => p.1 ≤ b)
  let T : Finset (Problem520.HarperPrimeIndex y) := Finset.univ.filter (fun p => p.1 ≤ c)
  have hST : S ⊆ T := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2.trans hbc⟩
  have hrange : Problem520.harperScheduledPrimeRangeFrom y start n = T \ S := by
    ext p
    simp only [Problem520.mem_harperScheduledPrimeRangeFrom, T, S, Finset.mem_sdiff,
      Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    exact and_comm
  have hfactor (p : Problem520.HarperPrimeIndex y) :
      Problem520.harperCoordinateFactor p.1 t (Problem520.harperPrimeRestriction y ω p) =
        Problem520.harperEulerFactor ω p.1 t := by
    simp [Problem520.harperCoordinateFactor, Problem520.harperEulerFactor,
      Problem520.harperPrimeRestriction, Problem520.ε]
  have hprod : (∏ p ∈ Problem520.harperScheduledPrimeRangeFrom y start n,
      Problem520.harperCoordinateFactor p.1 t (Problem520.harperPrimeRestriction y ω p)) *
      Problem520.harperEulerDensity b ω t = Problem520.harperEulerDensity c ω t := by
    rw [candidate_eulerDensity_eq_primeCube_prefix y b (hbc.trans hy),
      candidate_eulerDensity_eq_primeCube_prefix y c hy, hrange]
    simpa only [hfactor] using
      (Finset.prod_sdiff (f := fun p : Problem520.HarperPrimeIndex y =>
        Problem520.harperEulerFactor ω p.1 t) hST)
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul (Finset.prod_pos (fun p hp => by
    rw [hfactor]
    exact Problem520.harperEulerFactor_pos ω (Nat.prime_of_mem_primesBelow p.property) t)).ne'
    (Problem520.harperEulerDensity_pos b ω t).ne'] at hlog
  unfold candidateEulerPrefixLog
  change _ = (1 / 2 : ℝ) *
    (Real.log (Problem520.harperEulerDensity c ω t) -
      Real.log (Problem520.harperEulerDensity b ω t)) - (n : ℝ) * Real.log 2
  linarith

end

end Erdos.Problem1144
