import Erdos.Problem1144.HarperRankinGaussianFixedStart

open Finset MeasureTheory Measure ProbabilityTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Exact block independence under the Rankin tilt

The shifted tilted cube remains a product measure.  Hence centered sums over
disjoint scheduled prime blocks are independent, and their path vector has
exactly the product law used by the Gaussian ballot comparison.
-/

/-- Scheduled vector of shifted centered block increments. -/
noncomputable def harperRankinScheduledCenteredBlockVector
    (y start n : ℕ) (a t : ℝ) :
    Problem520.HarperPrimeCube y → (Fin n → ℝ) :=
  fun eta i =>
    harperRankinCenteredLinearPrimeBlockSum y
      (Problem520.harperScheduledPrimeBlock y (start + (i : ℕ)))
      a t t eta

/-- Shifted centered sums on disjoint scheduled blocks are mutually
independent under the shifted tilted cube. -/
theorem iIndepFun_harperRankinScheduledCenteredBlockSums
    (y start n : ℕ) (a t : ℝ) :
    iIndepFun
      (fun i : Fin n ↦
        harperRankinCenteredLinearPrimeBlockSum y
          (Problem520.harperScheduledPrimeBlock y (start + (i : ℕ)))
          a t t)
      (harperRankinTiltedCubeLaw y a t) := by
  let κ : Fin n → Type := fun i ↦
    {p : Problem520.HarperPrimeIndex y //
      p ∈ Problem520.harperScheduledPrimeBlock y (start + (i : ℕ))}
  let embed : (p : (i : Fin n) × κ i) → Problem520.HarperPrimeIndex y :=
    fun p ↦ p.2.1
  have hblocks : Pairwise fun i j : Fin n ↦
      Disjoint
        (Problem520.harperScheduledPrimeBlock y (start + (i : ℕ)))
        (Problem520.harperScheduledPrimeBlock y (start + (j : ℕ))) := by
    intro i j hij
    apply Problem520.disjoint_harperScheduledPrimeBlock y
    intro hs
    apply hij
    apply Fin.ext
    omega
  have hembed : Function.Injective embed := by
    rintro ⟨i, p⟩ ⟨j, q⟩ hpq
    change p.1 = q.1 at hpq
    by_cases hij : i = j
    · subst j
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext hpq))
    · exfalso
      apply (Finset.disjoint_left.mp (hblocks hij)) p.2
      rw [hpq]
      exact q.2
  have hflat : iIndepFun
      (fun p : (i : Fin n) × κ i ↦
        fun eta : Problem520.HarperPrimeCube y ↦ eta (embed p))
      (harperRankinTiltedCubeLaw y a t) :=
    iIndepFun.precomp hembed
      (iIndepFun_harperRankinTiltedCube_coordinates y a t)
  have hgroup : iIndepFun
      (fun i : Fin n ↦ fun eta : Problem520.HarperPrimeCube y ↦
        fun p : κ i ↦ eta p.1)
      (harperRankinTiltedCubeLaw y a t) := by
    simpa only [embed] using
      Problem520.iIndepFun_piCurry_of_iIndepFun
        (fun p : (i : Fin n) × κ i ↦
          fun eta : Problem520.HarperPrimeCube y ↦ eta (embed p))
        (fun _p ↦ measurable_of_finite _) hflat
  let blockSum : (i : Fin n) → (κ i → Bool) → ℝ :=
    fun i z ↦ ∑ p : κ i,
      harperRankinCenteredLinearPrimeIncrement p.1.1 a t t (z p)
  have hsum := hgroup.comp blockSum
    (fun _i ↦ measurable_of_finite _)
  apply hsum.congr
  intro i
  exact ae_of_all (harperRankinTiltedCubeLaw y a t) fun eta ↦ by
    change blockSum i (fun p : κ i ↦ eta p.1) =
      harperRankinCenteredLinearPrimeBlockSum y
        (Problem520.harperScheduledPrimeBlock y (start + (i : ℕ)))
        a t t eta
    unfold blockSum harperRankinCenteredLinearPrimeBlockSum
    exact Finset.sum_coe_sort
      (Problem520.harperScheduledPrimeBlock y (start + (i : ℕ)))
      (fun p ↦ harperRankinCenteredLinearPrimeIncrement p.1 a t t (eta p))

/-- Exact pushforward law of the shifted centered scheduled vector. -/
theorem map_harperRankinScheduledCenteredBlockVector_eq_pi
    (y start n : ℕ) (a t : ℝ) :
    Measure.map
        (harperRankinScheduledCenteredBlockVector y start n a t)
        (harperRankinTiltedCubeLaw y a t) =
      Measure.pi (fun i : Fin n ↦
        harperRankinCenteredLinearBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + (i : ℕ)))
          a t t) := by
  have hmeas : ∀ i : Fin n, Measurable
      (harperRankinCenteredLinearPrimeBlockSum y
        (Problem520.harperScheduledPrimeBlock y (start + (i : ℕ)))
        a t t) := fun _i ↦ measurable_of_finite _
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (fun i ↦ (hmeas i).aemeasurable)).mp
      (iIndepFun_harperRankinScheduledCenteredBlockSums y start n a t)
  simpa only [harperRankinScheduledCenteredBlockVector,
    harperRankinCenteredLinearBlockLaw] using h

theorem measurable_harperRankinScheduledCenteredBlockVector
    (y start n : ℕ) (a t : ℝ) :
    Measurable (harperRankinScheduledCenteredBlockVector y start n a t) := by
  exact measurable_of_finite _

/-- Every measurable path event has identical probability under the shifted
cube and the product of its shifted block marginals. -/
theorem harperRankinTiltedCubeLaw_real_preimage_centeredBlockVector_eq_pi
    (y start n : ℕ) (a t : ℝ)
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    (harperRankinTiltedCubeLaw y a t).real
        ((harperRankinScheduledCenteredBlockVector y start n a t) ⁻¹' A) =
      (Measure.pi (fun i : Fin n ↦
        harperRankinCenteredLinearBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + (i : ℕ)))
          a t t)).real A := by
  have hmap := map_measureReal_apply
    (μ := harperRankinTiltedCubeLaw y a t)
    (measurable_harperRankinScheduledCenteredBlockVector y start n a t) hA
  rw [map_harperRankinScheduledCenteredBlockVector_eq_pi] at hmap
  exact hmap.symm

/-- Literal shifted-cube logarithmic ballot event. -/
def harperRankinLogBallotCubeEvent
    (y start n : ℕ) (a t : ℝ) :
    Set (Problem520.HarperPrimeCube y) :=
  (harperRankinScheduledCenteredBlockVector y start n a t) ⁻¹'
    Problem520.harperPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start n)
      (harper1144LogBallotUpperBarrier n)

theorem measurableSet_harperRankinLogBallotCubeEvent
    (y start n : ℕ) (a t : ℝ) :
    MeasurableSet (harperRankinLogBallotCubeEvent y start n a t) := by
  unfold harperRankinLogBallotCubeEvent
  exact (Problem520.measurableSet_harperPartialSumBarrierSet _ _).preimage
    (measurable_harperRankinScheduledCenteredBlockVector y start n a t)

/-- Complete one-height lower bound on the literal Rankin-tilted prime cube. -/
theorem exists_gap_harperRankinLogBallotFixedStart_cube_lower
    (V : ℝ) (hV : 0 ≤ V) :
    ∃ gap J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n : ℕ, 0 < n →
      ∀ y : ℕ,
        Problem520.harperBlockEndpoint (start + n + gap) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            (3 / 16 : ℝ) *
                Real.exp
                  (-2 - harper1144GaussianLogFenceCertificateBudget) /
                  Real.sqrt (n : ℝ) ≤
              (harperRankinTiltedCubeLaw y
                (4 * V / Real.log (y : ℝ)) t).real
                (harperRankinLogBallotCubeEvent y start n
                  (4 * V / Real.log (y : ℝ)) t) := by
  obtain ⟨gap, J, hproduct⟩ :=
    exists_gap_harperRankinLogBallotFixedStart_product_lower V hV
  refine ⟨gap, J, ?_⟩
  intro start hstart n hn y hy t ht
  rw [harperRankinLogBallotCubeEvent,
    harperRankinTiltedCubeLaw_real_preimage_centeredBlockVector_eq_pi
      y start n (4 * V / Real.log (y : ℝ)) t
      (Problem520.harperPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start n)
        (harper1144LogBallotUpperBarrier n))
      (Problem520.measurableSet_harperPartialSumBarrierSet _ _)]
  exact hproduct start hstart n hn y hy t ht

/-- Critical-scale form of the shifted one-height theorem.  The terminal
Rankin gap only strengthens the endpoint hypothesis and does not change the
log-log normalization. -/
theorem exists_gap_harperRankinLogBallotFixedStart_cube_ge_criticalScale
    (V : ℝ) (hV : 0 ≤ V) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ gap J : ℕ,
      ∀ start : ℕ, J ≤ start → ∀ n y : ℕ, 0 < n → 4 ≤ y →
        Problem520.harperBlockEndpoint (start + n + gap) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            delta * harperInitialCriticalScale y ≤
              (harperRankinTiltedCubeLaw y
                (4 * V / Real.log (y : ℝ)) t).real
                (harperRankinLogBallotCubeEvent y start n
                  (4 * V / Real.log (y : ℝ)) t) := by
  obtain ⟨gap, J, hone⟩ :=
    exists_gap_harperRankinLogBallotFixedStart_cube_lower V hV
  let c : ℝ := (3 / 16 : ℝ) *
    Real.exp (-2 - harper1144GaussianLogFenceCertificateBudget)
  let delta : ℝ := c / 2
  refine ⟨delta, by dsimp only [delta, c]; positivity, gap, J, ?_⟩
  intro start hstart n y hn hy4 hendpoint t ht
  have hendpointBase :
      Problem520.harperBlockEndpoint (start + n) ≤ y :=
    (Problem520.monotone_harperBlockEndpoint (by omega)).trans hendpoint
  let L : ℝ := 1 + Problem520.logLogNat y
  have hL : 0 < L := by
    dsimp only [L]
    exact Problem520.one_add_logLogNat_pos_of_four_le hy4
  have hindex := half_index_le_logLogNat_of_harperBlockEndpoint_le
    hendpointBase
  have hnL : (n : ℝ) ≤ 4 * L := by
    push_cast at hindex
    have hstartR : 0 ≤ (start : ℝ) := by positivity
    have hnHalf : (n : ℝ) / 2 ≤ Problem520.logLogNat y := by
      nlinarith
    have hnR' : 0 < (n : ℝ) := by exact_mod_cast hn
    dsimp only [L]
    nlinarith
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt L := by
    calc
      Real.sqrt (n : ℝ) ≤ Real.sqrt (4 * L) :=
        Real.sqrt_le_sqrt hnL
      _ = 2 * Real.sqrt L := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
  have hinv : (2 * Real.sqrt L)⁻¹ ≤
      (Real.sqrt (n : ℝ))⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (Real.sqrt_pos.2 hnR) hsqrt
  have hcritical : harperInitialCriticalScale y / 2 ≤
      (Real.sqrt (n : ℝ))⁻¹ := by
    have hrewrite : harperInitialCriticalScale y = (Real.sqrt L)⁻¹ := by
      unfold harperInitialCriticalScale
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hL.le]
      congr 2
      ring
    rw [hrewrite]
    have hsqrtL : Real.sqrt L ≠ 0 := (Real.sqrt_pos.2 hL).ne'
    calc
      (Real.sqrt L)⁻¹ / 2 = (2 * Real.sqrt L)⁻¹ := by
        field_simp
      _ ≤ (Real.sqrt (n : ℝ))⁻¹ := hinv
  have hraw := hone start hstart n hn y hendpoint t ht
  calc
    delta * harperInitialCriticalScale y =
        c * (harperInitialCriticalScale y / 2) := by
      dsimp only [delta]
      ring
    _ ≤ c * (Real.sqrt (n : ℝ))⁻¹ := by
      gcongr
    _ = (3 / 16 : ℝ) *
          Real.exp (-2 - harper1144GaussianLogFenceCertificateBudget) /
            Real.sqrt (n : ℝ) := by
      dsimp only [c]
      rw [div_eq_mul_inv]
      ring
    _ ≤ _ := hraw

#print axioms
  Erdos.Problem1144.map_harperRankinScheduledCenteredBlockVector_eq_pi
#print axioms
  Erdos.Problem1144.harperRankinTiltedCubeLaw_real_preimage_centeredBlockVector_eq_pi
#print axioms
  Erdos.Problem1144.exists_gap_harperRankinLogBallotFixedStart_cube_lower
#print axioms
  Erdos.Problem1144.exists_gap_harperRankinLogBallotFixedStart_cube_ge_criticalScale

end

end Problem1144
end Erdos
