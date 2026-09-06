import Erdos.Problem1144.HarperCandidateEnergyTwoHeightDrifted
import Erdos.Problem1144.HarperFiniteCoordinateReplacement

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

/-! Literal shifted paired-ballot paths: finite replacement and exact cube laws. -/

theorem candidate_rankinScheduledArbitraryBarrier_finiteReplacement
    (y start n : Nat) (σ : ℝ) (hσ : 0 ≤ σ) (t s : Real)
    (lower upper : Fin n → Real)
    (hn : 4 ≤ n)
    (hcorridor : ∀ i, upper i - lower i ≤ 64 * (n : Real) + 1)
    (hfrequency : ∀ i : Fin n,
      4 * (n : Real) ^ (6 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hendpoint : ∀ i : Fin n,
      1048576 * (n : Real) ^ (48 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hcovariance : ∀ i : Fin n,
      |harperRankinTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          σ hσ t s t s| ≤ 1 / (n : Real) ^ (40 : Nat)) :
    let beta : Real :=
      ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
    let expand : Real := 4 * (1 / (n : Real) ^ (2 : Nat))
    let err : Real := 6 / (n : Real) ^ (4 : Nat)
    let P : Fin n → Measure (Real × Real) := fun i ↦
      candidateRankinTwoHeightBallotBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s
    let Q : Fin n → Measure (Real × Real) := fun i ↦
      candidateRankinTwoHeightDriftedIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s
    beta ^ n * (Measure.pi P).real
        (harperPairedPartialSumBarrierSet lower upper) ≤
      (Measure.pi Q).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ lower k - (n : Real) * expand)
            (fun k ↦ upper k + (n : Real) * expand)) +
        (n : Real) * err := by
  dsimp only
  let beta : Real :=
    ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
  let expand : Real := 4 * (1 / (n : Real) ^ (2 : Nat))
  let err : Real := 6 / (n : Real) ^ (4 : Nat)
  let P : Fin n → Measure (Real × Real) := fun i ↦
    candidateRankinTwoHeightBallotBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s
  let Q : Fin n → Measure (Real × Real) := fun i ↦
    candidateRankinTwoHeightDriftedIndependentGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s
  have hfracNonneg : 0 ≤ 2 / (n : Real) ^ (4 : Nat) := by positivity
  have hnPow : (2 : Real) ≤ (n : Real) ^ (4 : Nat) := by
    have hnR : (4 : Real) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : Real) ^ (2 : Nat) - 1)]
  have hfracOne : 2 / (n : Real) ^ (4 : Nat) ≤ 1 := by
    exact (div_le_one (by positivity)).mpr hnPow
  have huLower : -1 ≤ 1 - 2 / (n : Real) ^ (4 : Nat) := by
    linarith
  have huUpper : 1 - 2 / (n : Real) ^ (4 : Nat) ≤ 1 := by
    linarith
  have huSq :
      (1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat) ≤ 1 := by
    nlinarith [sq_nonneg
      (1 - 2 / (n : Real) ^ (4 : Nat) - 1),
      sq_nonneg
      (1 - 2 / (n : Real) ^ (4 : Nat) + 1)]
  have hbeta0 : 0 ≤ beta := by
    dsimp only [beta]
    positivity
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    nlinarith [sq_nonneg
      ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat))]
  have herr : 0 ≤ err := by
    dsimp only [err]
    positivity
  have hexpand : 0 ≤ expand := by
    dsimp only [expand]
    positivity
  apply pi_harperPairedBarrier_finite_replacement
    P Q lower upper beta err expand (65 * (n : Real) - 1)
    hbeta0 hbeta1 herr hexpand
  · intro r hr
    let i : Fin n := ⟨r, hr⟩
    have hbase := hcorridor i
    have hrn : (r : Real) ≤ n := by
      exact_mod_cast (show r ≤ n by omega)
    have hsmall : 2 * (r : Real) * expand ≤ 2 := by
      dsimp only [expand]
      have hden : 0 < (n : Real) ^ (2 : Nat) := by positivity
      rw [show 2 * (r : Real) * (4 * (1 / (n : Real) ^ (2 : Nat))) =
        (8 * (r : Real)) / (n : Real) ^ (2 : Nat) by
          field_simp
          ring]
      apply (div_le_iff₀ hden).mpr
      have hnR : (4 : Real) ≤ n := by exact_mod_cast hn
      nlinarith
    have hnR : (4 : Real) ≤ n := by exact_mod_cast hn
    change upper i - lower i + 2 * (r : Real) * expand ≤
      65 * (n : Real) - 1
    nlinarith
  · intro i a b c d hab hcd habWidth hcdWidth
    dsimp only [P, Q, beta, expand, err]
    exact
      candidate_rankinScheduledBallotClosedRectangleMass_le_drifted_cutoff
        y (start + i.val) n σ hσ t s hn hab hcd habWidth hcdWidth
          (hfrequency i) (hendpoint i) (hcovariance i)



theorem candidate_rankinScheduledDriftedGaussianPath_real_le_independent_relaxed
    (y start n : Nat) (σ : ℝ) (hσ : 0 ≤ σ) (t s : Real) (hn : 1 ≤ n)
    (lower upper : Fin n → Real)
    (hdriftFirst : ∀ i : Fin n,
      |harperRankinTwoHeightCenteredBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          σ t s t| ≤ 1 / (n : Real) ^ (2 : Nat))
    (hdriftSecond : ∀ i : Fin n,
      |harperRankinTwoHeightCenteredBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          σ s t s| ≤ 1 / (n : Real) ^ (2 : Nat)) :
    (Measure.pi (fun i : Fin n ↦
      candidateRankinTwoHeightDriftedIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s)).real
        (harperPairedPartialSumBarrierSet lower upper) ≤
      (Measure.pi (fun i : Fin n ↦
        candidateRankinTwoHeightIndependentGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s)).real
        (harperPairedPartialSumBarrierSet
          (fun k ↦ lower k - 1 / (n : Real))
          (fun k ↦ upper k + 1 / (n : Real))) := by
  let G : Fin n → Measure (Real × Real) := fun i ↦
    candidateRankinTwoHeightIndependentGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s
  let d : Fin n → Real × Real := fun i ↦
    candidateRankinTwoHeightBallotBlockDrift y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ t s
  have hnPos : (0 : Real) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hprefix
      (coord : (Real × Real) → Real)
      (hcoord : ∀ i : Fin n, |coord (d i)| ≤
        1 / (n : Real) ^ (2 : Nat))
      (k : Fin n) :
      |∑ i ∈ Finset.Iic k, coord (d i)| ≤ 1 / (n : Real) := by
    calc
      |∑ i ∈ Finset.Iic k, coord (d i)| ≤
          ∑ i ∈ Finset.Iic k, |coord (d i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.Iic k,
          1 / (n : Real) ^ (2 : Nat) := by
        exact Finset.sum_le_sum fun i _hi ↦ hcoord i
      _ = ((k.val + 1 : Nat) : Real) *
          (1 / (n : Real) ^ (2 : Nat)) := by
        rw [Finset.sum_const, Fin.card_Iic, nsmul_eq_mul]
      _ ≤ (n : Real) * (1 / (n : Real) ^ (2 : Nat)) := by
        gcongr
        exact_mod_cast (show k.val + 1 ≤ n by omega)
      _ = 1 / (n : Real) := by field_simp
  have hfirst : ∀ k : Fin n,
      |∑ i ∈ Finset.Iic k, (d i).1| ≤ 1 / (n : Real) := by
    apply hprefix Prod.fst
    intro i
    exact hdriftFirst i
  have hsecond : ∀ k : Fin n,
      |∑ i ∈ Finset.Iic k, (d i).2| ≤ 1 / (n : Real) := by
    apply hprefix Prod.snd
    intro i
    exact hdriftSecond i
  have hmass := pi_translated_pairedBarrier_real_le_relaxed
    G d lower upper (1 / (n : Real)) hfirst hsecond
  simpa only [G, d, candidateRankinTwoHeightBallotBlockDrift,
    candidateRankinTwoHeightDriftedIndependentGaussianBlockLaw] using hmass

/-- End-to-end finite replacement for an arbitrary admissible corridor,
including deterministic drift removal.  This is the conditional-suffix form:
the barrier may already have been translated by an exposed prefix. -/
theorem candidate_rankinScheduledArbitraryBarrierPath_le_independentGaussian
    (y start n : Nat) (σ : ℝ) (hσ : 0 ≤ σ) (t s : Real)
    (lower upper : Fin n → Real)
    (hn : 4 ≤ n)
    (hcorridor : ∀ i, upper i - lower i ≤ 64 * (n : Real) + 1)
    (hfrequency : ∀ i : Fin n,
      4 * (n : Real) ^ (6 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hendpoint : ∀ i : Fin n,
      1048576 * (n : Real) ^ (48 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hcovariance : ∀ i : Fin n,
      |harperRankinTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          σ hσ t s t s| ≤ 1 / (n : Real) ^ (40 : Nat))
    (hdriftFirst : ∀ i : Fin n,
      |harperRankinTwoHeightCenteredBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          σ t s t| ≤ 1 / (n : Real) ^ (2 : Nat))
    (hdriftSecond : ∀ i : Fin n,
      |harperRankinTwoHeightCenteredBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          σ s t s| ≤ 1 / (n : Real) ^ (2 : Nat)) :
    let beta : Real :=
      ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
    let P : Fin n → Measure (Real × Real) := fun i ↦
      candidateRankinTwoHeightBallotBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s
    let G : Fin n → Measure (Real × Real) := fun i ↦
      candidateRankinTwoHeightIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s
    beta ^ n * (Measure.pi P).real
        (harperPairedPartialSumBarrierSet lower upper) ≤
      (Measure.pi G).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ lower k - 5 / (n : Real))
            (fun k ↦ upper k + 5 / (n : Real))) +
        6 / (n : Real) ^ (3 : Nat) := by
  dsimp only
  let beta : Real :=
    ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
  let expand : Real := 4 * (1 / (n : Real) ^ (2 : Nat))
  let err : Real := 6 / (n : Real) ^ (4 : Nat)
  let P : Fin n → Measure (Real × Real) := fun i ↦
    candidateRankinTwoHeightBallotBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s
  let Q : Fin n → Measure (Real × Real) := fun i ↦
    candidateRankinTwoHeightDriftedIndependentGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s
  let G : Fin n → Measure (Real × Real) := fun i ↦
    candidateRankinTwoHeightIndependentGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s
  have hreplace :=
    candidate_rankinScheduledArbitraryBarrier_finiteReplacement
      y start n σ hσ t s lower upper hn hcorridor hfrequency hendpoint hcovariance
  dsimp only at hreplace
  have hremove :=
    candidate_rankinScheduledDriftedGaussianPath_real_le_independent_relaxed
      y start n σ hσ t s (by omega)
      (fun k ↦ lower k - (n : Real) * expand)
      (fun k ↦ upper k + (n : Real) * expand)
      hdriftFirst hdriftSecond
  have htotalExpand : (n : Real) * expand + 1 / (n : Real) =
      5 / (n : Real) := by
    dsimp only [expand]
    field_simp
    ring
  have htotalErr : (n : Real) * err =
      6 / (n : Real) ^ (3 : Nat) := by
    dsimp only [err]
    field_simp
  have hlowerEq :
      (fun k : Fin n ↦
        (lower k - (n : Real) * expand) - 1 / (n : Real)) =
        fun k ↦ lower k - 5 / (n : Real) := by
    funext k
    rw [← htotalExpand]
    ring
  have hupperEq :
      (fun k : Fin n ↦
        (upper k + (n : Real) * expand) + 1 / (n : Real)) =
        fun k ↦ upper k + 5 / (n : Real) := by
    funext k
    rw [← htotalExpand]
    ring
  have hremove' :
      (Measure.pi Q).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ lower k - (n : Real) * expand)
            (fun k ↦ upper k + (n : Real) * expand)) ≤
        (Measure.pi G).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ lower k - 5 / (n : Real))
            (fun k ↦ upper k + 5 / (n : Real))) := by
    rw [hlowerEq, hupperEq] at hremove
    simpa only [Q, G] using hremove
  dsimp only [P, Q, G, beta, expand, err] at hreplace hremove' ⊢
  rw [htotalErr] at hreplace
  exact hreplace.trans (add_le_add hremove' le_rfl)



theorem candidate_iIndepFun_rankinScheduledBallotBlockVectors
    (y start n : Nat) (σ : ℝ) (hσ : 0 ≤ σ) (t s : Real) :
    iIndepFun
      (fun j : Fin n ↦ fun eta : Problem520.HarperPrimeCube y ↦
        candidateRankinTwoHeightBallotBlockVector y
          (Problem520.harperScheduledPrimeBlock y (start + j.val)) σ t s eta)
      (harperRankinTwoHeightCubeLaw y σ hσ t s) := by
  let F : (j : Fin n) → Problem520.HarperPrimeCube y → Real × Real :=
    fun j eta ↦ harperRankinTwoHeightPrimeBlockVector y
      (Problem520.harperScheduledPrimeBlock y (start + j.val)) σ t s eta
  let g : (j : Fin n) → Real × Real → Real × Real := fun j ↦
    harperPairTranslate
      (candidateRankinTwoHeightBallotBlockDrift y
        (Problem520.harperScheduledPrimeBlock y (start + j.val)) σ t s)
  have hjoint : iIndepFun F (harperRankinTwoHeightCubeLaw y σ hσ t s) := by
    exact iIndepFun_harperRankinTwoHeightScheduledBlockVectors y start n σ hσ t s
  have htranslated := hjoint.comp g fun j ↦
    measurable_harperPairTranslate _
  apply htranslated.congr
  intro j
  exact ae_of_all (harperRankinTwoHeightCubeLaw y σ hσ t s) fun eta ↦ by
    exact (candidate_rankinTwoHeightBallotBlockVector_eq_translate y
      (Problem520.harperScheduledPrimeBlock y (start + j.val)) σ t s eta).symm

/-- Hence the full literal ballot-increment vector has exactly the product of
the individual literal ballot block laws. -/
theorem candidate_map_rankinScheduledBallotBlockVectors_eq_pi
    (y start n : Nat) (σ : ℝ) (hσ : 0 ≤ σ) (t s : Real) :
    Measure.map
        (fun eta : Problem520.HarperPrimeCube y ↦ fun j : Fin n ↦
          candidateRankinTwoHeightBallotBlockVector y
            (Problem520.harperScheduledPrimeBlock y (start + j.val)) σ t s eta)
        (harperRankinTwoHeightCubeLaw y σ hσ t s) =
      Measure.pi (fun j : Fin n ↦
        candidateRankinTwoHeightBallotBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + j.val)) σ hσ t s) := by
  have hmeas : ∀ j : Fin n, Measurable
      (fun eta : Problem520.HarperPrimeCube y ↦
        candidateRankinTwoHeightBallotBlockVector y
          (Problem520.harperScheduledPrimeBlock y (start + j.val)) σ t s eta) :=
    fun _j ↦ measurable_of_finite _
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (fun j ↦ (hmeas j).aemeasurable)).mp
      (candidate_iIndepFun_rankinScheduledBallotBlockVectors y start n σ hσ t s)
  simpa only [candidateRankinTwoHeightBallotBlockLaw] using h

/-- Measurable paired path events may therefore be evaluated exactly either
on the two-height tilted sign cube or under the product of literal ballot
block laws. -/
theorem candidate_rankinCubeLaw_real_preimage_scheduledBallotBlockVectors_eq_pi
    (y start n : Nat) (σ : ℝ) (hσ : 0 ≤ σ) (t s : Real)
    (A : Set (Fin n → Real × Real)) (hA : MeasurableSet A) :
    (harperRankinTwoHeightCubeLaw y σ hσ t s).real
        ((fun eta : Problem520.HarperPrimeCube y ↦ fun j : Fin n ↦
          candidateRankinTwoHeightBallotBlockVector y
            (Problem520.harperScheduledPrimeBlock y (start + j.val))
              σ t s eta) ⁻¹' A) =
      (Measure.pi (fun j : Fin n ↦
        candidateRankinTwoHeightBallotBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + j.val)) σ hσ t s)).real
        A := by
  let F : Problem520.HarperPrimeCube y → Fin n → Real × Real :=
    fun eta j ↦ candidateRankinTwoHeightBallotBlockVector y
      (Problem520.harperScheduledPrimeBlock y (start + j.val)) σ t s eta
  have hF : Measurable F :=
    measurable_pi_iff.mpr fun _j ↦ measurable_of_finite _
  have hmap := map_measureReal_apply
    (μ := harperRankinTwoHeightCubeLaw y σ hσ t s) hF hA
  rw [candidate_map_rankinScheduledBallotBlockVectors_eq_pi] at hmap
  simpa only [F] using hmap.symm


/-- Exact identification with the same one-height-centered Rankin ballot graph. -/
theorem candidate_preimage_rankinScheduledBallotBlockVectors_pairedLogBarrier_eq_inter
    (y start n : ℕ) (σ t s : ℝ) :
    (fun eta : Problem520.HarperPrimeCube y ↦ fun j : Fin n ↦
      candidateRankinTwoHeightBallotBlockVector y
        (Problem520.harperScheduledPrimeBlock y (start + j.val)) σ t s eta) ⁻¹'
        harperPairedPartialSumBarrierSet
          (harper1144LogBallotLowerBarrier start n)
          (harper1144LogBallotUpperBarrier n) =
      harperRankinLogBallotCubeEvent y start n σ t ∩
        harperRankinLogBallotCubeEvent y start n σ s := by
  ext eta
  rfl

/-- The literal intersection under the joint shifted tilt satisfies the proved
Gaussian corridor comparison, including its deterministic centering drift. -/
theorem candidate_rankinCubeLogBallotPair_le_independentGaussian
    (y start n : Nat) (σ : ℝ) (hσ : 0 ≤ σ) (t s : Real)
    (hn : 4 ≤ n)
    (hfrequency : ∀ i : Fin n,
      4 * (n : Real) ^ (6 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hendpoint : ∀ i : Fin n,
      1048576 * (n : Real) ^ (48 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hcovariance : ∀ i : Fin n,
      |harperRankinTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          σ hσ t s t s| ≤ 1 / (n : Real) ^ (40 : Nat))
    (hdriftFirst : ∀ i : Fin n,
      |harperRankinTwoHeightCenteredBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          σ t s t| ≤ 1 / (n : Real) ^ (2 : Nat))
    (hdriftSecond : ∀ i : Fin n,
      |harperRankinTwoHeightCenteredBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          σ s t s| ≤ 1 / (n : Real) ^ (2 : Nat)) :
    let beta : Real :=
      ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
    let G : Fin n → Measure (Real × Real) := fun i ↦
      candidateRankinTwoHeightIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s
    beta ^ n * (harperRankinTwoHeightCubeLaw y σ hσ t s).real
        (harperRankinLogBallotCubeEvent y start n σ t ∩
          harperRankinLogBallotCubeEvent y start n σ s) ≤
      (Measure.pi G).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ harper1144LogBallotLowerBarrier start n k - 5 / (n : Real))
            (fun k ↦ harper1144LogBallotUpperBarrier n k + 5 / (n : Real))) +
        6 / (n : Real) ^ (3 : Nat) := by
  have h := candidate_rankinScheduledArbitraryBarrierPath_le_independentGaussian
    y start n σ hσ t s
    (harper1144LogBallotLowerBarrier start n) (harper1144LogBallotUpperBarrier n)
    hn (harper1144LogBallot_corridorWidth_le_add_one start n)
    hfrequency hendpoint hcovariance hdriftFirst hdriftSecond
  have hmass := candidate_rankinCubeLaw_real_preimage_scheduledBallotBlockVectors_eq_pi
    y start n σ hσ t s
    (harperPairedPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start n) (harper1144LogBallotUpperBarrier n))
    (measurableSet_harperPairedPartialSumBarrierSet _ _)
  rw [candidate_preimage_rankinScheduledBallotBlockVectors_pairedLogBarrier_eq_inter] at hmass
  dsimp only at h ⊢
  rw [hmass]
  exact h

end Erdos.Problem1144
