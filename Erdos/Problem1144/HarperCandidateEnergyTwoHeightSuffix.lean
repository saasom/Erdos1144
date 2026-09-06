import Erdos.Problem1144.HarperCandidateEnergyTwoHeightPath
import Erdos.Problem520.HarperScheduledOffDiagonalBarrier

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

/-! Numerical suffix survival for the literal Rankin two-height ballot law. -/

theorem candidate_independentGaussianPairedBarrier_quarter_half_real_le
    (n : Nat) (hn : 0 < n)
    (variance₁ variance₂ : Fin n → NNReal)
    (lower upper : Fin n → Real)
    (a : Real) (ha : 0 ≤ a)
    (hupperBarrier : ∀ k, upper k ≤ a)
    (hlower₁ : ∀ i, (1 / 4 : NNReal) ≤ variance₁ i)
    (hupper₁ : ∀ i, variance₁ i ≤ (1 / 2 : NNReal))
    (hlower₂ : ∀ i, (1 / 4 : NNReal) ≤ variance₂ i)
    (hupper₂ : ∀ i, variance₂ i ≤ (1 / 2 : NNReal)) :
    (Measure.pi (fun i : Fin n ↦
      (gaussianReal 0 (variance₁ i)).prod
        (gaussianReal 0 (variance₂ i)))).real
        (harperPairedPartialSumBarrierSet lower upper) ≤
      4096 * (a + 2) ^ (2 : Nat) * (n : Real)⁻¹ := by
  let E : Set (Fin n → Real) :=
    Problem520.harperPartialSumBarrierSet lower upper
  let Q₁ : Measure (Fin n → Real) :=
    Measure.pi fun i : Fin n ↦ gaussianReal 0 (variance₁ i)
  let Q₂ : Measure (Fin n → Real) :=
    Measure.pi fun i : Fin n ↦ gaussianReal 0 (variance₂ i)
  let e := MeasurableEquiv.arrowProdEquivProdArrow Real Real (Fin n)
  have hmp : MeasurePreserving e
      (Measure.pi (fun i : Fin n ↦
        (gaussianReal 0 (variance₁ i)).prod
          (gaussianReal 0 (variance₂ i))))
      (Q₁.prod Q₂) := by
    exact measurePreserving_arrowProdEquivProdArrow Real Real (Fin n)
      (fun i ↦ gaussianReal 0 (variance₁ i))
      (fun i ↦ gaussianReal 0 (variance₂ i))
  have hpre : e ⁻¹' (E ×ˢ E) =
      harperPairedPartialSumBarrierSet lower upper := by
    ext z
    rfl
  have hmass :
      (Measure.pi (fun i : Fin n ↦
        (gaussianReal 0 (variance₁ i)).prod
          (gaussianReal 0 (variance₂ i)))).real
          (harperPairedPartialSumBarrierSet lower upper) =
        (Q₁.prod Q₂).real (E ×ˢ E) := by
    rw [← hmp.map_eq,
      map_measureReal_apply e.measurable
        ((Problem520.measurableSet_harperPartialSumBarrierSet lower upper).prod
          (Problem520.measurableSet_harperPartialSumBarrierSet lower upper)),
      hpre]
  have hsubset : E ⊆ Problem520.gaussianWalkSurvivalSet n a := by
    intro omega homega
    apply (gaussianWalkSurvives_iff_harperPathPartialSum_le
      n a omega).mpr
    intro k
    exact (Problem520.mem_harperPartialSumBarrierSet.mp homega k).2.trans
      (hupperBarrier k)
  have hQ₁ : Q₁.real E ≤
      64 * (a + 2) / Real.sqrt (n : Real) := by
    have hflat := Problem520.gaussianVarianceWalk_quarter_half_probability_le_fin
      n hn variance₁ (x := a) ha hlower₁ hupper₁
    exact (measureReal_mono hsubset).trans (by
      simpa only [Q₁] using hflat)
  have hQ₂ : Q₂.real E ≤
      64 * (a + 2) / Real.sqrt (n : Real) := by
    have hflat := Problem520.gaussianVarianceWalk_quarter_half_probability_le_fin
      n hn variance₂ (x := a) ha hlower₂ hupper₂
    exact (measureReal_mono hsubset).trans (by
      simpa only [Q₂] using hflat)
  have hproduct : (Q₁.prod Q₂).real (E ×ˢ E) =
      Q₁.real E * Q₂.real E := by
    simp only [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  rw [hmass, hproduct]
  calc
    Q₁.real E * Q₂.real E ≤
        (64 * (a + 2) / Real.sqrt (n : Real)) *
          (64 * (a + 2) / Real.sqrt (n : Real)) :=
      mul_le_mul hQ₁ hQ₂ measureReal_nonneg (by positivity)
    _ = 4096 * (a + 2) ^ (2 : Nat) * (n : Real)⁻¹ := by
      rw [div_mul_div_comm, ← pow_two (Real.sqrt (n : Real)),
        Real.sq_sqrt hnR.le]
      field_simp
      ring

/-- Quantitative conditional-suffix theorem for the literal two-height
ballot increments.  An arbitrary admissible corridor whose translated upper
barrier is at most `a` has probability at most a universal constant times
`(a+4)^2/n` once every suffix block lies beyond the decorrelation cutoff. -/
theorem candidate_rankinScheduledArbitraryBarrier_real_le
    (y start n : Nat) (σ : ℝ) (hσ : 0 ≤ σ) (t s : Real)
    (lower upper : Fin n → Real) (a : Real)
    (hn : 4 ≤ n) (ha : 0 ≤ a)
    (hupperBarrier : ∀ k, upper k ≤ a)
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
          σ s t s| ≤ 1 / (n : Real) ^ (2 : Nat))
    (hvarianceFirst : ∀ i : Fin n,
      (1 / 4 : Real) <
          harperRankinTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            σ hσ t s t t ∧
        harperRankinTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            σ hσ t s t t < (1 / 2 : Real))
    (hvarianceSecond : ∀ i : Fin n,
      (1 / 4 : Real) <
          harperRankinTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            σ hσ t s s s ∧
        harperRankinTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            σ hσ t s s s < (1 / 2 : Real)) :
    (Measure.pi (fun i : Fin n ↦
      candidateRankinTwoHeightBallotBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s)).real
        (harperPairedPartialSumBarrierSet lower upper) ≤
      5000 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹ := by
  let beta : Real :=
    ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
  let p : Real :=
    (Measure.pi (fun i : Fin n ↦
      candidateRankinTwoHeightBallotBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s)).real
        (harperPairedPartialSumBarrierSet lower upper)
  have hpath :=
    candidate_rankinScheduledArbitraryBarrierPath_le_independentGaussian
      y start n σ hσ t s lower upper hn hcorridor hfrequency hendpoint hcovariance
        hdriftFirst hdriftSecond
  dsimp only at hpath
  let variance₁ : Fin n → NNReal := fun i ↦
    candidateRankinTwoHeightCoordinateVarianceNNReal y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s t
  let variance₂ : Fin n → NNReal := fun i ↦
    candidateRankinTwoHeightCoordinateVarianceNNReal y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s s
  have hnPos : 0 < n := by omega
  have hnR : (4 : Real) ≤ n := by exact_mod_cast hn
  have hfive : 5 / (n : Real) ≤ 2 := by
    apply (div_le_iff₀ (by positivity : (0 : Real) < n)).mpr
    nlinarith
  have hupperRelax (k : Fin n) : upper k + 5 / (n : Real) ≤ a + 2 := by
    linarith [hupperBarrier k]
  have hlower₁ (i : Fin n) : (1 / 4 : NNReal) ≤ variance₁ i := by
    apply NNReal.coe_le_coe.mp
    change (1 / 4 : Real) ≤
      harperRankinTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s t t
    exact (hvarianceFirst i).1.le
  have hupper₁ (i : Fin n) : variance₁ i ≤ (1 / 2 : NNReal) := by
    apply NNReal.coe_le_coe.mp
    change harperRankinTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s t t ≤
      (1 / 2 : Real)
    exact (hvarianceFirst i).2.le
  have hlower₂ (i : Fin n) : (1 / 4 : NNReal) ≤ variance₂ i := by
    apply NNReal.coe_le_coe.mp
    change (1 / 4 : Real) ≤
      harperRankinTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s s s
    exact (hvarianceSecond i).1.le
  have hupper₂ (i : Fin n) : variance₂ i ≤ (1 / 2 : NNReal) := by
    apply NNReal.coe_le_coe.mp
    change harperRankinTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s s s ≤
      (1 / 2 : Real)
    exact (hvarianceSecond i).2.le
  have hgaussian := candidate_independentGaussianPairedBarrier_quarter_half_real_le
    n hnPos variance₁ variance₂
    (fun k ↦ lower k - 5 / (n : Real))
    (fun k ↦ upper k + 5 / (n : Real))
    (a + 2) (by linarith) hupperRelax
    hlower₁ hupper₁ hlower₂ hupper₂
  have hsum : a + 2 + 2 = a + 4 := by ring
  have hgaussian' :
      (Measure.pi (fun i : Fin n ↦
        candidateRankinTwoHeightIndependentGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s)).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ lower k - 5 / (n : Real))
            (fun k ↦ upper k + 5 / (n : Real))) ≤
        4096 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹ := by
    rw [hsum] at hgaussian
    simpa only [variance₁, variance₂,
      candidateRankinTwoHeightIndependentGaussianBlockLaw] using hgaussian
  have hweighted : beta ^ n * p ≤
      4096 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹ +
        6 / (n : Real) ^ (3 : Nat) := by
    dsimp only [beta, p]
    exact hpath.trans (add_le_add hgaussian' le_rfl)
  have hnPosR : (0 : Real) < n := by positivity
  have hnSq : (16 : Real) ≤ (n : Real) ^ (2 : Nat) := by
    nlinarith [sq_nonneg ((n : Real) - 4)]
  have hnLeCube : (n : Real) ≤ (n : Real) ^ (3 : Nat) := by
    have h1 : (1 : Real) ≤ (n : Real) ^ (2 : Nat) := by linarith
    calc
      (n : Real) = (n : Real) * 1 := by ring
      _ ≤ (n : Real) * (n : Real) ^ (2 : Nat) := by gcongr
      _ = (n : Real) ^ (3 : Nat) := by ring
  have herrSmall : 6 / (n : Real) ^ (3 : Nat) ≤ 6 / (n : Real) :=
    div_le_div_of_nonneg_left (by norm_num) hnPosR hnLeCube
  have haSq : (16 : Real) ≤ (a + 4) ^ (2 : Nat) := by
    nlinarith [sq_nonneg a]
  have hright :
      4096 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹ +
          6 / (n : Real) ^ (3 : Nat) ≤
        4375 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹ := by
    calc
      _ ≤ 4096 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹ +
          6 / (n : Real) := add_le_add le_rfl herrSmall
      _ = (4096 * (a + 4) ^ (2 : Nat) + 6) *
          (n : Real)⁻¹ := by ring
      _ ≤ (4375 * (a + 4) ^ (2 : Nat)) * (n : Real)⁻¹ := by
        gcongr
        nlinarith
      _ = _ := by ring
  have hretBase : (7 / 8 : Real) ≤
      1 - 8 / (n : Real) ^ (3 : Nat) := by
    have hden : 0 < (n : Real) ^ (3 : Nat) := by positivity
    have hnCube : (64 : Real) ≤ (n : Real) ^ (3 : Nat) := by
      calc
        (64 : Real) = (4 : Real) ^ (3 : Nat) := by norm_num
        _ ≤ (n : Real) ^ (3 : Nat) := by gcongr
    have hinv : 8 / (n : Real) ^ (3 : Nat) ≤ 1 / 8 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith
    linarith
  have hret : (7 / 8 : Real) ≤ beta ^ n :=
    hretBase.trans (by
      dsimp only [beta]
      exact one_sub_eight_div_cube_le_harperTwoHeightCutoff_retention
        (m := n) (n := n) (by omega) le_rfl)
  have hp0 : 0 ≤ p := by
    dsimp only [p]
    exact measureReal_nonneg
  have hweightedLower : (7 / 8 : Real) * p ≤ beta ^ n * p :=
    mul_le_mul_of_nonneg_right hret hp0
  have hpScaled : (7 / 8 : Real) * p ≤
      4375 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹ :=
    hweightedLower.trans (hweighted.trans hright)
  change p ≤ 5000 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹
  have hscaledTarget :
      (7 / 8 : Real) *
          (5000 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹) =
        4375 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹ := by
    ring
  exact (mul_le_mul_iff_right₀ (by norm_num : (0 : Real) < 7 / 8)).mp (by
    rw [hscaledTarget]
    exact hpScaled)


end Erdos.Problem1144
