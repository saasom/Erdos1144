import Erdos.Problem1144.HarperGaussianLogBallotTilt
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.PSeries

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# A summable lower fence for the logarithmic Gaussian tilt

The Cameron--Martin reduction in `HarperGaussianLogBallotTilt` leaves one
scalar likelihood condition.  This file supplies its deterministic core.
If every prefix of the original flat walk stays above

`-K * (k+1)^(3/4)`,

then Abel summation bounds the inverse-time likelihood uniformly in the path
length.  The budget is a fixed convergent `p`-series.  This turns the remaining
one-height probability theorem into the assertion that a flat Gaussian ballot
retains order `n^(-1/2)` mass after imposing this auxiliary lower fence.
-/

/-- The sublinear power used by the auxiliary lower fence. -/
def harper1144GaussianLogFencePower (m : Nat) : Real :=
  ((m : Real) ^ (3 / 4 : Real))

/-- A flat path with this property has a uniformly controlled logarithmic
tilt likelihood. -/
def harper1144GaussianLogAuxFenceEvent (n : Nat) (K : Real) :
    Set (Fin n -> Real) :=
  {omega | ∀ k : Fin n,
    -K * harper1144GaussianLogFencePower (k.val + 1) <=
      Problem520.harperPathPartialSum omega k}

theorem measurableSet_harper1144GaussianLogAuxFenceEvent
    (n : Nat) (K : Real) :
    MeasurableSet (harper1144GaussianLogAuxFenceEvent n K) := by
  rw [show harper1144GaussianLogAuxFenceEvent n K =
      ⋂ k : Fin n, {omega : Fin n -> Real |
        -K * harper1144GaussianLogFencePower (k.val + 1) <=
          Problem520.harperPathPartialSum omega k} by
    ext omega
    simp only [harper1144GaussianLogAuxFenceEvent, Set.mem_setOf_eq,
      Set.mem_iInter]]
  apply MeasurableSet.iInter
  intro k
  unfold Problem520.harperPathPartialSum
  exact measurableSet_le measurable_const
    (Finset.measurable_sum _ fun i _hi => measurable_pi_apply i)

/-- The likelihood linear form of a translated path is the original linear
form minus the Cameron--Martin energy. -/
theorem harper1144GaussianLogTiltLinear_tiltDown
    {n : Nat} (variance : Fin n -> NNReal) (omega : Fin n -> Real) :
    harper1144GaussianLogTiltLinear
        (harper1144GaussianLogTiltDown variance omega) =
      harper1144GaussianLogTiltLinear omega -
        harper1144GaussianLogTiltEnergy variance := by
  unfold harper1144GaussianLogTiltLinear
    harper1144GaussianLogTiltDown harper1144GaussianLogTiltIncrement
    harper1144GaussianLogTiltEnergy
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Nat-indexed version of the logarithmic tilt rate. -/
def harper1144GaussianLogTiltRateNat (i : Nat) : Real :=
  8 / ((i + 1 : Nat) : Real)

theorem harper1144GaussianLogTiltRate_eq_nat
    {n : Nat} (i : Fin n) :
    harper1144GaussianLogTiltRate i =
      harper1144GaussianLogTiltRateNat i.val := rfl

/-- Extend a finite increment vector by zero outside its range. -/
def harper1144GaussianZeroExtend {n : Nat}
    (omega : Fin n -> Real) (i : Nat) : Real :=
  if hi : i < n then omega ⟨i, hi⟩ else 0

/-- Prefix sum of the zero-extended increment vector. -/
def harper1144GaussianPrefixNat {n : Nat}
    (omega : Fin n -> Real) (m : Nat) : Real :=
  ∑ i ∈ Finset.range m, harper1144GaussianZeroExtend omega i

theorem harper1144GaussianZeroExtend_eq
    {n : Nat} (omega : Fin n -> Real) {i : Nat} (hi : i < n) :
    harper1144GaussianZeroExtend omega i = omega ⟨i, hi⟩ := by
  simp [harper1144GaussianZeroExtend, hi]

theorem harper1144GaussianPrefixNat_eq_sum_fin
    {n : Nat} (omega : Fin n -> Real) :
    harper1144GaussianPrefixNat omega n = ∑ i : Fin n, omega i := by
  unfold harper1144GaussianPrefixNat
  rw [show (∑ i : Fin n, omega i) =
      ∑ i ∈ Finset.range n, harper1144GaussianZeroExtend omega i by
    simpa [harper1144GaussianZeroExtend] using
      (Fin.sum_univ_eq_sum_range
        (fun i : Nat => harper1144GaussianZeroExtend omega i) n)]

/-- The Nat-indexed prefix is the ordinary path partial sum whenever the
prefix endpoint lies in the finite path. -/
theorem harper1144GaussianPrefixNat_eq_partialSum
    {n : Nat} (omega : Fin n -> Real) (k : Fin n) :
    harper1144GaussianPrefixNat omega (k.val + 1) =
      Problem520.harperPathPartialSum omega k := by
  rw [Problem520.harperPathPartialSum_eq_sum_prefix]
  unfold harper1144GaussianPrefixNat
  rw [← Fin.sum_univ_eq_sum_range
    (fun i : Nat => harper1144GaussianZeroExtend omega i) (k.val + 1)]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [harper1144GaussianZeroExtend,
    Problem520.harperPathPrefix]
  split
  · rfl
  · omega

/-- Abel summation identity for the logarithmic likelihood. -/
theorem harper1144GaussianLogTiltLinear_eq_by_parts
    {n : Nat} (omega : Fin n -> Real) :
    harper1144GaussianLogTiltLinear omega =
      harper1144GaussianLogTiltRateNat (n - 1) *
          harper1144GaussianPrefixNat omega n +
        ∑ i ∈ Finset.range (n - 1),
          (harper1144GaussianLogTiltRateNat i -
              harper1144GaussianLogTiltRateNat (i + 1)) *
            harper1144GaussianPrefixNat omega (i + 1) := by
  unfold harper1144GaussianLogTiltLinear
  rw [show (∑ i : Fin n, harper1144GaussianLogTiltRate i * omega i) =
      ∑ i ∈ Finset.range n,
        harper1144GaussianLogTiltRateNat i *
          harper1144GaussianZeroExtend omega i by
    simpa [harper1144GaussianLogTiltRate_eq_nat,
      harper1144GaussianZeroExtend] using
      (Fin.sum_univ_eq_sum_range
        (fun i : Nat => harper1144GaussianLogTiltRateNat i *
          harper1144GaussianZeroExtend omega i) n)]
  have hparts := Finset.sum_range_by_parts
    harper1144GaussianLogTiltRateNat
    (harper1144GaussianZeroExtend omega) n
  calc
    (∑ i ∈ Finset.range n,
        harper1144GaussianLogTiltRateNat i *
          harper1144GaussianZeroExtend omega i) =
        harper1144GaussianLogTiltRateNat (n - 1) *
            harper1144GaussianPrefixNat omega n -
          ∑ i ∈ Finset.range (n - 1),
            (harper1144GaussianLogTiltRateNat (i + 1) -
                harper1144GaussianLogTiltRateNat i) *
              harper1144GaussianPrefixNat omega (i + 1) := by
      simpa only [smul_eq_mul, harper1144GaussianPrefixNat] using hparts
    _ = harper1144GaussianLogTiltRateNat (n - 1) *
            harper1144GaussianPrefixNat omega n +
          ∑ i ∈ Finset.range (n - 1),
            (harper1144GaussianLogTiltRateNat i -
                harper1144GaussianLogTiltRateNat (i + 1)) *
              harper1144GaussianPrefixNat omega (i + 1) := by
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      ring

/-- Successive inverse-time rates decrease. -/
theorem harper1144GaussianLogTiltRateNat_succ_le (i : Nat) :
    harper1144GaussianLogTiltRateNat (i + 1) <=
      harper1144GaussianLogTiltRateNat i := by
  unfold harper1144GaussianLogTiltRateNat
  have hi1 : (0 : Real) < ((i + 1 : Nat) : Real) := by positivity
  have hi2 : (0 : Real) < ((i + 2 : Nat) : Real) := by positivity
  apply (div_le_div_iff_of_pos_left (by norm_num : (0 : Real) < 8) hi2 hi1).mpr
  norm_num

theorem harper1144GaussianLogTiltRateNat_sub_succ_nonneg (i : Nat) :
    0 <= harper1144GaussianLogTiltRateNat i -
      harper1144GaussianLogTiltRateNat (i + 1) :=
  sub_nonneg.mpr (harper1144GaussianLogTiltRateNat_succ_le i)

theorem harper1144GaussianLogFencePower_nonneg (m : Nat) :
    0 <= harper1144GaussianLogFencePower m := by
  unfold harper1144GaussianLogFencePower
  positivity

/-- On positive integer arguments the `3/4`-power fence is below the linear
fence. -/
theorem harper1144GaussianLogFencePower_le_self
    {m : Nat} (hm : 1 <= m) :
    harper1144GaussianLogFencePower m <= (m : Real) := by
  unfold harper1144GaussianLogFencePower
  calc
    (m : Real) ^ (3 / 4 : Real) <= (m : Real) ^ (1 : Real) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast hm
      · norm_num
    _ = (m : Real) := Real.rpow_one _

/-- Exact reciprocal-product formula for one Abel coefficient. -/
theorem harper1144GaussianLogTiltRateNat_sub_succ (i : Nat) :
    harper1144GaussianLogTiltRateNat i -
        harper1144GaussianLogTiltRateNat (i + 1) =
      8 / (((i + 1 : Nat) : Real) * ((i + 2 : Nat) : Real)) := by
  unfold harper1144GaussianLogTiltRateNat
  have hi1 : (0 : Real) < ((i + 1 : Nat) : Real) := by positivity
  have hi2 : (0 : Real) < ((i + 2 : Nat) : Real) := by positivity
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- Fixed summable majorant for the Abel coefficients after applying the
`3/4`-power lower fence. -/
def harper1144GaussianLogFencePSeriesTerm (i : Nat) : Real :=
  8 * (((i + 1 : Nat) : Real) ^ (-5 / 4 : Real))

theorem summable_harper1144GaussianLogFencePSeriesTerm :
    Summable harper1144GaussianLogFencePSeriesTerm := by
  unfold harper1144GaussianLogFencePSeriesTerm
  apply Summable.mul_left
  have hbase :=
    Real.summable_nat_rpow.mpr (by norm_num : (-5 / 4 : Real) < -1)
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).mpr hbase

/-- One Abel coefficient times the auxiliary fence is bounded by the fixed
`p`-series term. -/
theorem harper1144GaussianLogTiltRateDiff_mul_fencePower_le (i : Nat) :
    (harper1144GaussianLogTiltRateNat i -
        harper1144GaussianLogTiltRateNat (i + 1)) *
        harper1144GaussianLogFencePower (i + 1) <=
      harper1144GaussianLogFencePSeriesTerm i := by
  let x : Real := ((i + 1 : Nat) : Real)
  have hx : 0 < x := by dsimp [x]; positivity
  have hx1 : x <= ((i + 2 : Nat) : Real) := by
    dsimp [x]
    norm_num
  have hfrac :
      8 / (x * ((i + 2 : Nat) : Real)) <= 8 / (x * x) := by
    apply div_le_div_of_nonneg_left (by norm_num) (mul_pos hx hx)
    exact mul_le_mul_of_nonneg_left hx1 hx.le
  have hpow : 0 <= x ^ (3 / 4 : Real) := by positivity
  have hrpow : x ^ (3 / 4 : Real) / x ^ 2 =
      x ^ (-5 / 4 : Real) := by
    rw [← Real.rpow_sub_natCast hx.ne' (3 / 4 : Real) 2]
    congr 1
    norm_num
  rw [harper1144GaussianLogTiltRateNat_sub_succ]
  change 8 / (x * ((i + 2 : Nat) : Real)) * x ^ (3 / 4 : Real) <=
    8 * x ^ (-5 / 4 : Real)
  calc
    8 / (x * ((i + 2 : Nat) : Real)) * x ^ (3 / 4 : Real) <=
        8 / (x * x) * x ^ (3 / 4 : Real) :=
      mul_le_mul_of_nonneg_right hfrac hpow
    _ = 8 * (x ^ (3 / 4 : Real) / x ^ 2) := by
      rw [pow_two]
      field_simp
    _ = 8 * x ^ (-5 / 4 : Real) := by rw [hrpow]

/-- Uniform deterministic likelihood budget supplied by the summable lower
fence. -/
def harper1144GaussianLogFenceAbelBudget : Real :=
  8 + ∑' i : Nat, harper1144GaussianLogFencePSeriesTerm i

theorem harper1144GaussianLogFenceAbelBudget_nonneg :
    0 <= harper1144GaussianLogFenceAbelBudget := by
  unfold harper1144GaussianLogFenceAbelBudget
  have hterm : ∀ i, 0 <= harper1144GaussianLogFencePSeriesTerm i := by
    intro i
    unfold harper1144GaussianLogFencePSeriesTerm
    positivity
  exact add_nonneg (by norm_num)
    (tsum_nonneg hterm)

/-- The terminal Abel coefficient spends at most `8` units of the auxiliary
fence, independently of the path length. -/
theorem harper1144GaussianLogTiltRateLast_mul_fencePower_le_eight
    {n : Nat} (hn : 0 < n) :
    harper1144GaussianLogTiltRateNat (n - 1) *
        harper1144GaussianLogFencePower n <= 8 := by
  have hpower := harper1144GaussianLogFencePower_le_self
    (Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hrate : 0 <= harper1144GaussianLogTiltRateNat (n - 1) := by
    unfold harper1144GaussianLogTiltRateNat
    positivity
  calc
    harper1144GaussianLogTiltRateNat (n - 1) *
        harper1144GaussianLogFencePower n <=
      harper1144GaussianLogTiltRateNat (n - 1) * (n : Real) :=
        mul_le_mul_of_nonneg_left hpower hrate
    _ = 8 := by
      unfold harper1144GaussianLogTiltRateNat
      have hnR : (n : Real) ≠ 0 := by exact_mod_cast hn.ne'
      rw [show n - 1 + 1 = n by omega]
      field_simp

/-- Abel summation converts the entire auxiliary prefix fence into one fixed
lower bound for the logarithmic likelihood linear form. -/
theorem harper1144GaussianLogTiltLinear_lower_of_auxFence
    {n : Nat} {K : Real} (hK : 0 <= K) (omega : Fin n -> Real)
    (hfence : omega ∈ harper1144GaussianLogAuxFenceEvent n K) :
    -K * harper1144GaussianLogFenceAbelBudget <=
      harper1144GaussianLogTiltLinear omega := by
  by_cases hn : n = 0
  · subst n
    simp only [harper1144GaussianLogTiltLinear, Finset.univ_eq_empty,
      Finset.sum_empty]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hK)
      harper1144GaussianLogFenceAbelBudget_nonneg
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let last : Fin n := ⟨n - 1, by omega⟩
  have hlastFence :
      -K * harper1144GaussianLogFencePower n <=
        harper1144GaussianPrefixNat omega n := by
    have h := hfence last
    rw [← harper1144GaussianPrefixNat_eq_partialSum omega last] at h
    simpa only [last, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
      using h
  have hlastRate : 0 <= harper1144GaussianLogTiltRateNat (n - 1) := by
    unfold harper1144GaussianLogTiltRateNat
    positivity
  have hlastTerm :
      -K * 8 <=
        harper1144GaussianLogTiltRateNat (n - 1) *
          harper1144GaussianPrefixNat omega n := by
    calc
      -K * 8 <= -K *
          (harper1144GaussianLogTiltRateNat (n - 1) *
            harper1144GaussianLogFencePower n) := by
        exact mul_le_mul_of_nonpos_left
          (harper1144GaussianLogTiltRateLast_mul_fencePower_le_eight hnpos)
          (neg_nonpos.mpr hK)
      _ = harper1144GaussianLogTiltRateNat (n - 1) *
          (-K * harper1144GaussianLogFencePower n) := by ring
      _ <= harper1144GaussianLogTiltRateNat (n - 1) *
          harper1144GaussianPrefixNat omega n :=
        mul_le_mul_of_nonneg_left hlastFence hlastRate
  have hprefixTerm : ∀ i ∈ Finset.range (n - 1),
      -K * harper1144GaussianLogFencePSeriesTerm i <=
        (harper1144GaussianLogTiltRateNat i -
            harper1144GaussianLogTiltRateNat (i + 1)) *
          harper1144GaussianPrefixNat omega (i + 1) := by
    intro i hi
    have hin : i < n := by
      have : i < n - 1 := Finset.mem_range.mp hi
      omega
    let k : Fin n := ⟨i, hin⟩
    have hprefix :
        -K * harper1144GaussianLogFencePower (i + 1) <=
          harper1144GaussianPrefixNat omega (i + 1) := by
      have h := hfence k
      rw [← harper1144GaussianPrefixNat_eq_partialSum omega k] at h
      simpa only [k] using h
    have hdiff : 0 <= harper1144GaussianLogTiltRateNat i -
        harper1144GaussianLogTiltRateNat (i + 1) :=
      harper1144GaussianLogTiltRateNat_sub_succ_nonneg i
    calc
      -K * harper1144GaussianLogFencePSeriesTerm i <=
          -K * ((harper1144GaussianLogTiltRateNat i -
              harper1144GaussianLogTiltRateNat (i + 1)) *
            harper1144GaussianLogFencePower (i + 1)) := by
        exact mul_le_mul_of_nonpos_left
          (harper1144GaussianLogTiltRateDiff_mul_fencePower_le i)
          (neg_nonpos.mpr hK)
      _ = (harper1144GaussianLogTiltRateNat i -
              harper1144GaussianLogTiltRateNat (i + 1)) *
            (-K * harper1144GaussianLogFencePower (i + 1)) := by ring
      _ <= (harper1144GaussianLogTiltRateNat i -
              harper1144GaussianLogTiltRateNat (i + 1)) *
            harper1144GaussianPrefixNat omega (i + 1) :=
        mul_le_mul_of_nonneg_left hprefix hdiff
  have hsumTerms :
      -K * (∑ i ∈ Finset.range (n - 1),
          harper1144GaussianLogFencePSeriesTerm i) <=
        ∑ i ∈ Finset.range (n - 1),
          (harper1144GaussianLogTiltRateNat i -
              harper1144GaussianLogTiltRateNat (i + 1)) *
            harper1144GaussianPrefixNat omega (i + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hprefixTerm
  have hfiniteTsum :
      (∑ i ∈ Finset.range (n - 1),
          harper1144GaussianLogFencePSeriesTerm i) <=
        ∑' i : Nat, harper1144GaussianLogFencePSeriesTerm i := by
    exact summable_harper1144GaussianLogFencePSeriesTerm.sum_le_tsum
      (Finset.range (n - 1)) (fun i _hi => by
        unfold harper1144GaussianLogFencePSeriesTerm
        positivity)
  rw [harper1144GaussianLogTiltLinear_eq_by_parts]
  unfold harper1144GaussianLogFenceAbelBudget
  calc
    -K * (8 + ∑' i : Nat, harper1144GaussianLogFencePSeriesTerm i) =
        -K * 8 + -K *
          (∑' i : Nat, harper1144GaussianLogFencePSeriesTerm i) := by ring
    _ <= -K * 8 + -K *
          (∑ i ∈ Finset.range (n - 1),
            harper1144GaussianLogFencePSeriesTerm i) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonpos_left hfiniteTsum (neg_nonpos.mpr hK))
    _ <= harper1144GaussianLogTiltRateNat (n - 1) *
          harper1144GaussianPrefixNat omega n +
        ∑ i ∈ Finset.range (n - 1),
          (harper1144GaussianLogTiltRateNat i -
              harper1144GaussianLogTiltRateNat (i + 1)) *
            harper1144GaussianPrefixNat omega (i + 1) :=
      add_le_add hlastTerm hsumTerms

/-- Every drift increment is at most `4/(i+1)` under the variance upper
bound. -/
theorem harper1144GaussianLogTiltIncrement_le_four_div
    {n : Nat} (variance : Fin n -> NNReal)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) (i : Fin n) :
    harper1144GaussianLogTiltIncrement variance i <=
      4 / ((i.val + 1 : Nat) : Real) := by
  have hden : (0 : Real) < ((i.val + 1 : Nat) : Real) := by positivity
  have hv : (variance i : Real) <= (1 / 2 : Real) := by
    exact_mod_cast hupper i
  unfold harper1144GaussianLogTiltIncrement
    harper1144GaussianLogTiltRate
  calc
    8 / ((i.val + 1 : Nat) : Real) * (variance i : Real) <=
        8 / ((i.val + 1 : Nat) : Real) * (1 / 2 : Real) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ = 4 / ((i.val + 1 : Nat) : Real) := by
      field_simp
      ring

/-- The cumulative deterministic translation through time `k` is at most
`4(k+1)`. -/
theorem harper1144GaussianLogTiltCumulative_le_four_mul
    {n : Nat} (variance : Fin n -> NNReal)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) (k : Fin n) :
    harper1144GaussianLogTiltCumulative variance k <=
      4 * ((k.val + 1 : Nat) : Real) := by
  have hterm : ∀ i : Fin n,
      harper1144GaussianLogTiltIncrement variance i <= 4 := by
    intro i
    have hdiv := harper1144GaussianLogTiltIncrement_le_four_div
      variance hupper i
    have hden : (1 : Real) <= ((i.val + 1 : Nat) : Real) := by norm_num
    have hfour : 4 / ((i.val + 1 : Nat) : Real) <= (4 : Real) := by
      apply (div_le_iff₀ (by positivity :
        (0 : Real) < ((i.val + 1 : Nat) : Real))).mpr
      nlinarith
    exact hdiv.trans hfour
  unfold harper1144GaussianLogTiltCumulative
  calc
    (∑ i ∈ Finset.Iic k,
        harper1144GaussianLogTiltIncrement variance i) <=
        ∑ _i ∈ Finset.Iic k, (4 : Real) :=
      Finset.sum_le_sum fun i _hi => hterm i
    _ = 4 * ((k.val + 1 : Nat) : Real) := by
      simp [Finset.sum_const, mul_comm]

/-- Fixed likelihood threshold associated with the concrete auxiliary fence
constant `K = 16`. -/
def harper1144GaussianLogFenceCertificateBudget : Real :=
  16 * harper1144GaussianLogFenceAbelBudget + 32

theorem harper1144GaussianLogFenceCertificateBudget_nonneg :
    0 <= harper1144GaussianLogFenceCertificateBudget := by
  unfold harper1144GaussianLogFenceCertificateBudget
  nlinarith [harper1144GaussianLogFenceAbelBudget_nonneg]

/-- A flat ballot together with the `16 k^(3/4)` lower fence satisfies every
condition of the explicit Cameron--Martin certificate. -/
theorem flat_inter_auxFence_subset_logTiltCertificate
    {n : Nat} (variance : Fin n -> NNReal)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) :
    Problem520.gaussianWalkSurvivalSet n (1 / 2 : Real) ∩
        harper1144GaussianLogAuxFenceEvent n 16 ⊆
      harper1144GaussianLogTiltCertificateEvent variance
        harper1144GaussianLogFenceCertificateBudget := by
  intro omega homega
  refine ⟨homega.1, ?_, ?_⟩
  · intro k
    have hfence := homega.2 k
    have hpower := harper1144GaussianLogFencePower_le_self
      (m := k.val + 1) (by omega)
    have hlinearFence :
        -16 * ((k.val + 1 : Nat) : Real) <=
          Problem520.harperPathPartialSum omega k := by
      exact (mul_le_mul_of_nonpos_left hpower (by norm_num :
        (-16 : Real) <= 0)).trans hfence
    have hcumulative :=
      harper1144GaussianLogTiltCumulative_le_four_mul
        variance hupper k
    rw [harperPathPartialSum_harper1144GaussianLogTiltDown]
    linarith
  · have hlinear := harper1144GaussianLogTiltLinear_lower_of_auxFence
      (K := (16 : Real)) (by norm_num) omega homega.2
    have henergy :=
      sum_harper1144GaussianLogTiltRate_sq_mul_variance_le
        variance hupper
    change harper1144GaussianLogTiltEnergy variance <= 64 at henergy
    rw [harper1144GaussianLogTiltLinear_tiltDown]
    unfold harper1144GaussianLogFenceCertificateBudget
    linarith

/-- Final deterministic reduction for the one-height lower bound.  The only
remaining probability theorem is that the flat ballot retains order
`n^(-1/2)` mass after the concrete auxiliary lower fence is imposed. -/
theorem pi_gaussianReal_flat_inter_auxFence_le_exp_mul_core
    {n : Nat} (variance : Fin n -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) :
    Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
        (Problem520.gaussianWalkSurvivalSet n (1 / 2 : Real) ∩
          harper1144GaussianLogAuxFenceEvent n 16) <=
      ENNReal.ofReal
          (Real.exp harper1144GaussianLogFenceCertificateBudget) *
        Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
          (harper1144GaussianLogBallotCoreEvent n) := by
  exact (measure_mono
      (flat_inter_auxFence_subset_logTiltCertificate variance hupper)).trans
    (pi_gaussianReal_logTiltCertificate_le_exp_mul_core variance hlower
      harper1144GaussianLogFenceCertificateBudget)

#print axioms Erdos.Problem1144.harper1144GaussianLogTiltLinear_lower_of_auxFence
#print axioms Erdos.Problem1144.flat_inter_auxFence_subset_logTiltCertificate
#print axioms Erdos.Problem1144.pi_gaussianReal_flat_inter_auxFence_le_exp_mul_core

end

end Problem1144
end Erdos
