import Erdos.Problem1144.HarperGaussianFenceTail
import Erdos.Problem520.HarperMovingHeightVerticalCumulative

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Summing the auxiliary-fence failures

The measure-theoretic prefix/suffix estimate is proved in
`HarperGaussianFenceTail`.  This file supplies its deliberately wasteful
numerical specialization.  At split time `m` we use

`a_m = 16 m^(3/4)` and `t_m = 8 m^(-1/4)`.

The resulting Chernoff exponent is at most `-112 sqrt m`; this leaves far
more room than is needed to sum all possible failure times while retaining a
fixed multiple of the flat-ballot probability.
-/

/-- The lower-fence depth at a positive prefix length. -/
def harper1144GaussianFenceDepth (m : Nat) : Real :=
  16 * harper1144GaussianLogFencePower m

/-- Split-dependent Chernoff parameter for the fence tail. -/
def harper1144GaussianFenceChernoff (m : Nat) : Real :=
  8 * ((m : Real) ^ (-1 / 4 : Real))

/-- The chosen fractional powers combine to the square-root scale. -/
theorem harper1144GaussianFenceChernoff_mul_depth
    {m : Nat} (hm : 0 < m) :
    harper1144GaussianFenceChernoff m *
        harper1144GaussianFenceDepth m =
      128 * Real.sqrt (m : Real) := by
  have hmReal : 0 < (m : Real) := by exact_mod_cast hm
  have hpow :
      ((m : Real) ^ (-1 / 4 : Real)) *
          ((m : Real) ^ (3 / 4 : Real)) =
        Real.sqrt (m : Real) := by
    rw [← Real.rpow_add hmReal]
    norm_num
    exact (Real.sqrt_eq_rpow (m : Real)).symm
  unfold harper1144GaussianFenceChernoff
    harper1144GaussianFenceDepth harper1144GaussianLogFencePower
  rw [← hpow]
  ring

/-- Squaring the Chernoff parameter and multiplying by the maximal prefix
variance produces only `16 sqrt(m)` units of energy. -/
theorem harper1144GaussianFence_variance_energy_le
    {m : Nat} (hm : 0 < m) {V : Real} (hV0 : 0 <= V)
    (hV : V <= (m : Real) / 2) :
    V * harper1144GaussianFenceChernoff m ^ 2 / 2 <=
      16 * Real.sqrt (m : Real) := by
  have hmReal : 0 < (m : Real) := by exact_mod_cast hm
  have hpowSq :
      ((m : Real) ^ (-1 / 4 : Real)) ^ 2 =
        (m : Real) ^ (-1 / 2 : Real) := by
    rw [show ((m : Real) ^ (-1 / 4 : Real)) ^ 2 =
        ((m : Real) ^ (-1 / 4 : Real)) *
          ((m : Real) ^ (-1 / 4 : Real)) by ring]
    rw [← Real.rpow_add hmReal]
    norm_num
  have hpowMul :
      (m : Real) * ((m : Real) ^ (-1 / 2 : Real)) =
        Real.sqrt (m : Real) := by
    calc
      (m : Real) * ((m : Real) ^ (-1 / 2 : Real)) =
          (m : Real) ^ (1 : Real) *
            ((m : Real) ^ (-1 / 2 : Real)) := by rw [Real.rpow_one]
      _ = (m : Real) ^ ((1 : Real) + (-1 / 2 : Real)) :=
        (Real.rpow_add hmReal _ _).symm
      _ = Real.sqrt (m : Real) := by
        norm_num
        exact (Real.sqrt_eq_rpow (m : Real)).symm
  have htSq : harper1144GaussianFenceChernoff m ^ 2 =
      64 * ((m : Real) ^ (-1 / 2 : Real)) := by
    unfold harper1144GaussianFenceChernoff
    rw [mul_pow, hpowSq]
    norm_num
  rw [htSq]
  calc
    V * (64 * ((m : Real) ^ (-1 / 2 : Real))) / 2 <=
        ((m : Real) / 2) *
          (64 * ((m : Real) ^ (-1 / 2 : Real))) / 2 := by
      gcongr
    _ = 16 * Real.sqrt (m : Real) := by rw [← hpowMul]; ring

/-- The complete exponent checkpoint. -/
theorem harper1144GaussianFence_exponent_le
    {m : Nat} (hm : 0 < m) {V : Real} (hV0 : 0 <= V)
    (hV : V <= (m : Real) / 2) :
    -harper1144GaussianFenceChernoff m *
          harper1144GaussianFenceDepth m +
        V * harper1144GaussianFenceChernoff m ^ 2 / 2 <=
      -112 * Real.sqrt (m : Real) := by
  rw [neg_mul]
  have hdepth := harper1144GaussianFenceChernoff_mul_depth hm
  have henergy := harper1144GaussianFence_variance_energy_le hm hV0 hV
  nlinarith

/-- The harmless affine overshoot weight is at most linear in the split
time. -/
theorem harper1144GaussianFence_affineWeight_le
    {m : Nat} (hm : 0 < m) :
    (1 / 2 : Real) + 2 + harper1144GaussianFenceDepth m +
        1 / harper1144GaussianFenceChernoff m <=
      20 * (m : Real) := by
  have hmReal : 0 < (m : Real) := by exact_mod_cast hm
  have hmOne : (1 : Real) <= m := by exact_mod_cast hm
  have hthreeQuarter :
      (m : Real) ^ (3 / 4 : Real) <= (m : Real) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hmOne (by norm_num :
        (3 / 4 : Real) <= 1)
  have honeQuarter :
      (m : Real) ^ (1 / 4 : Real) <= (m : Real) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hmOne (by norm_num :
        (1 / 4 : Real) <= 1)
  have htInv : 1 / harper1144GaussianFenceChernoff m =
      ((m : Real) ^ (1 / 4 : Real)) / 8 := by
    unfold harper1144GaussianFenceChernoff
    rw [show (-1 / 4 : Real) = -(1 / 4 : Real) by norm_num,
      Real.rpow_neg hmReal.le]
    field_simp [(Real.rpow_pos_of_pos hmReal (1 / 4 : Real)).ne']
  rw [htInv]
  unfold harper1144GaussianFenceDepth
    harper1144GaussianLogFencePower
  nlinarith

/-- A prefix of `m` coordinates has total variance at most `m/2`. -/
theorem harper1144Gaussian_prefixVariance_le
    {m q : Nat} (variance : Fin (m + q) -> NNReal)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) :
    ((List.ofFn (fun i : Fin m =>
        variance (Fin.castAdd q i))).sum : Real) <=
      (m : Real) / 2 := by
  calc
    ((List.ofFn (fun i : Fin m =>
        variance (Fin.castAdd q i))).sum : Real) =
        ∑ i : Fin m, (variance (Fin.castAdd q i) : Real) := by
      simp [List.sum_ofFn]
    _ <= ∑ _i : Fin m, (1 / 2 : Real) := by
      exact Finset.sum_le_sum fun i _hi => by exact_mod_cast hupper _
    _ = (m : Real) / 2 := by simp; ring

/-- Numerical specialization of the deep-prefix estimate. -/
theorem gaussianWalkDeepAtSplit_fence_probability_le
    (m q : Nat) (hm : 0 < m) (hq : 0 < q)
    (variance : Fin (m + q) -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) :
    (Measure.pi (fun i : Fin (m + q) =>
      gaussianReal 0 (variance i))).real
        (gaussianWalkDeepAtSplitSet m q (1 / 2)
          (harper1144GaussianFenceDepth m)) <=
      (1280 * (m : Real) / Real.sqrt (q : Real)) *
        Real.exp (-112 * Real.sqrt (m : Real)) := by
  let V : Real :=
    ((List.ofFn (fun i : Fin m =>
      variance (Fin.castAdd q i))).sum : Real)
  have hV0 : 0 <= V := by dsimp only [V]; positivity
  have hV : V <= (m : Real) / 2 := by
    exact harper1144Gaussian_prefixVariance_le variance hupper
  have ha : 0 <= harper1144GaussianFenceDepth m := by
    unfold harper1144GaussianFenceDepth
      harper1144GaussianLogFencePower
    positivity
  have ht : 0 < harper1144GaussianFenceChernoff m := by
    unfold harper1144GaussianFenceChernoff
    positivity
  have hmain := gaussianWalkDeepAtSplit_probability_le_exp
    m q hq variance (x := (1 / 2 : Real))
    (a := harper1144GaussianFenceDepth m)
    (t := harper1144GaussianFenceChernoff m)
    (by norm_num) ha ht hlower hupper
  have hweight := harper1144GaussianFence_affineWeight_le hm
  have hexponent := harper1144GaussianFence_exponent_le hm hV0 hV
  have hsqrtq : 0 < Real.sqrt (q : Real) := by positivity
  calc
    (Measure.pi (fun i : Fin (m + q) =>
      gaussianReal 0 (variance i))).real
        (gaussianWalkDeepAtSplitSet m q (1 / 2)
          (harper1144GaussianFenceDepth m)) <=
      (64 / Real.sqrt (q : Real)) *
        ((1 / 2 : Real) + 2 + harper1144GaussianFenceDepth m +
          1 / harper1144GaussianFenceChernoff m) *
        Real.exp (-harper1144GaussianFenceChernoff m *
            harper1144GaussianFenceDepth m +
          V * harper1144GaussianFenceChernoff m ^ 2 / 2) := by
        simpa only [V] using hmain
    _ <= (64 / Real.sqrt (q : Real)) * (20 * (m : Real)) *
        Real.exp (-112 * Real.sqrt (m : Real)) := by
      gcongr
    _ = (1280 * (m : Real) / Real.sqrt (q : Real)) *
        Real.exp (-112 * Real.sqrt (m : Real)) := by ring

/-- The very strong square-root exponential is dominated by the fourth
inverse power, with a fixed tiny prefactor. -/
theorem exp_neg_112_sqrt_nat_le_inv_fourth
    {m : Nat} (hm : 0 < m) :
    Real.exp (-112 * Real.sqrt (m : Real)) <=
      Real.exp (-56) * (((m : Real) ^ 4)⁻¹) := by
  have hmReal : 0 < (m : Real) := by exact_mod_cast hm
  have hmOne : (1 : Real) <= m := by exact_mod_cast hm
  have hsqrtPos : 0 < Real.sqrt (m : Real) := Real.sqrt_pos.2 hmReal
  have hsqrtOne : (1 : Real) <= Real.sqrt (m : Real) := by
    have hsq := Real.sq_sqrt hmReal.le
    nlinarith [Real.sqrt_nonneg (m : Real)]
  have hlogBase := Real.log_le_sub_one_of_pos hsqrtPos
  have hlog : Real.log (m : Real) <=
      2 * (Real.sqrt (m : Real) - 1) := by
    rw [Real.log_sqrt hmReal.le] at hlogBase
    linarith
  have hexponent :
      -112 * Real.sqrt (m : Real) <=
        -56 - 4 * Real.log (m : Real) := by
    nlinarith
  calc
    Real.exp (-112 * Real.sqrt (m : Real)) <=
        Real.exp (-56 - 4 * Real.log (m : Real)) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.exp (-56) * (((m : Real) ^ 4)⁻¹) := by
      rw [show -56 - 4 * Real.log (m : Real) =
          -56 + -(4 * Real.log (m : Real)) by ring,
        Real.exp_add]
      congr 1
      rw [Real.exp_neg]
      congr 1
      simpa only [Real.exp_log hmReal] using
        Real.exp_nat_mul (Real.log (m : Real)) 4

/-- The untouched suffix denominator can be put on the full path scale at
the cost of two powers of the split time. -/
theorem inv_sqrt_le_two_mul_div_sqrt_add
    {m q : Nat} (hm : 0 < m) (hq : 0 < q) :
    (Real.sqrt (q : Real))⁻¹ <=
      2 * (m : Real) / Real.sqrt ((m + q : Nat) : Real) := by
  have hqReal : 0 < (q : Real) := by exact_mod_cast hq
  have hnReal : 0 < ((m + q : Nat) : Real) := by positivity
  have hsqrtq : 0 < Real.sqrt (q : Real) := Real.sqrt_pos.2 hqReal
  have hsqrtn : 0 < Real.sqrt ((m + q : Nat) : Real) :=
    Real.sqrt_pos.2 hnReal
  have hmq : ((m + q : Nat) : Real) <=
      (2 * (m : Real) * Real.sqrt (q : Real)) ^ 2 := by
    have hsq := Real.sq_sqrt hqReal.le
    have hmNat : m <= m ^ 2 * q := by
      have hmqOne : 1 <= m * q := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.ne_of_gt hm) (Nat.ne_of_gt hq))
      calc
        m = m * 1 := by omega
        _ <= m * (m * q) := Nat.mul_le_mul_left m hmqOne
        _ = m ^ 2 * q := by ring
    have hqNat : q <= m ^ 2 * q := by
      have hmSqOne : 1 <= m ^ 2 := Nat.one_le_iff_ne_zero.mpr
        (pow_ne_zero 2 (Nat.ne_of_gt hm))
      calc
        q = 1 * q := by omega
        _ <= (m ^ 2) * q := Nat.mul_le_mul_right q hmSqOne
    have hnat : m + q <= 4 * m ^ 2 * q := by
      calc
        m + q <= m ^ 2 * q + m ^ 2 * q := Nat.add_le_add hmNat hqNat
        _ = 2 * (m ^ 2 * q) := by ring
        _ <= 4 * (m ^ 2 * q) := Nat.mul_le_mul_right _ (by omega)
        _ = 4 * m ^ 2 * q := by ring
    rw [mul_pow]
    nlinarith [show ((m + q : Nat) : Real) <=
        4 * (m : Real) ^ 2 * (q : Real) by exact_mod_cast hnat]
  have hsqrt : Real.sqrt ((m + q : Nat) : Real) <=
      2 * (m : Real) * Real.sqrt (q : Real) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · simpa only [sq] using hmq
  rw [inv_eq_one_div]
  exact (div_le_div_iff₀ hsqrtq hsqrtn).2 (by
    simpa only [one_mul, mul_assoc] using hsqrt)

/-- A single nonterminal fence-failure contribution is already on the full
path `1/sqrt(m+q)` scale with a square-summable time weight. -/
theorem gaussianWalkDeepAtSplit_fence_probability_le_invSq
    (m q : Nat) (hm : 0 < m) (hq : 0 < q)
    (variance : Fin (m + q) -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) :
    (Measure.pi (fun i : Fin (m + q) =>
      gaussianReal 0 (variance i))).real
        (gaussianWalkDeepAtSplitSet m q (1 / 2)
          (harper1144GaussianFenceDepth m)) <=
      (2560 * Real.exp (-56) /
          Real.sqrt ((m + q : Nat) : Real)) *
        (((m : Real) ^ 2)⁻¹) := by
  have hbase := gaussianWalkDeepAtSplit_fence_probability_le
    m q hm hq variance hlower hupper
  have hexp := exp_neg_112_sqrt_nat_le_inv_fourth hm
  have hsuffix := inv_sqrt_le_two_mul_div_sqrt_add hm hq
  have hmReal : 0 < (m : Real) := by exact_mod_cast hm
  have hsqrtq : 0 < Real.sqrt (q : Real) := by positivity
  have hsqrtn : 0 < Real.sqrt ((m + q : Nat) : Real) := by positivity
  calc
    (Measure.pi (fun i : Fin (m + q) =>
      gaussianReal 0 (variance i))).real
        (gaussianWalkDeepAtSplitSet m q (1 / 2)
          (harper1144GaussianFenceDepth m)) <=
      (1280 * (m : Real) / Real.sqrt (q : Real)) *
        Real.exp (-112 * Real.sqrt (m : Real)) := hbase
    _ <= (1280 * (m : Real) *
          (2 * (m : Real) / Real.sqrt ((m + q : Nat) : Real))) *
        (Real.exp (-56) * (((m : Real) ^ 4)⁻¹)) := by
      rw [div_eq_mul_inv]
      gcongr
    _ = (2560 * Real.exp (-56) /
          Real.sqrt ((m + q : Nat) : Real)) *
        (((m : Real) ^ 2)⁻¹) := by
      field_simp
      ring

/-! ## Returning to an unsplit path -/

/-- Flat survival together with a deep value at the `m`-step prefix. -/
def gaussianWalkDeepAtTimeSet (n m : Nat) (x a : Real) :
    Set (Fin n -> Real) :=
  {omega | Problem520.gaussianWalkSurvives n x omega ∧
    harper1144GaussianPrefixNat omega m <= -a}

theorem measurableSet_gaussianWalkDeepAtTimeSet
    (n m : Nat) {x a : Real} (hx : 0 <= x) :
    MeasurableSet (gaussianWalkDeepAtTimeSet n m x a) := by
  apply (Problem520.measurableSet_gaussianWalkSurvivalSet n hx).inter
  unfold harper1144GaussianPrefixNat
  have hsum : Measurable (fun omega : Fin n -> Real =>
      ∑ i ∈ Finset.range m, harper1144GaussianZeroExtend omega i) := by
    exact Finset.measurable_sum _ fun i _hi => by
      by_cases hi : i < n
      · simpa [harper1144GaussianZeroExtend, hi] using
          (measurable_pi_apply (⟨i, hi⟩ : Fin n))
      · simp [harper1144GaussianZeroExtend, hi]
  exact measurableSet_le hsum measurable_const

/-- The first component of the finite split is exactly the Nat-indexed
prefix sum. -/
theorem sum_harperFinSplit_fst_eq_prefixNat
    {m q : Nat} (omega : Fin (m + q) -> Real) :
    (∑ i, (harperFinSplit omega).1 i) =
      harper1144GaussianPrefixNat omega m := by
  calc
    (∑ i, (harperFinSplit omega).1 i) =
        ∑ i : Fin m, harper1144GaussianZeroExtend omega i.val := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [harperFinSplit]
      rw [harper1144GaussianZeroExtend_eq omega (by omega)]
      congr 1
    _ = ∑ i ∈ Finset.range m,
        harper1144GaussianZeroExtend omega i :=
      Fin.sum_univ_eq_sum_range
        (fun i : Nat => harper1144GaussianZeroExtend omega i) m
    _ = harper1144GaussianPrefixNat omega m := rfl

theorem gaussianWalkDeepAtSplitSet_eq_timeSet
    (m q : Nat) (x a : Real) :
    gaussianWalkDeepAtSplitSet m q x a =
      gaussianWalkDeepAtTimeSet (m + q) m x a := by
  ext omega
  rw [show (omega ∈ gaussianWalkDeepAtSplitSet m q x a) ↔
      Problem520.gaussianWalkSurvives (m + q) x omega ∧
        (∑ i, (harperFinSplit omega).1 i) <= -a by rfl]
  rw [sum_harperFinSplit_fst_eq_prefixNat]
  rfl

/-- The inverse-square estimate stated on a path of fixed total length. -/
theorem gaussianWalkDeepAtTime_fence_probability_le_invSq
    (n m : Nat) (hm : 0 < m) (hmn : m < n)
    (variance : Fin n -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) :
    (Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))).real
        (gaussianWalkDeepAtTimeSet n m (1 / 2)
          (harper1144GaussianFenceDepth m)) <=
      (2560 * Real.exp (-56) / Real.sqrt (n : Real)) *
        (((m : Real) ^ 2)⁻¹) := by
  obtain ⟨q, rfl : n = m + q⟩ := Nat.exists_eq_add_of_le hmn.le
  have hq : 0 < q := by omega
  rw [← gaussianWalkDeepAtSplitSet_eq_timeSet]
  exact gaussianWalkDeepAtSplit_fence_probability_le_invSq
    m q hm hq variance hlower hupper

/-! ## The finite union of nonterminal failure times -/

theorem sum_Ico_inv_nat_sq_le_two (n : Nat) :
    (∑ m ∈ Finset.Ico 1 n, (((m : Real) ^ 2)⁻¹)) <= 2 := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h := Problem520.sum_range_inv_nat_succ_sq_le_two (n - 1)
  simpa only [Nat.cast_add, Nat.cast_one, add_comm] using h

/-- Union of all auxiliary-fence failures strictly before terminal time. -/
def gaussianWalkDeepBeforeTerminalSet (n : Nat) : Set (Fin n -> Real) :=
  ⋃ m ∈ Finset.Ico 1 n,
    gaussianWalkDeepAtTimeSet n m (1 / 2)
      (harper1144GaussianFenceDepth m)

theorem measurableSet_gaussianWalkDeepBeforeTerminalSet (n : Nat) :
    MeasurableSet (gaussianWalkDeepBeforeTerminalSet n) := by
  apply MeasurableSet.iUnion
  intro m
  apply MeasurableSet.iUnion
  intro hm
  exact measurableSet_gaussianWalkDeepAtTimeSet n m (by norm_num)

/-- All nonterminal failures together consume only a tiny fixed multiple of
the inverse-square-root ballot scale. -/
theorem gaussianWalkDeepBeforeTerminal_probability_le
    (n : Nat) (hn : 0 < n) (variance : Fin n -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) :
    (Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))).real
        (gaussianWalkDeepBeforeTerminalSet n) <=
      5120 * Real.exp (-56) / Real.sqrt (n : Real) := by
  let P : Measure (Fin n -> Real) :=
    Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
  let C : Real := 2560 * Real.exp (-56) / Real.sqrt (n : Real)
  have hC : 0 <= C := by dsimp only [C]; positivity
  calc
    P.real (gaussianWalkDeepBeforeTerminalSet n) <=
        ∑ m ∈ Finset.Ico 1 n,
          P.real (gaussianWalkDeepAtTimeSet n m (1 / 2)
            (harper1144GaussianFenceDepth m)) := by
      unfold gaussianWalkDeepBeforeTerminalSet
      exact measureReal_biUnion_finset_le _ _
    _ <= ∑ m ∈ Finset.Ico 1 n, C * (((m : Real) ^ 2)⁻¹) := by
      apply Finset.sum_le_sum
      intro m hm
      have hm' := Finset.mem_Ico.mp hm
      exact gaussianWalkDeepAtTime_fence_probability_le_invSq
        n m hm'.1 hm'.2 variance hlower hupper
    _ = C * ∑ m ∈ Finset.Ico 1 n, (((m : Real) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
    _ <= C * 2 := mul_le_mul_of_nonneg_left
      (sum_Ico_inv_nat_sq_le_two n) hC
    _ = 5120 * Real.exp (-56) / Real.sqrt (n : Real) := by
      dsimp only [C]
      ring

/-! ## Terminal failure -/

/-- The unrestricted deep terminal tail. -/
def gaussianWalkTerminalDeepSet (n : Nat) (a : Real) :
    Set (Fin n -> Real) :=
  {omega | (∑ i, omega i) <= -a}

theorem measurableSet_gaussianWalkTerminalDeepSet (n : Nat) (a : Real) :
    MeasurableSet (gaussianWalkTerminalDeepSet n a) := by
  exact measurableSet_le
    (Finset.measurable_sum _ fun i _hi => measurable_pi_apply i)
    measurable_const

theorem gaussianWalkTerminalDeep_probability_eq
    (n : Nat) (variance : Fin n -> NNReal) (a : Real) :
    (Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))).real
        (gaussianWalkTerminalDeepSet n a) =
      (gaussianReal 0 (List.ofFn variance).sum).real (Set.Iic (-a)) := by
  let P : Measure (Fin n -> Real) :=
    Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
  let S : (Fin n -> Real) -> Real := fun omega => ∑ i, omega i
  have hS : Measurable S :=
    Finset.measurable_sum _ fun i _hi => measurable_pi_apply i
  have hmap : P.map S = gaussianReal 0 (List.ofFn variance).sum := by
    simpa only [P, S] using map_pi_gaussianReal_sum_eq n variance
  rw [← hmap, map_measureReal_apply hS measurableSet_Iic]
  rfl

/-- The terminal fence failure is even smaller than one inverse-square-root
unit. -/
theorem gaussianWalkTerminalDeep_fence_probability_le
    (n : Nat) (hn : 0 < n) (variance : Fin n -> NNReal)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) :
    (Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))).real
        (gaussianWalkTerminalDeepSet n
          (harper1144GaussianFenceDepth n)) <=
      Real.exp (-56) / Real.sqrt (n : Real) := by
  let V : Real := (List.ofFn variance).sum
  have hV0 : 0 <= V := by dsimp only [V]; positivity
  have hV : V <= (n : Real) / 2 := by
    simpa only [V] using
      (harper1144Gaussian_prefixVariance_le (m := n) (q := 0)
        variance hupper)
  have ht : 0 < harper1144GaussianFenceChernoff n := by
    unfold harper1144GaussianFenceChernoff
    positivity
  have htail := gaussianReal_Iic_neg_le_exp
    (List.ofFn variance).sum
    (a := harper1144GaussianFenceDepth n)
    (t := harper1144GaussianFenceChernoff n) ht
  have hexponent := harper1144GaussianFence_exponent_le hn hV0 hV
  have hpoly := exp_neg_112_sqrt_nat_le_inv_fourth hn
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hsqrtPos : 0 < Real.sqrt (n : Real) := Real.sqrt_pos.2 hnReal
  have hsqrtLeN : Real.sqrt (n : Real) <= (n : Real) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · exact hnReal.le
    · have hnOne : (1 : Real) <= n := by exact_mod_cast hn
      nlinarith
  have hnLeFourth : (n : Real) <= (n : Real) ^ 4 := by
    have hnOne : (1 : Real) <= n := by exact_mod_cast hn
    let x : Real := n
    have hx0 : 0 <= x := by
      dsimp only [x]
      positivity
    have hx1 : 0 <= x - 1 := by
      dsimp only [x]
      linarith
    have hpoly : 0 <= x ^ 2 + x + 1 := by
      nlinarith [sq_nonneg x]
    have hfactor : 0 <= x * (x - 1) * (x ^ 2 + x + 1) :=
      mul_nonneg (mul_nonneg hx0 hx1) hpoly
    dsimp only [x] at hfactor
    nlinarith
  have hinv : (((n : Real) ^ 4)⁻¹) <=
      1 / Real.sqrt (n : Real) := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hsqrtPos (hsqrtLeN.trans hnLeFourth)
  calc
    (Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))).real
        (gaussianWalkTerminalDeepSet n
          (harper1144GaussianFenceDepth n)) =
      (gaussianReal 0 (List.ofFn variance).sum).real
        (Set.Iic (-harper1144GaussianFenceDepth n)) :=
      gaussianWalkTerminalDeep_probability_eq n variance _
    _ <= Real.exp (-harper1144GaussianFenceChernoff n *
          harper1144GaussianFenceDepth n +
        V * harper1144GaussianFenceChernoff n ^ 2 / 2) := by
      simpa only [V] using htail
    _ <= Real.exp (-112 * Real.sqrt (n : Real)) :=
      Real.exp_le_exp.mpr hexponent
    _ <= Real.exp (-56) * (((n : Real) ^ 4)⁻¹) := hpoly
    _ <= Real.exp (-56) * (1 / Real.sqrt (n : Real)) := by
      gcongr
    _ = Real.exp (-56) / Real.sqrt (n : Real) := by ring

/-! ## Identifying every auxiliary-fence failure -/

/-- A flat-surviving path which fails the auxiliary lower fence does so either
strictly before terminal time or at terminal time. -/
theorem flat_diff_auxFence_subset_deepBeforeTerminal_union_terminal
    (n : Nat) :
    Problem520.gaussianWalkSurvivalSet n (1 / 2 : Real) \
        harper1144GaussianLogAuxFenceEvent n 16 ⊆
      gaussianWalkDeepBeforeTerminalSet n ∪
        gaussianWalkTerminalDeepSet n
          (harper1144GaussianFenceDepth n) := by
  intro omega homega
  rcases homega with ⟨hflat, hfence⟩
  simp only [harper1144GaussianLogAuxFenceEvent, Set.mem_setOf_eq,
    not_forall, not_le] at hfence
  obtain ⟨k, hk⟩ := hfence
  let m : Nat := k.val + 1
  have hmPos : 0 < m := by
    dsimp only [m]
    omega
  have hpref : harper1144GaussianPrefixNat omega m <
      -harper1144GaussianFenceDepth m := by
    dsimp only [m]
    rw [harper1144GaussianPrefixNat_eq_partialSum omega k]
    simpa only [harper1144GaussianFenceDepth, neg_mul] using hk
  by_cases hmTerminal : m < n
  · left
    simp only [gaussianWalkDeepBeforeTerminalSet, Set.mem_iUnion]
    refine ⟨m, Finset.mem_Ico.mpr ⟨hmPos, hmTerminal⟩, ?_⟩
    exact ⟨hflat, hpref.le⟩
  · right
    have hmLe : m <= n := by
      dsimp only [m]
      omega
    have hmEq : m = n := Nat.le_antisymm hmLe (Nat.le_of_not_gt hmTerminal)
    have hprefn : harper1144GaussianPrefixNat omega n <
        -harper1144GaussianFenceDepth n := by
      simpa only [hmEq] using hpref
    have hterminal : (∑ i : Fin n, omega i) <
        -harper1144GaussianFenceDepth n := by
      rw [← harper1144GaussianPrefixNat_eq_sum_fin omega]
      exact hprefn
    exact hterminal.le

/-- The total mass removed from the flat ballot by the auxiliary fence is a
negligible fixed multiple of the ballot scale. -/
theorem flat_diff_auxFence_probability_le
    (n : Nat) (hn : 0 < n) (variance : Fin n -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) :
    (Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))).real
        (Problem520.gaussianWalkSurvivalSet n (1 / 2 : Real) \
          harper1144GaussianLogAuxFenceEvent n 16) <=
      5121 * Real.exp (-56) / Real.sqrt (n : Real) := by
  let P : Measure (Fin n -> Real) :=
    Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
  have hbefore := gaussianWalkDeepBeforeTerminal_probability_le
    n hn variance hlower hupper
  have hterminal := gaussianWalkTerminalDeep_fence_probability_le
    n hn variance hupper
  calc
    P.real (Problem520.gaussianWalkSurvivalSet n (1 / 2 : Real) \
        harper1144GaussianLogAuxFenceEvent n 16) <=
      P.real (gaussianWalkDeepBeforeTerminalSet n ∪
        gaussianWalkTerminalDeepSet n
          (harper1144GaussianFenceDepth n)) :=
      measureReal_mono
        (flat_diff_auxFence_subset_deepBeforeTerminal_union_terminal n)
    _ <= P.real (gaussianWalkDeepBeforeTerminalSet n) +
        P.real (gaussianWalkTerminalDeepSet n
          (harper1144GaussianFenceDepth n)) := measureReal_union_le _ _
    _ <= 5120 * Real.exp (-56) / Real.sqrt (n : Real) +
        Real.exp (-56) / Real.sqrt (n : Real) :=
      add_le_add hbefore hterminal
    _ = 5121 * Real.exp (-56) / Real.sqrt (n : Real) := by ring

/-! ## A positive flat-ballot mass remains -/

/-- The deliberately extravagant Chernoff exponent makes the entire fence
error smaller than one quarter of the elementary flat-ballot constant. -/
theorem harper1144GaussianFence_error_constant_le :
    5121 * Real.exp (-56) <= Real.exp (-2) / 4 := by
  have htwo : (2 : Real) <= Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : Real)
  have hpow : (2 : Real) ^ 54 <= (Real.exp 1) ^ 54 := by
    gcongr
  have hexp54 : Real.exp (54 : Real) = (Real.exp 1) ^ 54 := by
    simpa only [Nat.cast_ofNat, Nat.cast_one, mul_one] using
      (Real.exp_nat_mul (1 : Real) 54)
  have hnum : (20484 : Real) <= (2 : Real) ^ 54 := by norm_num
  have hbig : (20484 : Real) <= Real.exp 54 := by
    rw [hexp54]
    exact hnum.trans hpow
  rw [show (-2 : Real) = -56 + 54 by norm_num, Real.exp_add]
  calc
    5121 * Real.exp (-56) <=
        (Real.exp 54 / 4) * Real.exp (-56) := by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · positivity
    _ = Real.exp (-56) * Real.exp 54 / 4 := by ring

/-- Imposing the auxiliary lower fence retains a concrete positive multiple
of the inverse-square-root ballot mass. -/
theorem quarter_exp_neg_two_div_sqrt_le_flat_inter_auxFence
    (n : Nat) (hn : 0 < n) (variance : Fin n -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) :
    Real.exp (-2) / (4 * Real.sqrt (n : Real)) <=
      (Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))).real
        (Problem520.gaussianWalkSurvivalSet n (1 / 2 : Real) ∩
          harper1144GaussianLogAuxFenceEvent n 16) := by
  let P : Measure (Fin n -> Real) :=
    Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
  let A := Problem520.gaussianWalkSurvivalSet n (1 / 2 : Real)
  let F := harper1144GaussianLogAuxFenceEvent n 16
  have hflat :=
    half_exp_neg_two_div_sqrt_le_gaussianVarianceWalk_probability_fin
      n hn variance hlower hupper
  have herror := flat_diff_auxFence_probability_le
    n hn variance hlower hupper
  have hsqrtPos : 0 < Real.sqrt (n : Real) := by
    apply Real.sqrt_pos.2
    exact_mod_cast hn
  have hconstant := harper1144GaussianFence_error_constant_le
  have herror' : P.real (A \ F) <=
      Real.exp (-2) / (4 * Real.sqrt (n : Real)) := by
    calc
      P.real (A \ F) <=
          5121 * Real.exp (-56) / Real.sqrt (n : Real) := by
        simpa only [P, A, F] using herror
      _ <= (Real.exp (-2) / 4) / Real.sqrt (n : Real) :=
        div_le_div_of_nonneg_right hconstant hsqrtPos.le
      _ = Real.exp (-2) / (4 * Real.sqrt (n : Real)) := by ring
  have hcover : A ⊆ (A ∩ F) ∪ (A \ F) := by
    intro omega homega
    by_cases hfence : omega ∈ F
    · exact Or.inl ⟨homega, hfence⟩
    · exact Or.inr ⟨homega, hfence⟩
  have hsplit : P.real A <= P.real (A ∩ F) + P.real (A \ F) :=
    (measureReal_mono hcover).trans (measureReal_union_le _ _)
  have hflat' : Real.exp (-2) / (2 * Real.sqrt (n : Real)) <=
      P.real A := by
    simpa only [P, A] using hflat
  let c : Real := Real.exp (-2) / (4 * Real.sqrt (n : Real))
  have hflatC : 2 * c <= P.real A := by
    calc
      2 * c = Real.exp (-2) / (2 * Real.sqrt (n : Real)) := by
        dsimp only [c]
        ring
      _ <= P.real A := hflat'
  have herrorC : P.real (A \ F) <= c := by
    simpa only [c] using herror'
  change c <= P.real (A ∩ F)
  linarith

/-- The completed one-height Gaussian theorem: the elapsed-time logarithmic
barrier core has a uniform inverse-square-root lower bound. -/
theorem exp_neg_certificateBudget_div_sqrt_le_gaussianLogBallotCore
    (n : Nat) (hn : 0 < n) (variance : Fin n -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) :
    Real.exp (-2 - harper1144GaussianLogFenceCertificateBudget) /
        (4 * Real.sqrt (n : Real)) <=
      (Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))).real
        (harper1144GaussianLogBallotCoreEvent n) := by
  let P : Measure (Fin n -> Real) :=
    Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
  let A := Problem520.gaussianWalkSurvivalSet n (1 / 2 : Real) ∩
    harper1144GaussianLogAuxFenceEvent n 16
  let G := harper1144GaussianLogBallotCoreEvent n
  let B := harper1144GaussianLogFenceCertificateBudget
  have hsource := quarter_exp_neg_two_div_sqrt_le_flat_inter_auxFence
    n hn variance hlower hupper
  have hcompare := pi_gaussianReal_flat_inter_auxFence_le_exp_mul_core
    variance hlower hupper
  have hcompareReal : P.real A <= Real.exp B * P.real G := by
    calc
      P.real A = (P A).toReal := measureReal_def P A
      _ <= (ENNReal.ofReal (Real.exp B) * P G).toReal :=
        ENNReal.toReal_mono (by finiteness) (by
          simpa only [P, A, G, B] using hcompare)
      _ = Real.exp B * P.real G := by
        rw [ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (Real.exp_pos B).le]
        rfl
  have hsourceReal : Real.exp (-2) / (4 * Real.sqrt (n : Real)) <=
      P.real A := by
    simpa only [P, A] using hsource
  have hdiv :
      (Real.exp (-2) / (4 * Real.sqrt (n : Real))) / Real.exp B <=
        P.real G := by
    apply (div_le_iff₀ (Real.exp_pos B)).2
    calc
      Real.exp (-2) / (4 * Real.sqrt (n : Real)) <=
          Real.exp B * P.real G := hsourceReal.trans hcompareReal
      _ = P.real G * Real.exp B := mul_comm _ _
  change Real.exp (-2 - B) / (4 * Real.sqrt (n : Real)) <= P.real G
  rw [Real.exp_sub]
  convert hdiv using 1 <;> ring

/-! ## Transfer to the scheduled Rademacher logarithmic event -/

/-- Scheduled one-height logarithmic ballot lower bound, with the sole
remaining schedule condition displayed as the geometric box budget. -/
theorem
    exists_three_eighths_mul_exp_neg_certificateBudget_div_sqrt_le_harper1144LogBallot :
    ∃ J : Nat, ∀ d start : Nat, J + d <= start -> ∀ n : Nat, 0 < n ->
      ∀ y : Nat, Problem520.harperBlockEndpoint (start + n) <= y ->
        ∀ t : Real,
          (1 / 2 : Real) ^ (d + 1) < |t| ->
          |t| <= (1 / 2 : Real) ^ d ->
          64 * (1 / 2 : Real) ^ start <=
              (1 / 2 : Real) *
                (Real.exp
                    (-2 - harper1144GaussianLogFenceCertificateBudget) /
                  (4 * Real.sqrt (n : Real))) ->
            (3 / 8 : Real) *
                (Real.exp
                    (-2 - harper1144GaussianLogFenceCertificateBudget) /
                  (4 * Real.sqrt (n : Real))) <=
              (Problem520.harperTiltedCubeLaw y t).real
                (harper1144LogBallotCubeEvent y start n t) := by
  obtain ⟨Jtransfer, htransfer⟩ :=
    exists_three_eighths_mul_gaussianLogBallot_le_tiltedLogBallot
  obtain ⟨Jvar, hvar⟩ :=
    Problem520.exists_harperScheduledCentralBandVarianceVector_quarter_half
  refine ⟨max 16 (max Jtransfer Jvar), ?_⟩
  intro d start hstart n hn y hy t htLower htUpper hbudget
  have hstart16 : 16 <= start := by omega
  have hstart8 : 8 <= start := by omega
  have hstartTransfer : Jtransfer + d <= start := by omega
  have hstartVar : Jvar + d <= start := by omega
  let variance : Fin n -> NNReal := fun i =>
    Problem520.harperLinearBlockVarianceNNReal y
      (Problem520.harperScheduledPrimeBlock y
        (start + (i : Nat))) t t
  let Q : Measure (Fin n -> Real) :=
    Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
  let coreMass : Real :=
    Real.exp (-2 - harper1144GaussianLogFenceCertificateBudget) /
      (4 * Real.sqrt (n : Real))
  have hvarianceVector := hvar d start hstartVar n y hy t htLower htUpper
    (fun _i : Fin n => t) (by intro i; simp)
  have hlower : ∀ i, (1 / 4 : NNReal) <= variance i := by
    intro i
    exact_mod_cast (hvarianceVector i).1.le
  have hupper : ∀ i, variance i <= (1 / 2 : NNReal) := by
    intro i
    exact_mod_cast (hvarianceVector i).2.le
  have hcore : coreMass <=
      Q.real (harper1144GaussianLogBallotCoreEvent n) := by
    simpa only [coreMass, Q] using
      exp_neg_certificateBudget_div_sqrt_le_gaussianLogBallotCore
        n hn variance hlower hupper
  have hcontracted : coreMass <=
      Q.real (harper1144ContractedGaussianLogBallotEvent start n) :=
    hcore.trans (measureReal_mono
      (harper1144GaussianLogBallotCoreEvent_subset_contracted hstart16))
  have hvarianceUpperReal : ∀ i : Fin n,
      Problem520.harperLinearBlockVariance y
          (Problem520.harperScheduledPrimeBlock y
            (start + (i : Nat))) t t <= (1 / 2 : Real) := by
    intro i
    exact (hvarianceVector i).2.le
  have hbox :
      Q.real (Problem520.harperCoordinateBox
        (Problem520.harperScheduledModerateRadius start n))ᶜ <=
        64 * (1 / 2 : Real) ^ start := by
    simpa only [Q, variance, Problem520.harperGaussianBlockLaw] using
      harperScheduledGaussianProductMeasure_box_compl_le
        t hstart8 hvarianceUpperReal
  have hboxBudget :
      Q.real (Problem520.harperCoordinateBox
        (Problem520.harperScheduledModerateRadius start n))ᶜ <=
        (1 / 2 : Real) * coreMass :=
    hbox.trans (by simpa only [coreMass] using hbudget)
  have hmain := htransfer d start hstartTransfer n y hy t htLower htUpper
    coreMass
  simpa only [Q, variance, coreMass,
    Problem520.harperGaussianBlockLaw] using hmain hcontracted hboxBudget

/-- The base-four ceiling supplies exactly one inverse square root. -/
theorem half_pow_clog_four_le_inv_sqrt
    {n : Nat} (hn : 0 < n) :
    (1 / 2 : Real) ^ Nat.clog 4 n <=
      1 / Real.sqrt (n : Real) := by
  let k := Nat.clog 4 n
  have hnpowNat : n <= 4 ^ k := by
    dsimp only [k]
    exact Nat.le_pow_clog (by norm_num) n
  have hnpowReal : (n : Real) <= (4 : Real) ^ k := by
    exact_mod_cast hnpowNat
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hsqrtPos : 0 < Real.sqrt (n : Real) := Real.sqrt_pos.2 hnReal
  have htwoPowPos : 0 < (2 : Real) ^ k := by positivity
  have hsq : ((2 : Real) ^ k) ^ (2 : Nat) = (4 : Real) ^ k := by
    calc
      ((2 : Real) ^ k) ^ (2 : Nat) =
          (2 : Real) ^ (k * 2) := (pow_mul _ k 2).symm
      _ = (2 : Real) ^ (2 * k) := by rw [Nat.mul_comm]
      _ = ((2 : Real) ^ (2 : Nat)) ^ k := pow_mul _ 2 k
      _ = (4 : Real) ^ k := by norm_num
  have hsqrt : Real.sqrt (n : Real) <= (2 : Real) ^ k := by
    rw [Real.sqrt_le_iff]
    exact ⟨htwoPowPos.le, by simpa only [hsq] using hnpowReal⟩
  rw [one_div_pow]
  exact one_div_le_one_div_of_le hsqrtPos hsqrt

/-- A sufficiently late fixed part of the canonical logarithmic guard
absorbs the Gaussian moderate-box complement uniformly in the path length. -/
theorem exists_harperTerminalGuardStart_logFence_gaussian_box_budget :
    ∃ J₀ : Nat, ∀ J : Nat, J₀ <= J -> ∀ n : Nat, 0 < n ->
      64 * (1 / 2 : Real) ^ harperTerminalGuardStart J n <=
        (1 / 2 : Real) *
          (Real.exp
              (-2 - harper1144GaussianLogFenceCertificateBudget) /
            (4 * Real.sqrt (n : Real))) := by
  let ε : Real :=
    Real.exp (-2 - harper1144GaussianLogFenceCertificateBudget) / 512
  have hε : 0 < ε := by
    dsimp only [ε]
    positivity
  have hq : Tendsto (fun J : Nat => (1 / 2 : Real) ^ J)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hevent : ∀ᶠ J : Nat in atTop, (1 / 2 : Real) ^ J < ε :=
    (tendsto_order.mp hq).2 ε hε
  obtain ⟨J₀, hJ₀⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨J₀, ?_⟩
  intro J hJ n hn
  have hfixed : (1 / 2 : Real) ^ J <= ε := (hJ₀ J hJ).le
  have hclog := half_pow_clog_four_le_inv_sqrt hn
  unfold harperTerminalGuardStart
  rw [pow_add]
  calc
    64 * ((1 / 2 : Real) ^ J *
          (1 / 2 : Real) ^ Nat.clog 4 n) <=
        64 * (ε * (1 / Real.sqrt (n : Real))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul hfixed hclog (by positivity) hε.le
    _ = (1 / 2 : Real) *
        (Real.exp
            (-2 - harper1144GaussianLogFenceCertificateBudget) /
          (4 * Real.sqrt (n : Real))) := by
      dsimp only [ε]
      ring

/-- The formerly missing one-height lower bound on the exact canonical
guarded schedule.  It uses the same logarithmic event and start rule as the
two-height overlap-shell estimate. -/
theorem exists_harper1144LogBallotGuarded_oneHeight_lower :
    ∃ J : Nat, ∀ n : Nat, 0 < n ->
      let start := harperTerminalGuardStart J n
      let y := Problem520.harperBlockEndpoint (start + n)
      ∀ t ∈ harperLowerVerticalBand,
        (3 / 32 : Real) *
            Real.exp
              (-2 - harper1144GaussianLogFenceCertificateBudget) /
              Real.sqrt (n : Real) <=
          (Problem520.harperTiltedCubeLaw y t).real
            (harper1144LogBallotCubeEvent y start n t) := by
  obtain ⟨Jballot, hballot⟩ :=
    exists_three_eighths_mul_exp_neg_certificateBudget_div_sqrt_le_harper1144LogBallot
  obtain ⟨Jbox, hbox⟩ :=
    exists_harperTerminalGuardStart_logFence_gaussian_box_budget
  let J : Nat := max Jbox (Jballot + 1)
  refine ⟨J, ?_⟩
  intro n hn
  dsimp only
  let start := harperTerminalGuardStart J n
  let y := Problem520.harperBlockEndpoint (start + n)
  have hJbox : Jbox <= J := le_max_left _ _
  have hJballot : Jballot + 1 <= J := le_max_right _ _
  have hstartBallot : Jballot + 1 <= start :=
    hJballot.trans (Nat.le_add_right J (Nat.clog 4 n))
  have hbudget := hbox J hJbox n hn
  intro t ht
  have htBounds : (1 / 3 : Real) <= t ∧ t <= (1 / 2 : Real) := ht
  have htPositive : 0 < t := by linarith
  have htLower : (1 / 2 : Real) ^ (1 + 1) < |t| := by
    rw [abs_of_pos htPositive]
    norm_num
    linarith
  have htUpper : |t| <= (1 / 2 : Real) ^ (1 : Nat) := by
    rw [abs_of_pos htPositive]
    norm_num
    exact htBounds.2
  have hmain := hballot 1 start hstartBallot n hn y le_rfl t
    htLower htUpper hbudget
  calc
    (3 / 32 : Real) *
          Real.exp
            (-2 - harper1144GaussianLogFenceCertificateBudget) /
            Real.sqrt (n : Real) =
        (3 / 8 : Real) *
          (Real.exp
              (-2 - harper1144GaussianLogFenceCertificateBudget) /
            (4 * Real.sqrt (n : Real))) := by ring
    _ <= (Problem520.harperTiltedCubeLaw y t).real
          (harper1144LogBallotCubeEvent y start n t) := hmain

#print axioms Erdos.Problem1144.harper1144GaussianFence_exponent_le
#print axioms Erdos.Problem1144.gaussianWalkDeepAtSplit_fence_probability_le
#print axioms Erdos.Problem1144.gaussianWalkDeepAtSplit_fence_probability_le_invSq
#print axioms Erdos.Problem1144.gaussianWalkDeepAtTime_fence_probability_le_invSq
#print axioms Erdos.Problem1144.gaussianWalkDeepBeforeTerminal_probability_le
#print axioms Erdos.Problem1144.gaussianWalkTerminalDeep_fence_probability_le
#print axioms Erdos.Problem1144.flat_diff_auxFence_subset_deepBeforeTerminal_union_terminal
#print axioms Erdos.Problem1144.flat_diff_auxFence_probability_le
#print axioms Erdos.Problem1144.harper1144GaussianFence_error_constant_le
#print axioms Erdos.Problem1144.quarter_exp_neg_two_div_sqrt_le_flat_inter_auxFence
#print axioms Erdos.Problem1144.exp_neg_certificateBudget_div_sqrt_le_gaussianLogBallotCore
#print axioms Erdos.Problem1144.exists_three_eighths_mul_exp_neg_certificateBudget_div_sqrt_le_harper1144LogBallot
#print axioms Erdos.Problem1144.exists_harperTerminalGuardStart_logFence_gaussian_box_budget
#print axioms Erdos.Problem1144.exists_harper1144LogBallotGuarded_oneHeight_lower

end

end Problem1144
end Erdos
