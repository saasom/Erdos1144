import Erdos.Problem1144.HarperShiftedLatticeAveraging
import Erdos.Problem1144.HarperPathSuffix

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Shifted-lattice comparison for translated suffix corridors

The overlap-shell argument exposes a common prefix and leaves a suffix whose
partial-sum barriers have been translated by the two prefix endpoints.  This
module specializes the shifted-lattice path lift to arbitrary such corridors.
The first theorem below is deliberately geometric: a one-unit total
coordinate enlargement sends any paired corridor into the same corridor with
both barriers relaxed by one.
-/

/-- The paired partial-sum corridor obtained by adding one unit of room on
both sides. -/
def harperPairedRelaxedPartialSumBarrierSet {n : Nat}
    (lower upper : Fin n → Real) : Set (Fin n → Real × Real) :=
  harperPairedPartialSumBarrierSet
    (fun k ↦ lower k - 1) (fun k ↦ upper k + 1)

theorem measurableSet_harperPairedRelaxedPartialSumBarrierSet
    {n : Nat} (lower upper : Fin n → Real) :
    MeasurableSet (harperPairedRelaxedPartialSumBarrierSet lower upper) :=
  measurableSet_harperPairedPartialSumBarrierSet _ _

/-- A coordinatewise perturbation whose total size is at most one sends an
arbitrary paired partial-sum corridor into its one-unit relaxation. -/
theorem coordinateNeighborhood_pairedBarrier_subset_relaxed
    {n : Nat} (lower upper epsilon : Fin n → Real)
    (hepsilon : ∀ i, 0 ≤ epsilon i)
    (hsum : (∑ i, epsilon i) ≤ 1) :
    harperPairPathCoordinateNeighborhood
        (harperPairedPartialSumBarrierSet lower upper) epsilon ⊆
      harperPairedRelaxedPartialSumBarrierSet lower upper := by
  intro y hy
  obtain ⟨x, hx, hcoordinate⟩ := hy
  have hxPair :
      (fun i ↦ (x i).1) ∈
          Problem520.harperPartialSumBarrierSet lower upper ∧
        (fun i ↦ (x i).2) ∈
          Problem520.harperPartialSumBarrierSet lower upper := hx
  have hinside (b : Bool) :
      (fun i ↦ if b then (y i).2 else (y i).1) ∈
        Problem520.harperPartialSumBarrierSet
          (fun k ↦ lower k - 1) (fun k ↦ upper k + 1) := by
    let xp : Fin n → Real := fun i ↦ if b then (x i).2 else (x i).1
    let yp : Fin n → Real := fun i ↦ if b then (y i).2 else (y i).1
    have hxp : xp ∈ Problem520.harperPartialSumBarrierSet lower upper := by
      cases b with
      | false => simpa only [xp, if_false] using hxPair.1
      | true => simpa only [xp, if_true] using hxPair.2
    have hcoord : ∀ i, |yp i - xp i| ≤ epsilon i := by
      intro i
      cases b with
      | false => simpa only [yp, xp, if_false] using (hcoordinate i).1
      | true => simpa only [yp, xp, if_true] using (hcoordinate i).2
    intro k
    have hdiff := abs_harperPathPartialSum_sub_le_total_of_coordinatewise
      hepsilon hcoord k
    have hdiff' :
        |Problem520.harperPathPartialSum yp k -
            Problem520.harperPathPartialSum xp k| ≤ 1 :=
      hdiff.trans hsum
    have hxbounds :=
      Problem520.mem_harperPartialSumBarrierSet.mp hxp k
    have hdiffBounds := abs_le.mp hdiff'
    change
      lower k - 1 ≤ Problem520.harperPathPartialSum yp k ∧
        Problem520.harperPathPartialSum yp k ≤ upper k + 1
    constructor <;> linarith
  change
    (fun i ↦ (y i).1) ∈
        Problem520.harperPartialSumBarrierSet
          (fun k ↦ lower k - 1) (fun k ↦ upper k + 1) ∧
      (fun i ↦ (y i).2) ∈
        Problem520.harperPartialSumBarrierSet
          (fun k ↦ lower k - 1) (fun k ↦ upper k + 1)
  exact ⟨by simpa using hinside false, by simpa using hinside true⟩

/-- Whole-path shifted-lattice comparison for an arbitrary bounded paired
partial-sum corridor.  The caller supplies a coordinate envelope `R` and the
single numerical check placing that envelope in the scheduled moderate
window.  All lattice-retention losses are absorbed into `4 * exp 4`. -/
theorem exists_harperScheduledTwoHeightPairedBarrier_le_gaussianRelaxed :
    ∃ J : Nat, ∀ shell start n y : Nat,
      J + (shell + 1) ≤ start →
      Problem520.harperBlockEndpoint (start + n) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (shell + 1) < |t - s| →
              ∀ lower upper R : Fin n → Real,
                (∀ x ∈ harperPairedPartialSumBarrierSet lower upper,
                  ∀ i, |(x i).1| ≤ R i ∧ |(x i).2| ≤ R i) →
                (∀ i, 2 * R i + 5 ≤
                  (1 / 16 : Real) *
                    Real.sqrt (((2 ^ (start + i.val) : Nat) : Real))) →
                (Measure.pi (fun i : Fin n ↦
                  harperTwoHeightPrimeBlockVectorLaw y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + i.val)) t s)).real
                    (harperPairedPartialSumBarrierSet lower upper) ≤
                  4 * Real.exp 4 *
                    (Measure.pi (fun i : Fin n ↦
                      harperTwoHeightGaussianLaw y
                        (Problem520.harperScheduledPrimeBlock y
                          (start + i.val)) t s)).real
                      (harperPairedRelaxedPartialSumBarrierSet lower upper) := by
  obtain ⟨Jpath, hpath⟩ :=
    exists_harperScheduledTwoHeightRelativeShiftedPath_le
  let J := max 6 Jpath
  refine ⟨J, ?_⟩
  intro shell start n y hstart hy t ht s hs hsep lower upper R
    hcoordinate hmoderate
  have hstartSix : 6 ≤ start := by
    dsimp only [J] at hstart
    omega
  have hstartPath : Jpath + (shell + 1) ≤ start := by
    dsimp only [J] at hstart
    omega
  let delta : Fin n → Real := fun i ↦
    Problem520.harperScheduledRelativeIntervalWidth (start + i.val)
  let h : Fin n → Real := fun i ↦
    harperScheduledBivariateExpansionRadius (start + i.val)
  let period : Fin n → Real := fun i ↦
    harperShiftedLatticePeriod (delta i) (h i)
  have hdelta (i : Fin n) : 0 ≤ delta i :=
    (Problem520.harperScheduledRelativeIntervalWidth_pos _).le
  have hh (i : Fin n) : 0 ≤ h i :=
    (harperScheduledBivariateExpansionRadius_pos _).le
  have hperiodPos (i : Fin n) : 0 < period i := by
    dsimp only [period, delta, h, harperShiftedLatticePeriod]
    exact add_pos_of_pos_of_nonneg
      (Problem520.harperScheduledRelativeIntervalWidth_pos _)
      (mul_nonneg (by norm_num)
        (harperScheduledBivariateExpansionRadius_pos _).le)
  have hbounded :
      ∀ x ∈ harperPairedPartialSumBarrierSet lower upper, ∀ i,
        (x i).1 ∈ Icc (-(R i)) (R i) ∧
          (x i).2 ∈ Icc (-(R i)) (R i) := by
    intro x hx i
    exact ⟨abs_le.mp (hcoordinate x hx i).1,
      abs_le.mp (hcoordinate x hx i).2⟩
  have hgeometry :
      ∀ phi : Fin n → UnitAddCircle × UnitAddCircle,
        ∃ active : Finset (Fin n → Int × Int),
          harperPairedPartialSumBarrierSet lower upper ∩
              harperShiftedPairPathCoreSet delta h phi ⊆
            ⋃ z ∈ active,
              harperShiftedPairPathCoreCell delta h phi z ∧
          (∀ z ∈ active, ∀ i,
            let j := start + i.val
            let delta :=
              Problem520.harperScheduledRelativeIntervalWidth j
            let h := harperScheduledBivariateExpansionRadius j
            let a := ((z i).1 : Real) +
              harperUnitPhaseRepresentative (phi i).1
            let b := ((z i).2 : Real) +
              harperUnitPhaseRepresentative (phi i).2
            |a * harperShiftedLatticePeriod delta h| +
                |b * harperShiftedLatticePeriod delta h| + 3 ≤
              (1 / 16 : Real) *
                Real.sqrt (((2 ^ j : Nat) : Real))) ∧
          (⋃ z ∈ active,
              harperShiftedPairPathFullCell delta h phi z) ⊆
            harperPairedRelaxedPartialSumBarrierSet lower upper := by
    intro phi
    obtain ⟨active, hcover, hmeets⟩ :=
      exists_finite_shiftedPairPathCoreCell_cover_of_bounded
        (harperPairedPartialSumBarrierSet lower upper)
        delta h R phi (fun i ↦ by
          simpa only [period] using hperiodPos i) hbounded
    refine ⟨active, hcover, ?_, ?_⟩
    · intro z hz i
      dsimp only
      obtain ⟨x, hxBarrier, hxCell⟩ := hmeets z hz
      have hxAll :
          (x i).1 ∈ harperShiftedCoreCell
              (delta i) (h i) (phi i).1 (z i).1 ∧
            (x i).2 ∈ harperShiftedCoreCell
              (delta i) (h i) (phi i).2 (z i).2 := by
        simpa only [harperShiftedPairPathCoreCell, Set.mem_pi,
          Set.mem_univ, forall_const, harperShiftedPairCoreCell,
          Set.mem_prod] using hxCell i
      have hdeltaOne : delta i ≤ 1 := by
        exact Problem520.harperScheduledRelativeIntervalWidth_le_one _
      have ha := abs_shiftedCoreCell_lower_le_abs_add_delta
        (hdelta i) hxAll.1
      have hb := abs_shiftedCoreCell_lower_le_abs_add_delta
        (hdelta i) hxAll.2
      have hxBound := hcoordinate x hxBarrier i
      have hmod := hmoderate i
      dsimp only [delta, h] at ha hb ⊢
      calc
        |(((z i).1 : Real) +
              harperUnitPhaseRepresentative (phi i).1) *
            harperShiftedLatticePeriod
              (Problem520.harperScheduledRelativeIntervalWidth
                (start + i.val))
              (harperScheduledBivariateExpansionRadius
                (start + i.val))| +
          |(((z i).2 : Real) +
              harperUnitPhaseRepresentative (phi i).2) *
            harperShiftedLatticePeriod
              (Problem520.harperScheduledRelativeIntervalWidth
                (start + i.val))
              (harperScheduledBivariateExpansionRadius
                (start + i.val))| + 3 ≤
            2 * R i + 5 := by
              nlinarith
        _ ≤ (1 / 16 : Real) *
            Real.sqrt (((2 ^ (start + i.val) : Nat) : Real)) := hmod
    · apply (iUnion_fullCells_subset_coordinateNeighborhood_of_meets
          (harperPairedPartialSumBarrierSet lower upper)
          delta h phi active hdelta hh hmeets).trans
      apply coordinateNeighborhood_pairedBarrier_subset_relaxed
        lower upper period
      · intro i
        exact (hperiodPos i).le
      · dsimp only [period, delta, h]
        exact sum_harperScheduled_shiftedLatticePeriod_le_one hstartSix
  have hraw := hpath shell start n y hstartPath hy t ht s hs hsep
    (harperPairedPartialSumBarrierSet lower upper)
    (harperPairedRelaxedPartialSumBarrierSet lower upper)
    (measurableSet_harperPairedPartialSumBarrierSet lower upper)
    (by simpa only [delta, h] using hgeometry)
  apply le_four_mul_exp_four_of_harperScheduled_products
    (start := start) (n := n) hstartSix
    measureReal_nonneg measureReal_nonneg
  simpa only [harperPairedRelaxedPartialSumBarrierSet] using hraw

/-! ## The literal translated logarithmic suffix geometry -/

/-- A scalar path whose partial sums lie in the coarse translated suffix
corridor has the required elapsed-time coordinate envelope. -/
theorem abs_coordinate_le_of_suffix_partialSum_guard
    {d n : Nat} (omega : Fin n → Real)
    (hlower : ∀ k : Fin n,
      -64 * ((d + k.val + 1 : Nat) : Real) - 1 ≤
        Problem520.harperPathPartialSum omega k)
    (hupper : ∀ k : Fin n,
      Problem520.harperPathPartialSum omega k ≤ 64 * (d : Real))
    (i : Fin n) :
    |omega i| ≤ 128 * ((d + i.val + 1 : Nat) : Real) + 2 := by
  have habsSum (k : Fin n) :
      |Problem520.harperPathPartialSum omega k| ≤
        64 * ((d + k.val + 1 : Nat) : Real) + 1 := by
    rw [abs_le]
    constructor
    · linarith [hlower k]
    · have hdleNat : d ≤ d + k.val + 1 := by omega
      have hdle : (d : Real) ≤ ((d + k.val + 1 : Nat) : Real) := by
        exact_mod_cast hdleNat
      linarith [hupper k]
  by_cases hi : i.val = 0
  · have hset : Finset.Iic i = {i} := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_singleton]
      constructor
      · intro hji
        apply Fin.eq_of_val_eq
        have hj0 : j.val = 0 := by omega
        exact hj0.trans hi.symm
      · rintro rfl
        exact le_rfl
    have hiBound := habsSum i
    unfold Problem520.harperPathPartialSum at hiBound
    rw [hset, Finset.sum_singleton] at hiBound
    have hnonneg : 0 ≤ 64 * ((d + i.val + 1 : Nat) : Real) + 1 := by
      positivity
    nlinarith
  · let p : Fin n := ⟨i.val - 1, by omega⟩
    have hset : Finset.Iic i = insert i (Finset.Iic p) := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_insert]
      constructor
      · intro hj
        by_cases hji : j = i
        · exact Or.inl hji
        · right
          change j.val ≤ p.val
          dsimp only [p]
          have hne : j.val ≠ i.val := by
            intro heq
            exact hji (Fin.eq_of_val_eq heq)
          omega
      · rintro (rfl | hj)
        · exact le_rfl
        · exact hj.trans (by
            change p.val ≤ i.val
            dsimp only [p]
            omega)
    have hinot : i ∉ Finset.Iic p := by
      simp only [Finset.mem_Iic]
      change ¬ i.val ≤ p.val
      dsimp only [p]
      omega
    have hsplit :
        Problem520.harperPathPartialSum omega i =
          omega i + Problem520.harperPathPartialSum omega p := by
      unfold Problem520.harperPathPartialSum
      rw [hset, Finset.sum_insert hinot]
    have hcoord : omega i =
        Problem520.harperPathPartialSum omega i -
          Problem520.harperPathPartialSum omega p := by
      linarith
    rw [hcoord]
    calc
      |Problem520.harperPathPartialSum omega i -
          Problem520.harperPathPartialSum omega p| ≤
          |Problem520.harperPathPartialSum omega i| +
            |Problem520.harperPathPartialSum omega p| := abs_sub _ _
      _ ≤ (64 * ((d + i.val + 1 : Nat) : Real) + 1) +
          (64 * ((d + p.val + 1 : Nat) : Real) + 1) := by
        exact add_le_add (habsSum i) (habsSum p)
      _ ≤ 128 * ((d + i.val + 1 : Nat) : Real) + 2 := by
        have hp : d + p.val + 1 ≤ d + i.val + 1 := by
          dsimp only [p]
          omega
        exact_mod_cast (show
          (64 * (d + i.val + 1) + 1) +
              (64 * (d + p.val + 1) + 1) ≤
            128 * (d + i.val + 1) + 2 by omega)

/-- Every path in an extendable translated logarithmic suffix corridor has
the sharp pointwise coordinate envelope needed by the local comparison. -/
theorem abs_coordinates_le_of_mem_harperPairedSuffix_logBallot
    {start d m : Nat} (hd : 0 < d)
    (u : Fin d → Real × Real) (v : Fin m → Real × Real)
    (hfull : Fin.addCases u v ∈ harperPairedPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start (d + m))
      (harper1144LogBallotUpperBarrier (d + m)))
    (x : Fin m → Real × Real)
    (hx : x ∈ harperPairedPartialSumBarrierSet
      (harperPairedSuffixLower
        (harper1144LogBallotLowerBarrier start (d + m)) u)
      (harperPairedSuffixUpper
        (harper1144LogBallotUpperBarrier (d + m)) u))
    (i : Fin m) :
    |(x i).1| ≤ 128 * ((d + i.val + 1 : Nat) : Real) + 2 ∧
      |(x i).2| ≤ 128 * ((d + i.val + 1 : Nat) : Real) + 2 := by
  let lower := harperPairedSuffixLower
    (harper1144LogBallotLowerBarrier start (d + m)) u
  let upper := harperPairedSuffixUpper
    (harper1144LogBallotUpperBarrier (d + m)) u
  have hxPair :
      (fun k ↦ (x k).1) ∈
          Problem520.harperPartialSumBarrierSet lower upper ∧
        (fun k ↦ (x k).2) ∈
          Problem520.harperPartialSumBarrierSet lower upper := hx
  have hlower (k : Fin m) :
      -64 * ((d + k.val + 1 : Nat) : Real) - 1 ≤ lower k := by
    exact
      neg_sixtyFour_mul_suffixElapsed_sub_one_le_harperPairedSuffixLower_logBallot
        hd u v hfull k
  have hupper (k : Fin m) : upper k ≤ 64 * (d : Real) := by
    exact harperPairedSuffixUpper_logBallot_le hd u v hfull k
  constructor
  · apply abs_coordinate_le_of_suffix_partialSum_guard
      (fun k ↦ (x k).1)
    · intro k
      exact (hlower k).trans
        (Problem520.mem_harperPartialSumBarrierSet.mp hxPair.1 k).1
    · intro k
      exact (Problem520.mem_harperPartialSumBarrierSet.mp hxPair.1 k).2.trans
        (hupper k)
  · apply abs_coordinate_le_of_suffix_partialSum_guard
      (fun k ↦ (x k).2)
    · intro k
      exact (hlower k).trans
        (Problem520.mem_harperPartialSumBarrierSet.mp hxPair.2 k).1
    · intro k
      exact (Problem520.mem_harperPartialSumBarrierSet.mp hxPair.2 k).2.trans
        (hupper k)

private theorem scheduled_moderate_suffix_nat_bound (i : Nat) :
    (4096 * (i + 1) + 144) ^ 2 ≤ 2 ^ (30 + i) := by
  by_cases hi : i < 2
  · interval_cases i <;> norm_num
  · have hi2 : 2 ≤ i := by omega
    induction i, hi2 using Nat.le_induction with
    | base => norm_num
    | succ i hi ih =>
        have hgrowth :
            (4096 * (i + 1 + 1) + 144) ^ 2 ≤
              2 * (4096 * (i + 1) + 144) ^ 2 := by
          nlinarith
        calc
          (4096 * (i + 1 + 1) + 144) ^ 2 ≤
              2 * (4096 * (i + 1) + 144) ^ 2 := hgrowth
          _ ≤ 2 * 2 ^ (30 + i) := Nat.mul_le_mul_left 2 (ih (by omega))
          _ = 2 ^ (30 + (i + 1)) := by
            rw [show 30 + (i + 1) = (30 + i) + 1 by omega, pow_succ]
            omega

theorem harperScheduled_suffixEnvelope_le_moderateWindow
    {baseStart : Nat} (hstart : 30 ≤ baseStart) (i : Nat) :
    256 * (((i + 1 : Nat) : Real)) + 9 ≤
      (1 / 16 : Real) *
        Real.sqrt (((2 ^ (baseStart + i) : Nat) : Real)) := by
  have hnatBase := scheduled_moderate_suffix_nat_bound i
  have hexponent : 30 + i ≤ baseStart + i := by omega
  have hnatPow : 2 ^ (30 + i) ≤ 2 ^ (baseStart + i) :=
    Nat.pow_le_pow_right (by norm_num) hexponent
  have hnat : (4096 * (i + 1) + 144) ^ 2 ≤ 2 ^ (baseStart + i) :=
    hnatBase.trans hnatPow
  have hreal :
      ((4096 * (i + 1) + 144 : Nat) : Real) ^ 2 ≤
        ((2 ^ (baseStart + i) : Nat) : Real) := by exact_mod_cast hnat
  have hsqrt :
      (16 : Real) * (256 * (((i + 1 : Nat) : Real)) + 9) ≤
        Real.sqrt (((2 ^ (baseStart + i) : Nat) : Real)) := by
    apply Real.le_sqrt_of_sq_le
    convert hreal using 1 <;> push_cast <;> ring
  nlinarith

/-- The centered actual two-height law on an extendable translated suffix
corridor is bounded by the exact covariance Gaussian on the one-unit relaxed
corridor, beginning immediately at the natural coherence scale. -/
theorem exists_harperScheduledTwoHeightCenteredLogBallotSuffix_le_gaussianRelaxed :
    ∃ J : Nat, ∀ shell baseStart d m y : Nat,
      J ≤ baseStart → shell + 1 ≤ d →
      Problem520.harperBlockEndpoint (baseStart + d + m) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (shell + 1) < |t - s| →
              ∀ u : Fin d → Real × Real,
                ∀ v : Fin m → Real × Real,
                  Fin.addCases u v ∈ harperPairedPartialSumBarrierSet
                    (harper1144LogBallotLowerBarrier baseStart (d + m))
                    (harper1144LogBallotUpperBarrier (d + m)) →
                  let lower := harperPairedSuffixLower
                    (harper1144LogBallotLowerBarrier baseStart (d + m)) u
                  let upper := harperPairedSuffixUpper
                    (harper1144LogBallotUpperBarrier (d + m)) u
                  (Measure.pi (fun i : Fin m ↦
                    harperTwoHeightPrimeBlockVectorLaw y
                      (Problem520.harperScheduledPrimeBlock y
                        (baseStart + d + i.val)) t s)).real
                      (harperPairedPartialSumBarrierSet lower upper) ≤
                    4 * Real.exp 4 *
                      (Measure.pi (fun i : Fin m ↦
                        harperTwoHeightGaussianLaw y
                          (Problem520.harperScheduledPrimeBlock y
                            (baseStart + d + i.val)) t s)).real
                        (harperPairedRelaxedPartialSumBarrierSet lower upper) := by
  obtain ⟨Jpath, hpath⟩ :=
    exists_harperScheduledTwoHeightPairedBarrier_le_gaussianRelaxed
  let J := max 30 Jpath
  refine ⟨J, ?_⟩
  intro shell baseStart d m y hstart hd hy t ht s hs hsep u v hfull
  dsimp only
  have hbaseThirty : 30 ≤ baseStart :=
    (le_max_left 30 Jpath).trans hstart
  have hpathStart : Jpath + (shell + 1) ≤ baseStart + d := by
    have hJpath : Jpath ≤ baseStart :=
      (le_max_right 30 Jpath).trans hstart
    omega
  have hdPos : 0 < d := by omega
  let lower := harperPairedSuffixLower
    (harper1144LogBallotLowerBarrier baseStart (d + m)) u
  let upper := harperPairedSuffixUpper
    (harper1144LogBallotUpperBarrier (d + m)) u
  let R : Fin m → Real := fun i ↦
    128 * ((d + i.val + 1 : Nat) : Real) + 2
  apply hpath shell (baseStart + d) m y hpathStart (by
      simpa only [add_assoc] using hy) t ht s hs hsep lower upper R
  · intro x hx i
    simpa only [lower, upper, R] using
      abs_coordinates_le_of_mem_harperPairedSuffix_logBallot
        hdPos u v hfull x hx i
  · intro i
    have hmod := harperScheduled_suffixEnvelope_le_moderateWindow
      hbaseThirty (d + i.val)
    dsimp only [R]
    rw [show
      2 * (128 * ((d + i.val + 1 : Nat) : Real) + 2) + 5 =
          256 * (((d + i.val + 1 : Nat) : Real)) + 9 by ring]
    simpa only [add_assoc] using hmod

end

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.coordinateNeighborhood_pairedBarrier_subset_relaxed
#print axioms Erdos.Problem1144.exists_harperScheduledTwoHeightPairedBarrier_le_gaussianRelaxed
#print axioms Erdos.Problem1144.abs_coordinates_le_of_mem_harperPairedSuffix_logBallot
#print axioms Erdos.Problem1144.exists_harperScheduledTwoHeightCenteredLogBallotSuffix_le_gaussianRelaxed
