import Erdos.Problem1144.HarperNearDiagonalStrip

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# The final two-sided logarithmic ballot event

This module fixes the event needed by the separated-height argument.  Its
upper boundary is pinched by elapsed prefix length, so every prefix of `m`
blocks supplies the fourth-power rooted-density saving `m^-4`.  Its lower
boundary is a linear guard, with the automatic moderate-box lower boundary
retained by taking a maximum.

The event is proved to depend only on the scheduled prime range and to be a
subset of the terminal-capped event.  Consequently the completed
near-diagonal `O(1/n)` estimate applies to it without any further probability
argument.
-/

/-- The forward logarithmic upper boundary.  At elapsed prefix length
`m = k+1` it is exactly `1 - 2 log m`. -/
noncomputable def harper1144LogBallotUpperBarrier
    (n : Nat) (k : Fin n) : Real :=
  1 - 2 * Real.log ((k.val + 1 : Nat) : Real)

/-- A two-sided lower guard of Harper type.  The maximum makes containment in
the previously formalized automatic lower barrier literal. -/
noncomputable def harper1144LogBallotLowerBarrier
    (start n : Nat) (k : Fin n) : Real :=
  max (harperScheduledAutomaticLowerBarrier start n k)
    (-64 * ((k.val + 1 : Nat) : Real))

theorem harper1144LogBallotUpperBarrier_le_one
    (n : Nat) (k : Fin n) :
    harper1144LogBallotUpperBarrier n k ≤ 1 := by
  have hk : (1 : Real) ≤ ((k.val + 1 : Nat) : Real) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : k.val + 1 ≠ 0))
  have hlog := Real.log_nonneg hk
  unfold harper1144LogBallotUpperBarrier
  linarith

theorem harperScheduledAutomaticLowerBarrier_le_logBallotLower
    (start n : Nat) (k : Fin n) :
    harperScheduledAutomaticLowerBarrier start n k ≤
      harper1144LogBallotLowerBarrier start n k := by
  exact le_max_left _ _

/-- Sharp elementary width budget for the pinched corridor. -/
theorem harper1144LogBallot_corridorWidth_le_add_one
    (start n : Nat) (k : Fin n) :
    harper1144LogBallotUpperBarrier n k -
        harper1144LogBallotLowerBarrier start n k ≤
      64 * (n : Real) + 1 := by
  have hupper := harper1144LogBallotUpperBarrier_le_one n k
  have hlower :
      -64 * ((k.val + 1 : Nat) : Real) ≤
        harper1144LogBallotLowerBarrier start n k :=
    le_max_right _ _
  have hk : (k.val + 1 : Real) ≤ n := by
    exact_mod_cast (show k.val + 1 ≤ n by omega)
  push_cast at hk hlower
  linarith

/-- The pinched corridor has only linear width.  This lets the bivariate
local comparison be applied to the whole Markov transition rectangle rather
than to a lattice partition of it. -/
theorem harper1144LogBallot_corridorWidth_le
    (start n : Nat) (k : Fin n) :
    harper1144LogBallotUpperBarrier n k -
        harper1144LogBallotLowerBarrier start n k ≤
      65 * (n : Real) := by
  have hsharp := harper1144LogBallot_corridorWidth_le_add_one start n k
  have hn : (1 : Real) ≤ n := by
    have hklt := k.isLt
    exact_mod_cast (show 1 ≤ n by omega)
  linarith

/-- At the last coordinate, the reverse logarithmic upper boundary is below
the strengthened terminal cap. -/
theorem harper1144LogBallotUpperBarrier_last_le_terminalCap
    {n : Nat} (hn : 0 < n) :
    let k : Fin n := ⟨n - 1, by omega⟩
    harper1144LogBallotUpperBarrier n k ≤
      harperTerminalCappedEventLevel n := by
  dsimp only
  let k : Fin n := ⟨n - 1, by omega⟩
  unfold harper1144LogBallotUpperBarrier
    harperTerminalCappedEventLevel harperTerminalCenteredCap
  have hk : n - 1 + 1 = n := by omega
  change 1 - 2 * Real.log (((n - 1 + 1 : Nat) : Real)) ≤
    -2 * Real.log (n : Real) + 2
  rw [hk]
  linarith

/-- The final finite-cube section event. -/
def harper1144LogBallotCubeEvent
    (y start n : Nat) (t : Real) :
    Set (Problem520.HarperPrimeCube y) :=
  (Problem520.harperScheduledCenteredBlockVectorVarying
      y start n t (fun _i : Fin n ↦ t)) ⁻¹'
    Problem520.harperPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start n)
      (harper1144LogBallotUpperBarrier n)

theorem measurableSet_harper1144LogBallotCubeEvent
    (y start n : Nat) (t : Real) :
    MeasurableSet (harper1144LogBallotCubeEvent y start n t) := by
  exact (Set.toFinite
    (harper1144LogBallotCubeEvent y start n t)).measurableSet

/-- The logarithmic event uses only the primes in its scheduled range. -/
theorem harper1144LogBallotCubeEvent_dependsOn_rangeFrom
    (y start n : Nat) (t : Real) :
    HarperEventDependsOn y
      (Problem520.harperScheduledPrimeRangeFrom y start n)
      (harper1144LogBallotCubeEvent y start n t) := by
  intro eta xi heq
  unfold harper1144LogBallotCubeEvent
  change
    Problem520.harperScheduledCenteredBlockVectorVarying
          y start n t (fun _i : Fin n ↦ t) eta ∈
        Problem520.harperPartialSumBarrierSet
          (harper1144LogBallotLowerBarrier start n)
          (harper1144LogBallotUpperBarrier n) ↔
      Problem520.harperScheduledCenteredBlockVectorVarying
          y start n t (fun _i : Fin n ↦ t) xi ∈
        Problem520.harperPartialSumBarrierSet
          (harper1144LogBallotLowerBarrier start n)
          (harper1144LogBallotUpperBarrier n)
  rw [harperScheduledCenteredBlockVectorVarying_eq_of_eqOn_rangeFrom
    y start n t (fun _i : Fin n ↦ t) eta xi heq]

/-- The prefix sum in the path vector is literally the centered prime sum on
the first `k+1` scheduled blocks. -/
theorem harper1144_centeredRangeFrom_eq_pathPartialSum
    (y start n : Nat) (t : Real)
    (eta : Problem520.HarperPrimeCube y) (k : Fin n) :
    Problem520.harperCenteredLinearPrimeBlockSum y
        (Problem520.harperScheduledPrimeRangeFrom y start (k.val + 1))
        t t eta =
      Problem520.harperPathPartialSum
        (Problem520.harperScheduledCenteredBlockVectorVarying
          y start n t (fun _i : Fin n ↦ t) eta) k := by
  let v := Problem520.harperScheduledCenteredBlockVectorVarying
    y start n t (fun _i : Fin n ↦ t) eta
  calc
    Problem520.harperCenteredLinearPrimeBlockSum y
        (Problem520.harperScheduledPrimeRangeFrom y start (k.val + 1))
        t t eta =
      ∑ i ∈ Finset.range (k.val + 1),
        Problem520.harperCenteredLinearPrimeBlockSum y
          (Problem520.harperScheduledPrimeBlock y (start + i))
          t t eta := by
            symm
            exact Problem520.sum_harperCenteredLinearPrimeBlockSum_eq_rangeFrom
              y start (k.val + 1) t t eta
    _ = ∑ i : Fin (k.val + 1),
        Problem520.harperCenteredLinearPrimeBlockSum y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t t eta := by
            exact (Fin.sum_univ_eq_sum_range
              (fun i : Nat =>
                Problem520.harperCenteredLinearPrimeBlockSum y
                  (Problem520.harperScheduledPrimeBlock y (start + i))
                  t t eta) (k.val + 1)).symm
    _ = ∑ i : Fin (k.val + 1),
        Problem520.harperPathPrefix (show k.val + 1 ≤ n by omega) v i := by
          rfl
    _ = Problem520.harperPathPartialSum v k :=
      (Problem520.harperPathPartialSum_eq_sum_prefix v k).symm

/-- Membership in the forward-pinched event gives its logarithmic upper
bound at every elapsed prefix, not merely at the terminal coordinate. -/
theorem harperCenteredRangeFrom_le_forwardLog_of_mem_harper1144LogBallot
    (y start n : Nat) (t : Real)
    (eta : Problem520.HarperPrimeCube y)
    (heta : eta ∈ harper1144LogBallotCubeEvent y start n t)
    (k : Fin n) :
    Problem520.harperCenteredLinearPrimeBlockSum y
        (Problem520.harperScheduledPrimeRangeFrom y start (k.val + 1))
        t t eta ≤
      1 - 2 * Real.log ((k.val + 1 : Nat) : Real) := by
  have hpath :=
    (Problem520.mem_harperPartialSumBarrierSet.mp heta k).2
  rw [harper1144_centeredRangeFrom_eq_pathPartialSum y start n t eta k]
  simpa only [harper1144LogBallotUpperBarrier] using hpath

/-- Exact rooted-density consequence of the elapsed-prefix pinch. -/
theorem harperSubsetNormalizedDensity_prefix_le_exp_of_mem_harper1144LogBallot
    (y start n : Nat) (t : Real)
    (eta : Problem520.HarperPrimeCube y)
    (heta : eta ∈ harper1144LogBallotCubeEvent y start n t)
    (k : Fin n) :
    let S := Problem520.harperScheduledPrimeRangeFrom
      y start (k.val + 1)
    let R := (4 / 3 : Real) *
      (Real.sqrt (Problem520.harperBlockEndpoint start : Real))⁻¹
    let Q := ∑ p ∈ S,
      let x : Real := (p.1 : Real)⁻¹
      x - x ^ (2 : Nat)
    harperSubsetNormalizedDensity y S t eta ≤
      Real.exp
        (2 * (1 - 2 * Real.log ((k.val + 1 : Nat) : Real) +
          Problem520.harperLogMainBlockMean y S t t + R) - Q) := by
  dsimp only
  let S := Problem520.harperScheduledPrimeRangeFrom
    y start (k.val + 1)
  let R := (4 / 3 : Real) *
    (Real.sqrt (Problem520.harperBlockEndpoint start : Real))⁻¹
  let Q := ∑ p ∈ S,
    let x : Real := (p.1 : Real)⁻¹
    x - x ^ (2 : Nat)
  have hpos : 0 < harperSubsetNormalizedDensity y S t eta :=
    harperSubsetNormalizedDensity_pos y S t eta
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  rw [log_harperSubsetNormalizedDensity]
  have hTaylor :=
    Problem520.abs_harperLogRangeFrom_sub_centered_add_mean_le
      y start (k.val + 1) t t eta
  have hTaylorUpper := le_of_abs_le hTaylor
  have hcenter :=
    harperCenteredRangeFrom_le_forwardLog_of_mem_harper1144LogBallot
      y start n t eta heta k
  have hnormalizer : Q ≤
      Real.log (harperSubsetOneHeightNormalizer y S) := by
    exact sum_inv_sub_sq_le_log_harperSubsetOneHeightNormalizer y S
  change
    2 * Problem520.harperLogBlockSum y S t eta -
          Real.log (harperSubsetOneHeightNormalizer y S) ≤
      2 * (1 - 2 * Real.log ((k.val + 1 : Nat) : Real) +
        Problem520.harperLogMainBlockMean y S t t + R) - Q
  change
    Problem520.harperLogBlockSum y S t eta -
        (Problem520.harperCenteredLinearPrimeBlockSum y S t t eta +
          Problem520.harperLogMainBlockMean y S t t) ≤ R at hTaylorUpper
  change Problem520.harperCenteredLinearPrimeBlockSum y S t t eta ≤
    1 - 2 * Real.log ((k.val + 1 : Nat) : Real) at hcenter
  nlinarith

/-- The fourth-power prefix cancellation in its final explicit form. -/
theorem exists_harper1144LogBallot_prefixDensity_le_powTwo_div_fourth :
    ∃ B > 0, ∃ J : Nat,
      ∀ start n y : Nat, J + 1 ≤ start →
        Problem520.harperBlockEndpoint (start + n) ≤ y →
          ∀ s ∈ harperLowerVerticalBand,
            ∀ eta ∈ harper1144LogBallotCubeEvent y start n s,
              ∀ k : Fin n,
                let P := Problem520.harperScheduledPrimeRangeFrom
                  y start (k.val + 1)
                harperSubsetNormalizedDensity y P s eta ≤
                  B * (2 : Real) ^ (k.val + 1) /
                    (((k.val + 1 : Nat) : Real) ^ (4 : Nat)) := by
  obtain ⟨C, hC, J, hflat⟩ :=
    exists_harperCentralPrefixLikelihoodExponent_le
  refine ⟨Real.exp C, Real.exp_pos C, J, ?_⟩
  intro start n y hstart hy s hs eta heta k
  dsimp only
  let m : Nat := k.val + 1
  let P := Problem520.harperScheduledPrimeRangeFrom y start m
  let R : Real := (4 / 3 : Real) *
    (Real.sqrt (Problem520.harperBlockEndpoint start : Real))⁻¹
  let Q : Real := ∑ p ∈ P,
    let x : Real := (p.1 : Real)⁻¹
    x - x ^ (2 : Nat)
  have hcap :=
    harperSubsetNormalizedDensity_prefix_le_exp_of_mem_harper1144LogBallot
      y start n s eta heta k
  have hbase := hflat start n y hstart hy s hs k
  dsimp only at hcap hbase
  have hmpos : (0 : Real) < m := by
    dsimp only [m]
    positivity
  have hexponent :
      2 * (1 - 2 * Real.log (m : Real) +
          Problem520.harperLogMainBlockMean y P s s + R) - Q ≤
        (m : Real) * Real.log 2 + C - 4 * Real.log (m : Real) := by
    dsimp only [P, R, Q, m] at hbase ⊢
    nlinarith
  apply hcap.trans
  calc
    Real.exp
        (2 * (1 - 2 * Real.log (m : Real) +
          Problem520.harperLogMainBlockMean y P s s + R) - Q) ≤
      Real.exp ((m : Real) * Real.log 2 + C -
        4 * Real.log (m : Real)) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp C * (2 : Real) ^ m / (m : Real) ^ (4 : Nat) := by
      rw [show (m : Real) * Real.log 2 + C - 4 * Real.log (m : Real) =
          C + (m : Real) * Real.log 2 - 4 * Real.log (m : Real) by ring,
        Real.exp_sub, Real.exp_add, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : Real) < 2)]
      have hm4 : Real.exp (4 * Real.log (m : Real)) =
          (m : Real) ^ (4 : Nat) := by
        rw [show (4 : Real) * Real.log (m : Real) =
            ((4 : Nat) : Real) * Real.log (m : Real) by norm_num,
          Real.exp_nat_mul, Real.exp_log hmpos]
      rw [hm4]
    _ = _ := by rfl

/-- Prefix localization with the fourth-power pinch exposed.  This is the
pointwise form consumed by the overlap-shell decomposition. -/
theorem
    exists_harper1144LogBallot_correlation_probability_le_powTwo_div_fourth_compl :
    ∃ B > 0, ∃ J : Nat,
      ∀ start n y : Nat, J + 1 ≤ start →
        Problem520.harperBlockEndpoint (start + n) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand, ∀ k : Fin n,
              let P := Problem520.harperScheduledPrimeRangeFrom
                y start (k.val + 1)
              harperTwoHeightCorrelation y t s *
                  (harperTwoHeightCubeLaw y t s).real
                    (harper1144LogBallotCubeEvent y start n t ∩
                      harper1144LogBallotCubeEvent y start n s) ≤
                (B * (2 : Real) ^ (k.val + 1) /
                    (((k.val + 1 : Nat) : Real) ^ (4 : Nat))) *
                  harperSubsetCorrelation y Pᶜ t s := by
  obtain ⟨B, hB, J, hbudget⟩ :=
    exists_harper1144LogBallot_prefixDensity_le_powTwo_div_fourth
  refine ⟨B, hB, J, ?_⟩
  intro start n y hstart hy t ht s hs k
  dsimp only
  let P := Problem520.harperScheduledPrimeRangeFrom
    y start (k.val + 1)
  let S := Problem520.harperScheduledPrimeRangeFrom y start n
  let M : Real := B * (2 : Real) ^ (k.val + 1) /
    (((k.val + 1 : Nat) : Real) ^ (4 : Nat))
  have hPS : P ⊆ S := by
    intro p hp
    have hp' := (Problem520.mem_harperScheduledPrimeRangeFrom p).mp hp
    apply (Problem520.mem_harperScheduledPrimeRangeFrom p).mpr
    refine ⟨hp'.1, hp'.2.trans ?_⟩
    apply Problem520.monotone_harperBlockEndpoint
    omega
  apply harperTwoHeightCorrelation_mul_probability_le_of_prefixCap
    y hPS t s M
  · exact (harper1144LogBallotCubeEvent_dependsOn_rangeFrom
        y start n t).inter
      (harper1144LogBallotCubeEvent_dependsOn_rangeFrom
        y start n s)
  · dsimp only [M]
    positivity
  · intro eta heta
    simpa only [P, M] using
      hbudget start n y hstart hy s hs eta heta.2 k

/-- The two-sided logarithmic event is contained in the earlier flat central
ballot. -/
theorem harper1144LogBallotCubeEvent_subset_central
    (y start n : Nat) (t : Real) :
    harper1144LogBallotCubeEvent y start n t ⊆
      harperCentralLowerBallotCubeEvent y start n t := by
  intro eta heta
  unfold harper1144LogBallotCubeEvent at heta
  change
    Problem520.harperScheduledCenteredBlockVectorVarying
          y start n t (fun _i : Fin n ↦ t) eta ∈
        Problem520.harperPartialSumBarrierSet
          (harper1144LogBallotLowerBarrier start n)
          (harper1144LogBallotUpperBarrier n) at heta
  rw [Problem520.mem_harperPartialSumBarrierSet] at heta
  unfold harperCentralLowerBallotCubeEvent
  change
    Problem520.harperScheduledCenteredBlockVectorVarying
          y start n t (fun _i : Fin n ↦ t) eta ∈
        Problem520.harperPartialSumBarrierSet
          (harperScheduledAutomaticLowerBarrier start n)
          (harperScheduledAutomaticUpperBarrier start n)
  rw [Problem520.mem_harperPartialSumBarrierSet]
  intro k
  have hk := heta k
  constructor
  · exact (harperScheduledAutomaticLowerBarrier_le_logBallotLower
      start n k).trans hk.1
  · have hwidth : 0 ≤
        Problem520.harperCumulativeCellWidth
          (Problem520.harperScheduledRelativeCellWidth start n) k := by
      exact Problem520.harperCumulativeCellWidth_nonneg
        (fun i ↦ (Problem520.harperScheduledRelativeCellWidth_pos
          start n i).le) k
    have hlog := harper1144LogBallotUpperBarrier_le_one n k
    unfold harperScheduledAutomaticUpperBarrier
    linarith [Problem520.harperCumulativeCellWidth_nonneg
      (fun i ↦ (Problem520.harperScheduledRelativeCellWidth_pos
        start n i).le) k]

/-- The logarithmic event is contained in the terminal-capped event used by
the near-diagonal estimate. -/
theorem harper1144LogBallotCubeEvent_subset_terminalCapped
    (y start n : Nat) (t : Real) (hn : 0 < n) :
    harper1144LogBallotCubeEvent y start n t ⊆
      harperTerminalCappedCentralLowerBallotCubeEvent y start n t := by
  intro eta heta
  refine ⟨harper1144LogBallotCubeEvent_subset_central
      y start n t heta, ?_⟩
  let k : Fin n := ⟨n - 1, by omega⟩
  have hk : k.val + 1 = n := by
    dsimp only [k]
    omega
  have hbar :=
    (Problem520.mem_harperPartialSumBarrierSet.mp heta k).2
  have hterminal : Problem520.harperPathPartialSum
      (Problem520.harperScheduledCenteredBlockVectorVarying
        y start n t (fun _i : Fin n ↦ t) eta) k ≤
      harperTerminalCappedEventLevel n :=
    hbar.trans (harper1144LogBallotUpperBarrier_last_le_terminalCap hn)
  rw [harperPathPartialSum_eq_terminal_sum _ k hk] at hterminal
  change Problem520.harperCenteredLinearPrimeBlockSum y
      (Problem520.harperScheduledPrimeRangeFrom y start n) t t eta ≤
    harperTerminalCappedEventLevel n
  rw [← Problem520.sum_harperScheduledCenteredBlockVector_eq_rangeFrom
    y start n t t eta]
  simpa only [Problem520.harperScheduledCenteredBlockVector,
    Problem520.harperScheduledCenteredBlockVectorVarying] using hterminal

theorem harper1144LogBallotCubeEvent_inter_subset_terminalCapped
    (y start n : Nat) (t s : Real) (hn : 0 < n) :
    harper1144LogBallotCubeEvent y start n t ∩
        harper1144LogBallotCubeEvent y start n s ⊆
      harperTerminalCappedCentralLowerBallotCubeEvent y start n t ∩
        harperTerminalCappedCentralLowerBallotCubeEvent y start n s := by
  exact inter_subset_inter
    (harper1144LogBallotCubeEvent_subset_terminalCapped
      y start n t hn)
    (harper1144LogBallotCubeEvent_subset_terminalCapped
      y start n s hn)

/-! ## Near-diagonal handoff for the final event -/

/-- The terminal-capped pointwise estimate descends verbatim to the final
logarithmic event. -/
theorem exists_harper1144LogBallotGuarded_twoHeight_upper :
    ∃ C > 0, ∃ J : Nat, ∀ n : Nat, 0 < n →
      let start := harperTerminalGuardStart J n
      let y := Problem520.harperBlockEndpoint (start + n)
      ∀ t ∈ harperLowerVerticalBand,
      ∀ s ∈ harperLowerVerticalBand,
        harperTwoHeightCorrelation y t s *
            (harperTwoHeightCubeLaw y t s).real
              (harper1144LogBallotCubeEvent y start n t ∩
                harper1144LogBallotCubeEvent y start n s) ≤
          C * (2 : Real) ^ n * (n : Real)⁻¹ := by
  obtain ⟨C, hC, J, hterminal⟩ :=
    exists_harperTerminalGuarded_twoHeight_upper
  refine ⟨C, hC, J, ?_⟩
  intro n hn
  dsimp only
  intro t ht s hs
  let start := harperTerminalGuardStart J n
  let y := Problem520.harperBlockEndpoint (start + n)
  have hmeasure :
      (harperTwoHeightCubeLaw y t s).real
          (harper1144LogBallotCubeEvent y start n t ∩
            harper1144LogBallotCubeEvent y start n s) ≤
        (harperTwoHeightCubeLaw y t s).real
          (harperTerminalCappedCentralLowerBallotCubeEvent y start n t ∩
            harperTerminalCappedCentralLowerBallotCubeEvent y start n s) :=
    measureReal_mono
      (harper1144LogBallotCubeEvent_inter_subset_terminalCapped
        y start n t s hn)
  calc
    harperTwoHeightCorrelation y t s *
          (harperTwoHeightCubeLaw y t s).real
            (harper1144LogBallotCubeEvent y start n t ∩
              harper1144LogBallotCubeEvent y start n s) ≤
        harperTwoHeightCorrelation y t s *
          (harperTwoHeightCubeLaw y t s).real
            (harperTerminalCappedCentralLowerBallotCubeEvent y start n t ∩
              harperTerminalCappedCentralLowerBallotCubeEvent y start n s) :=
      mul_le_mul_of_nonneg_left hmeasure
        (harperTwoHeightCorrelation_pos y t s).le
    _ ≤ C * (2 : Real) ^ n * (n : Real)⁻¹ := by
      simpa only [start, y] using hterminal n hn t ht s hs

/-- The final logarithmic event contributes `O(1/n)` on the entire
reciprocal-frequency near-diagonal strip. -/
theorem exists_harper1144LogBallotGuarded_nearDiagonal_integral_le :
    ∃ C > 0, ∃ J : Nat, ∀ n : Nat, 0 < n →
      let start := harperTerminalGuardStart J n
      let y := Problem520.harperBlockEndpoint (start + n)
      (∫ ts in harperTerminalNearDiagonalStrip n,
          harperTwoHeightCorrelation y ts.1 ts.2 *
            (harperTwoHeightCubeLaw y ts.1 ts.2).real
              (harper1144LogBallotCubeEvent y start n ts.1 ∩
                harper1144LogBallotCubeEvent y start n ts.2)
        ∂( volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) ≤
        C * (n : Real)⁻¹ := by
  obtain ⟨C₀, hC₀, J, hupper⟩ :=
    exists_harper1144LogBallotGuarded_twoHeight_upper
  refine ⟨C₀ / 3, div_pos hC₀ (by norm_num), J, ?_⟩
  intro n hn
  dsimp only
  let start := harperTerminalGuardStart J n
  let y := Problem520.harperBlockEndpoint (start + n)
  let f : Real × Real → Real := fun ts ↦
    harperTwoHeightCorrelation y ts.1 ts.2 *
      (harperTwoHeightCubeLaw y ts.1 ts.2).real
        (harper1144LogBallotCubeEvent y start n ts.1 ∩
          harper1144LogBallotCubeEvent y start n ts.2)
  apply integral_harperTerminalNearDiagonalStrip_le_of_bound
    n hn f C₀ hC₀.le
  · intro ts
    exact mul_nonneg (harperTwoHeightCorrelation_pos y ts.1 ts.2).le
      measureReal_nonneg
  · intro ts ht hs
    simpa only [f, start, y] using hupper n hn ts.1 ht ts.2 hs

end
end Problem1144
end Erdos

#print axioms Erdos.Problem1144.harper1144LogBallotCubeEvent_dependsOn_rangeFrom
#print axioms Erdos.Problem1144.harper1144_centeredRangeFrom_eq_pathPartialSum
#print axioms Erdos.Problem1144.harperSubsetNormalizedDensity_prefix_le_exp_of_mem_harper1144LogBallot
#print axioms Erdos.Problem1144.exists_harper1144LogBallot_prefixDensity_le_powTwo_div_fourth
#print axioms Erdos.Problem1144.exists_harper1144LogBallot_correlation_probability_le_powTwo_div_fourth_compl
#print axioms Erdos.Problem1144.harper1144LogBallotCubeEvent_subset_terminalCapped
#print axioms Erdos.Problem1144.exists_harper1144LogBallotGuarded_twoHeight_upper
#print axioms Erdos.Problem1144.exists_harper1144LogBallotGuarded_nearDiagonal_integral_le
