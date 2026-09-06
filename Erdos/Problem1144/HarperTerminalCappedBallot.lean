import Erdos.Problem1144.HarperTwoHeightDeterministic

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# A terminal-capped Harper ballot

The ordinary central ballot keeps the centered Euler walk below a flat upper
barrier.  For the two-height second moment we also ask that its terminal value
be at most `-2 log n`.  This logarithmic terminal displacement is much smaller
than the walk's natural `sqrt n` scale, while the squared Euler likelihood
gains `1 / n^4`.  The extra room pays for a polynomially guarded omitted
prefix and the terminal separation strip without changing the one-height
ballot scale.

This file proves that deterministic likelihood gain.  The probabilistic task
left downstream is to show that imposing the terminal cap preserves the
one-height ballot mass up to an absolute constant.
-/

/-- The terminal centered height which produces four reciprocal path-length
factors after squaring the Euler likelihood. -/
noncomputable def harperTerminalCenteredCap (n : Nat) : Real :=
  -2 * Real.log (n : Real)

/-- The actual Harper event reserves the universal cumulative lattice-width
bound `2`.  This fixed safety margin is absorbed into the absolute likelihood
constant and leaves the reciprocal path-length gain unchanged. -/
noncomputable def harperTerminalCappedEventLevel (n : Nat) : Real :=
  harperTerminalCenteredCap n + 2

/-- The central lower ballot, strengthened by a logarithmic negative cap on
the full centered scheduled prime sum. -/
def harperTerminalCappedCentralLowerBallotCubeEvent
    (y start n : Nat) (t : Real) :
    Set (Problem520.HarperPrimeCube y) :=
  harperCentralLowerBallotCubeEvent y start n t ∩
    {eta |
      Problem520.harperCenteredLinearPrimeBlockSum y
          (Problem520.harperScheduledPrimeRangeFrom y start n)
          t t eta <= harperTerminalCappedEventLevel n}

theorem measurableSet_harperTerminalCappedCentralLowerBallotCubeEvent
    (y start n : Nat) (t : Real) :
    MeasurableSet
      (harperTerminalCappedCentralLowerBallotCubeEvent y start n t) := by
  exact (Set.toFinite
    (harperTerminalCappedCentralLowerBallotCubeEvent
      y start n t)).measurableSet

theorem harperTerminalCappedCentralLowerBallotCubeEvent_subset
    (y start n : Nat) (t : Real) :
    harperTerminalCappedCentralLowerBallotCubeEvent y start n t ⊆
      harperCentralLowerBallotCubeEvent y start n t := by
  intro eta heta
  exact heta.1

/-- The terminal-capped event still depends only on its scheduled prime
range, so exact prefix localization applies to it without alteration. -/
theorem harperTerminalCappedCentralLowerBallotCubeEvent_dependsOn_rangeFrom
    (y start n : Nat) (t : Real) :
    HarperEventDependsOn y
      (Problem520.harperScheduledPrimeRangeFrom y start n)
      (harperTerminalCappedCentralLowerBallotCubeEvent y start n t) := by
  intro eta xi heq
  constructor
  · intro heta
    refine ⟨(harperCentralLowerBallotCubeEvent_dependsOn_rangeFrom
      y start n t eta xi heq).mp heta.1, ?_⟩
    change Problem520.harperCenteredLinearPrimeBlockSum y
        (Problem520.harperScheduledPrimeRangeFrom y start n)
        t t xi <= harperTerminalCappedEventLevel n
    rw [show Problem520.harperCenteredLinearPrimeBlockSum y
          (Problem520.harperScheduledPrimeRangeFrom y start n)
          t t xi =
        Problem520.harperCenteredLinearPrimeBlockSum y
          (Problem520.harperScheduledPrimeRangeFrom y start n)
          t t eta by
      unfold Problem520.harperCenteredLinearPrimeBlockSum
      apply Finset.sum_congr rfl
      intro p hp
      rw [heq p hp]]
    exact heta.2
  · intro hxi
    refine ⟨(harperCentralLowerBallotCubeEvent_dependsOn_rangeFrom
      y start n t eta xi heq).mpr hxi.1, ?_⟩
    change Problem520.harperCenteredLinearPrimeBlockSum y
        (Problem520.harperScheduledPrimeRangeFrom y start n)
        t t eta <= harperTerminalCappedEventLevel n
    rw [show Problem520.harperCenteredLinearPrimeBlockSum y
          (Problem520.harperScheduledPrimeRangeFrom y start n)
          t t eta =
        Problem520.harperCenteredLinearPrimeBlockSum y
          (Problem520.harperScheduledPrimeRangeFrom y start n)
          t t xi by
      unfold Problem520.harperCenteredLinearPrimeBlockSum
      apply Finset.sum_congr rfl
      intro p hp
      rw [heq p hp]]
    exact hxi.2

/-- Exact terminal likelihood bound before replacing the one-height
normalizer by its reciprocal-prime lower bound. -/
theorem harperSubsetNormalizedDensity_terminal_le_exp_of_mem
    (y start n : Nat) (t : Real)
    (eta : Problem520.HarperPrimeCube y)
    (heta : eta ∈
      harperTerminalCappedCentralLowerBallotCubeEvent y start n t) :
    let S := Problem520.harperScheduledPrimeRangeFrom y start n
    let R := (4 / 3 : Real) *
      (Real.sqrt (Problem520.harperBlockEndpoint start : Real))⁻¹
    harperSubsetNormalizedDensity y S t eta <=
      Real.exp
        (2 * (harperTerminalCappedEventLevel n +
          Problem520.harperLogMainBlockMean y S t t + R) -
          Real.log (harperSubsetOneHeightNormalizer y S)) := by
  dsimp only
  let S := Problem520.harperScheduledPrimeRangeFrom y start n
  let R := (4 / 3 : Real) *
    (Real.sqrt (Problem520.harperBlockEndpoint start : Real))⁻¹
  have hpos : 0 < harperSubsetNormalizedDensity y S t eta :=
    harperSubsetNormalizedDensity_pos y S t eta
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  rw [log_harperSubsetNormalizedDensity]
  have hTaylor :=
    Problem520.abs_harperLogRangeFrom_sub_centered_add_mean_le
      y start n t t eta
  have hTaylorUpper := le_of_abs_le hTaylor
  change
    Problem520.harperLogBlockSum y S t eta -
        (Problem520.harperCenteredLinearPrimeBlockSum y S t t eta +
          Problem520.harperLogMainBlockMean y S t t) <= R at hTaylorUpper
  have hterminal := heta.2
  change Problem520.harperCenteredLinearPrimeBlockSum y S t t eta <=
    harperTerminalCappedEventLevel n at hterminal
  change
    2 * Problem520.harperLogBlockSum y S t eta -
          Real.log (harperSubsetOneHeightNormalizer y S) <=
      2 * (harperTerminalCappedEventLevel n +
          Problem520.harperLogMainBlockMean y S t t + R) -
        Real.log (harperSubsetOneHeightNormalizer y S)
  linarith

/-- Normalizer-free terminal likelihood bound. -/
theorem harperSubsetNormalizedDensity_terminal_le_exp_reciprocalBudget
    (y start n : Nat) (t : Real)
    (eta : Problem520.HarperPrimeCube y)
    (heta : eta ∈
      harperTerminalCappedCentralLowerBallotCubeEvent y start n t) :
    let S := Problem520.harperScheduledPrimeRangeFrom y start n
    let R := (4 / 3 : Real) *
      (Real.sqrt (Problem520.harperBlockEndpoint start : Real))⁻¹
    let Q := ∑ p ∈ S,
      let x : Real := (p.1 : Real)⁻¹
      x - x ^ (2 : Nat)
    harperSubsetNormalizedDensity y S t eta <=
      Real.exp
        (2 * (harperTerminalCappedEventLevel n +
          Problem520.harperLogMainBlockMean y S t t + R) - Q) := by
  dsimp only
  let S := Problem520.harperScheduledPrimeRangeFrom y start n
  let R := (4 / 3 : Real) *
    (Real.sqrt (Problem520.harperBlockEndpoint start : Real))⁻¹
  let Q := ∑ p ∈ S,
    let x : Real := (p.1 : Real)⁻¹
    x - x ^ (2 : Nat)
  have hcap := harperSubsetNormalizedDensity_terminal_le_exp_of_mem
    y start n t eta heta
  have hnormalizer : Q <=
      Real.log (harperSubsetOneHeightNormalizer y S) :=
    sum_inv_sub_sq_le_log_harperSubsetOneHeightNormalizer y S
  dsimp only at hcap
  apply hcap.trans
  apply Real.exp_le_exp.mpr
  linarith

/-- The logarithmic terminal cap subtracts `4 log n` from the full-prefix
likelihood exponent; the fixed lattice safety margin is absorbed into `C`. -/
theorem exists_harperTerminalLikelihoodExponent_le :
    ∃ C ≥ 0, ∃ J : Nat,
      ∀ start n y : Nat, J + 1 ≤ start → 0 < n →
        Problem520.harperBlockEndpoint (start + n) ≤ y →
          ∀ s ∈ harperLowerVerticalBand,
            let S := Problem520.harperScheduledPrimeRangeFrom y start n
            let R := (4 / 3 : Real) *
              (Real.sqrt (Problem520.harperBlockEndpoint start : Real))⁻¹
            let Q := ∑ p ∈ S,
              let x : Real := (p.1 : Real)⁻¹
              x - x ^ (2 : Nat)
            2 * (harperTerminalCappedEventLevel n +
                Problem520.harperLogMainBlockMean y S s s + R) - Q ≤
              (n : Real) * Real.log 2 + C -
                4 * Real.log (n : Real) := by
  obtain ⟨C, hC, J, hprefix⟩ :=
    exists_harperCentralPrefixLikelihoodExponent_le
  refine ⟨C + 4, by linarith, J, ?_⟩
  intro start n y hstart hn hy s hs
  dsimp only
  let k : Fin n := ⟨n - 1, by omega⟩
  have hk : k.val + 1 = n := by
    dsimp [k]
    omega
  have h := hprefix start n y hstart hy s hs k
  dsimp only at h
  rw [hk] at h
  unfold harperTerminalCappedEventLevel harperTerminalCenteredCap
  linarith

/-- Exponential form of the exact `1 / n^4` terminal discount. -/
theorem exists_harperTerminalLikelihoodBudget_le_powTwo_div :
    ∃ B > 0, ∃ J : Nat,
      ∀ start n y : Nat, J + 1 ≤ start → 0 < n →
        Problem520.harperBlockEndpoint (start + n) ≤ y →
          ∀ s ∈ harperLowerVerticalBand,
            let S := Problem520.harperScheduledPrimeRangeFrom y start n
            let R := (4 / 3 : Real) *
              (Real.sqrt (Problem520.harperBlockEndpoint start : Real))⁻¹
            let Q := ∑ p ∈ S,
              let x : Real := (p.1 : Real)⁻¹
              x - x ^ (2 : Nat)
            Real.exp
                (2 * (harperTerminalCappedEventLevel n +
                  Problem520.harperLogMainBlockMean y S s s + R) - Q) ≤
              B * (2 : Real) ^ n * ((n : Real)⁻¹ ^ 4) := by
  obtain ⟨C, hC, J, hbound⟩ :=
    exists_harperTerminalLikelihoodExponent_le
  refine ⟨Real.exp C, Real.exp_pos C, J, ?_⟩
  intro start n y hstart hn hy s hs
  have h := hbound start n y hstart hn hy s hs
  dsimp only at h ⊢
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  calc
    Real.exp
        (2 * (harperTerminalCappedEventLevel n +
          Problem520.harperLogMainBlockMean y
            (Problem520.harperScheduledPrimeRangeFrom y start n) s s +
          (4 / 3 : Real) *
            (Real.sqrt
              (Problem520.harperBlockEndpoint start : Real))⁻¹) -
          ∑ p ∈ Problem520.harperScheduledPrimeRangeFrom y start n,
            ((p.1 : Real)⁻¹ - (p.1 : Real)⁻¹ ^ (2 : Nat))) ≤
      Real.exp ((n : Real) * Real.log 2 + C -
        4 * Real.log (n : Real)) :=
        Real.exp_le_exp.mpr h
    _ = Real.exp C * (2 : Real) ^ n * ((n : Real)⁻¹ ^ 4) := by
      rw [show (n : Real) * Real.log 2 + C -
          4 * Real.log (n : Real) =
        ((((n : Real) * Real.log 2 + C - Real.log (n : Real)) -
          Real.log (n : Real)) - Real.log (n : Real)) -
          Real.log (n : Real) by ring,
        Real.exp_sub, Real.exp_sub, Real.exp_sub, Real.exp_sub,
        Real.exp_add, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : Real) < 2), Real.exp_log hnR]
      field_simp

/-- Pointwise likelihood form used by the localized two-height estimate. -/
theorem exists_harperSubsetNormalizedDensity_terminal_le_powTwo_div :
    ∃ B > 0, ∃ J : Nat,
      ∀ start n y : Nat, J + 1 ≤ start → 0 < n →
        Problem520.harperBlockEndpoint (start + n) ≤ y →
          ∀ s ∈ harperLowerVerticalBand,
            ∀ eta ∈ harperTerminalCappedCentralLowerBallotCubeEvent
              y start n s,
              harperSubsetNormalizedDensity y
                  (Problem520.harperScheduledPrimeRangeFrom y start n)
                  s eta ≤
                B * (2 : Real) ^ n * ((n : Real)⁻¹ ^ 4) := by
  obtain ⟨B, hB, J, hbudget⟩ :=
    exists_harperTerminalLikelihoodBudget_le_powTwo_div
  refine ⟨B, hB, J, ?_⟩
  intro start n y hstart hn hy s hs eta heta
  exact (harperSubsetNormalizedDensity_terminal_le_exp_reciprocalBudget
    y start n s eta heta).trans (hbudget start n y hstart hn hy s hs)

/-- Full-prefix localization for the simultaneous terminal-capped ballot.
The active scheduled range contributes at most `B * 2^n / n^4`; only the
correlation of primes outside the near-full path remains. -/
theorem
    exists_harperTerminalCapped_correlation_probability_le_powTwo_div_compl :
    ∃ B > 0, ∃ J : Nat,
      ∀ start n y : Nat, J + 1 ≤ start → 0 < n →
        Problem520.harperBlockEndpoint (start + n) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              harperTwoHeightCorrelation y t s *
                  (harperTwoHeightCubeLaw y t s).real
                    (harperTerminalCappedCentralLowerBallotCubeEvent
                        y start n t ∩
                      harperTerminalCappedCentralLowerBallotCubeEvent
                        y start n s) ≤
                B * (2 : Real) ^ n * (n : Real)⁻¹ *
                  (n : Real)⁻¹ * (n : Real)⁻¹ *
                  (n : Real)⁻¹ *
                  harperSubsetCorrelation y
                    (Problem520.harperScheduledPrimeRangeFrom
                      y start n)ᶜ t s := by
  obtain ⟨B, hB, J, hpoint⟩ :=
    exists_harperSubsetNormalizedDensity_terminal_le_powTwo_div
  refine ⟨B, hB, J, ?_⟩
  intro start n y hstart hn hy t ht s hs
  let S := Problem520.harperScheduledPrimeRangeFrom y start n
  let M := B * (2 : Real) ^ n * ((n : Real)⁻¹ ^ 4)
  calc
    harperTwoHeightCorrelation y t s *
        (harperTwoHeightCubeLaw y t s).real
          (harperTerminalCappedCentralLowerBallotCubeEvent y start n t ∩
            harperTerminalCappedCentralLowerBallotCubeEvent y start n s) <=
      M * harperSubsetCorrelation y Sᶜ t s := by
        apply harperTwoHeightCorrelation_mul_probability_le_of_prefixCap
          y (show S ⊆ S from Finset.Subset.rfl) t s M
        · exact
            (harperTerminalCappedCentralLowerBallotCubeEvent_dependsOn_rangeFrom
                y start n t).inter
              (harperTerminalCappedCentralLowerBallotCubeEvent_dependsOn_rangeFrom
                y start n s)
        · dsimp [M]
          positivity
        · intro eta heta
          exact hpoint start n y hstart hn hy s hs eta heta.2
    _ = B * (2 : Real) ^ n * (n : Real)⁻¹ * (n : Real)⁻¹ *
        (n : Real)⁻¹ * (n : Real)⁻¹ *
        harperSubsetCorrelation y
          (Problem520.harperScheduledPrimeRangeFrom y start n)ᶜ t s := by
      dsimp [M, S]
      ring

end
end Problem1144
end Erdos

#print axioms Erdos.Problem1144.harperTerminalCappedCentralLowerBallotCubeEvent_dependsOn_rangeFrom
#print axioms Erdos.Problem1144.harperSubsetNormalizedDensity_terminal_le_exp_reciprocalBudget
#print axioms Erdos.Problem1144.exists_harperTerminalLikelihoodExponent_le
#print axioms Erdos.Problem1144.exists_harperTerminalLikelihoodBudget_le_powTwo_div
#print axioms Erdos.Problem1144.exists_harperSubsetNormalizedDensity_terminal_le_powTwo_div
#print axioms Erdos.Problem1144.exists_harperTerminalCapped_correlation_probability_le_powTwo_div_compl
