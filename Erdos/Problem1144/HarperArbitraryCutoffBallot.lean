import Erdos.Problem1144.HarperOverlapShellAssembly
import Erdos.Problem1144.HarperPartialBlockScreen

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Logarithmic ballot bounds at arbitrary cutoffs

The core ballot path uses all completed scheduled blocks below `y`.  The
remaining coordinates in the one unfinished block form the independent
screen controlled in `HarperPartialBlockScreen`.  This lifts the fixed-start
one- and two-height estimates from exact scheduled endpoints to every
ambient cutoff between consecutive endpoints.
-/

/-- Natural-coherence pointwise shell bound throughout one scheduled
cutoff envelope. -/
theorem exists_harper1144LogBallot_naturalShell_pointwise_le_envelope :
    ∃ C > 0, ∃ J : Nat,
      ∀ start q d m y : Nat, J ≤ start → q + 1 ≤ d → 0 < m →
        Problem520.harperBlockEndpoint (start + (d + m)) ≤ y →
        y < Problem520.harperBlockEndpoint (start + (d + m) + 1) →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (q + 1) < |t - s| →
                harperTwoHeightCorrelation y t s *
                    (harperTwoHeightCubeLaw y t s).real
                      (harper1144LogBallotCubeEvent y start (d + m) t ∩
                        harper1144LogBallotCubeEvent y start (d + m) s) ≤
                  C * (4 : Real) ^ start *
                    (2 : Real) ^ (q + 1) /
                    (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
                    ((((d + 1 : Nat) : Real) ^ (2 : Nat)) *
                      (m : Real)⁻¹) := by
  obtain ⟨B, hB, L, hL, Jroot, hroot⟩ :=
    exists_harper1144LogBallot_rooted_naturalSuffix_le
  obtain ⟨D, hD, Jcorr, hcorr⟩ :=
    exists_harperScheduledPrefixComplement_shell_le_four_pow_start_envelope
  let K : Real :=
    4 * Real.exp 4 * (4096 * 68 * (536 * L + 68))
  let C : Real := B * D * K
  let J : Nat := max Jroot Jcorr
  refine ⟨C, by dsimp only [C, K]; positivity, J, ?_⟩
  intro start q d m y hstart hqd hm hlower hupper t ht s hs hsep
  have hstartRoot : Jroot ≤ start :=
    (le_max_left Jroot Jcorr).trans hstart
  have hstartCorr : Jcorr ≤ start :=
    (le_max_right Jroot Jcorr).trans hstart
  have hlowerRoot :
      Problem520.harperBlockEndpoint (start + d + m) ≤ y := by
    simpa only [add_assoc] using hlower
  have hrooted := hroot start q d m y hstartRoot hqd hm hlowerRoot
    t ht s hs hsep
  dsimp only at hrooted
  have hcomp := hcorr q start (q + 1) (d + m) y hstartCorr
    (by omega) (by omega) hlower hupper t ht s hs hsep
  have hleftNonneg :
      0 ≤ B * (2 : Real) ^ (q + 1) /
        (((q + 1 : Nat) : Real) ^ (4 : Nat)) := by positivity
  have hsuffixNonneg :
      0 ≤ 4 * Real.exp 4 *
        ((4096 * 68 * (536 * L + 68)) *
          (((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹) := by
    positivity
  calc
    harperTwoHeightCorrelation y t s *
          (harperTwoHeightCubeLaw y t s).real
            (harper1144LogBallotCubeEvent y start (d + m) t ∩
              harper1144LogBallotCubeEvent y start (d + m) s) ≤
        ((B * (2 : Real) ^ (q + 1) /
              (((q + 1 : Nat) : Real) ^ (4 : Nat))) *
            harperSubsetCorrelation y
              (Problem520.harperScheduledPrimeRangeFrom
                y start (q + 1))ᶜ t s) *
          (4 * Real.exp 4 *
            ((4096 * 68 * (536 * L + 68)) *
              (((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹)) :=
        hrooted
    _ ≤ ((B * (2 : Real) ^ (q + 1) /
              (((q + 1 : Nat) : Real) ^ (4 : Nat))) *
            (D * (4 : Real) ^ start)) *
          (4 * Real.exp 4 *
            ((4096 * 68 * (536 * L + 68)) *
              (((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹)) := by
      gcongr
    _ = C * (4 : Real) ^ start * (2 : Real) ^ (q + 1) /
          (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
          ((((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹) := by
      dsimp only [C, K]
      ring

/-- Every nonterminal overlap shell has the exact summable weight at an
arbitrary cutoff in the scheduled envelope. -/
theorem exists_harper1144LogBallot_naturalShell_integral_le_envelope :
    ∃ C > 0, ∃ J : Nat, ∀ start : Nat, J ≤ start →
      ∀ n q y : Nat, q + 2 ≤ n →
        Problem520.harperBlockEndpoint (start + n) ≤ y →
        y < Problem520.harperBlockEndpoint (start + n + 1) →
        (∫ ts in harper1144OverlapShell q,
            harperTwoHeightCorrelation y ts.1 ts.2 *
              (harperTwoHeightCubeLaw y ts.1 ts.2).real
                (harper1144LogBallotCubeEvent y start n ts.1 ∩
                  harper1144LogBallotCubeEvent y start n ts.2)
          ∂(volume.restrict harperLowerVerticalBand).prod
            (volume.restrict harperLowerVerticalBand)) ≤
          C * (4 : Real) ^ start *
            harper1144OverlapShellWeight n q := by
  obtain ⟨C₀, hC₀, J, hpoint⟩ :=
    exists_harper1144LogBallot_naturalShell_pointwise_le_envelope
  refine ⟨8 * C₀, by positivity, J, ?_⟩
  intro start hstart n q y hq hlower hupper
  let d : Nat := q + 1
  let m : Nat := n - (q + 1)
  have hm : 0 < m := by dsimp only [m]; omega
  have hsum : d + m = n := by dsimp only [d, m]; omega
  let f : Real × Real → Real := fun ts ↦
    harperTwoHeightCorrelation y ts.1 ts.2 *
      (harperTwoHeightCubeLaw y ts.1 ts.2).real
        (harper1144LogBallotCubeEvent y start n ts.1 ∩
          harper1144LogBallotCubeEvent y start n ts.2)
  have hfNonneg : ∀ ts, 0 ≤ f ts := fun ts ↦
    mul_nonneg (harperTwoHeightCorrelation_pos y ts.1 ts.2).le
      measureReal_nonneg
  have hpoint' : ∀ ts ∈
      harperLowerVerticalBand ×ˢ harperLowerVerticalBand,
      ts ∈ harper1144OverlapShell q →
        f ts ≤ C₀ * (4 : Real) ^ start * (2 : Real) ^ (q + 1) /
          (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
          ((((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹) := by
    intro ts hband hshell
    have hsepInv := (mem_harper1144OverlapShell_iff.mp hshell).1
    have hsep : (1 / 2 : Real) ^ (q + 1) < |ts.1 - ts.2| := by
      rw [show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num, inv_pow]
      exact hsepInv
    have hlower' :
        Problem520.harperBlockEndpoint (start + (d + m)) ≤ y := by
      simpa only [hsum] using hlower
    have hupper' :
        y < Problem520.harperBlockEndpoint (start + (d + m) + 1) := by
      simpa only [hsum] using hupper
    have hmain := hpoint start q d m y hstart (by simp [d]) hm
      hlower' hupper' ts.1 hband.1 ts.2 hband.2 hsep
    simpa only [f, hsum] using hmain
  have hintegral :=
    integral_harper1144OverlapShell_le_of_naturalRooted_bound
      q start d m C₀ hC₀.le f hfNonneg hpoint'
  have hnumeric := harper1144_naturalShell_numeric_le_weight hq
  have hfactor :
      (2 * C₀ / 3) * (4 : Real) ^ start /
          (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
          ((((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹) ≤
        (8 * C₀) * (4 : Real) ^ start *
          harper1144OverlapShellWeight n q := by
    dsimp only [d, m]
    have hmul : 0 ≤ C₀ * (4 : Real) ^ start := by positivity
    rw [show q + 1 + 1 = q + 2 by omega]
    calc
      (2 * C₀ / 3) * (4 : Real) ^ start /
            (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
            ((((q + 1 + 1 : Nat) : Real) ^ (2 : Nat)) *
              ((n - (q + 1) : Nat) : Real)⁻¹) =
          (C₀ * (4 : Real) ^ start) *
            ((2 / 3 : Real) /
              (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
              ((((q + 2 : Nat) : Real) ^ (2 : Nat)) *
                ((n - (q + 1) : Nat) : Real)⁻¹)) := by
        ring
      _ ≤ (C₀ * (4 : Real) ^ start) *
          (8 * harper1144OverlapShellWeight n q) :=
        mul_le_mul_of_nonneg_left hnumeric hmul
      _ = (8 * C₀) * (4 : Real) ^ start *
          harper1144OverlapShellWeight n q := by ring
  exact hintegral.trans (by simpa only [f, hsum] using hfactor)

/-- The last nonterminal shell has the same weight throughout the arbitrary
cutoff envelope. -/
theorem exists_harper1144LogBallot_terminalShell_integral_le_envelope :
    ∃ C > 0, ∃ J : Nat, ∀ start : Nat, J ≤ start →
      ∀ n y : Nat, 0 < n →
        Problem520.harperBlockEndpoint (start + n) ≤ y →
        y < Problem520.harperBlockEndpoint (start + n + 1) →
        (∫ ts in harper1144OverlapShell (n - 1),
            harperTwoHeightCorrelation y ts.1 ts.2 *
              (harperTwoHeightCubeLaw y ts.1 ts.2).real
                (harper1144LogBallotCubeEvent y start n ts.1 ∩
                  harper1144LogBallotCubeEvent y start n ts.2)
          ∂(volume.restrict harperLowerVerticalBand).prod
            (volume.restrict harperLowerVerticalBand)) ≤
          C * (4 : Real) ^ start *
            harper1144OverlapShellWeight n (n - 1) := by
  obtain ⟨C₀, hC₀, J, hterminal⟩ :=
    exists_harperTerminalCapped_correlation_probability_le_powTwo_mul_four_pow_div_sq_envelope
  refine ⟨4 * C₀ / 3, by positivity, J, ?_⟩
  intro start hstart n y hn hlower hupper
  let f : Real × Real → Real := fun ts ↦
    harperTwoHeightCorrelation y ts.1 ts.2 *
      (harperTwoHeightCubeLaw y ts.1 ts.2).real
        (harper1144LogBallotCubeEvent y start n ts.1 ∩
          harper1144LogBallotCubeEvent y start n ts.2)
  let M : Real := C₀ * (2 : Real) ^ n * (n : Real)⁻¹ *
    (n : Real)⁻¹ * (n : Real)⁻¹ * (n : Real)⁻¹ *
      (4 : Real) ^ start
  have hfNonneg : ∀ ts, 0 ≤ f ts := fun ts ↦
    mul_nonneg (harperTwoHeightCorrelation_pos y ts.1 ts.2).le
      measureReal_nonneg
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hpoint : ∀ ts ∈
      harperLowerVerticalBand ×ˢ harperLowerVerticalBand,
      ts ∈ harper1144OverlapShell (n - 1) → f ts ≤ M := by
    intro ts hband _hshell
    have hmeasure :
        (harperTwoHeightCubeLaw y ts.1 ts.2).real
            (harper1144LogBallotCubeEvent y start n ts.1 ∩
              harper1144LogBallotCubeEvent y start n ts.2) ≤
          (harperTwoHeightCubeLaw y ts.1 ts.2).real
            (harperTerminalCappedCentralLowerBallotCubeEvent
                  y start n ts.1 ∩
              harperTerminalCappedCentralLowerBallotCubeEvent
                  y start n ts.2) :=
      measureReal_mono
        (harper1144LogBallotCubeEvent_inter_subset_terminalCapped
          y start n ts.1 ts.2 hn)
    have hbase := hterminal start n y hstart hn hlower hupper
      ts.1 hband.1 ts.2 hband.2
    calc
      f ts ≤ harperTwoHeightCorrelation y ts.1 ts.2 *
          (harperTwoHeightCubeLaw y ts.1 ts.2).real
            (harperTerminalCappedCentralLowerBallotCubeEvent
                  y start n ts.1 ∩
              harperTerminalCappedCentralLowerBallotCubeEvent
                  y start n ts.2) :=
        mul_le_mul_of_nonneg_left hmeasure
          (harperTwoHeightCorrelation_pos y ts.1 ts.2).le
      _ ≤ M := by simpa only [M] using hbase
  have hintegral := integral_harper1144OverlapShell_le_of_bound
    (n - 1) M hM f hfNonneg hpoint
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hnOne : (1 : Real) ≤ n := by exact_mod_cast hn
  have hinvLe : (n : Real)⁻¹ ≤ 1 := (inv_le_one₀ hnR).2 hnOne
  have hpowCancel :
      (2 : Real) ^ n * ((2 : Real) ^ (n - 1))⁻¹ = 2 := by
    have hnSplit : n = (n - 1) + 1 := by omega
    have hpowN : (2 : Real) ^ n = (2 : Real) ^ (n - 1) * 2 := by
      exact (congrArg (fun k : Nat ↦ (2 : Real) ^ k) hnSplit).trans
        (pow_succ (2 : Real) (n - 1))
    rw [hpowN]
    field_simp
  have hweight :
      harper1144OverlapShellWeight n (n - 1) =
        (((n : Real) ^ (2 : Nat)) * 2)⁻¹ := by
    unfold harper1144OverlapShellWeight
    have hfirst : n - 1 + 1 = n := by omega
    have hsecond : n - (n - 1) + 1 = 2 := by omega
    rw [hfirst, hsecond]
    norm_num
  have hfinal :
      M * ((1 / 3 : Real) * ((2 : Real) ^ (n - 1))⁻¹) ≤
        (4 * C₀ / 3) * (4 : Real) ^ start *
          harper1144OverlapShellWeight n (n - 1) := by
    rw [hweight]
    dsimp only [M]
    have hsq : (n : Real)⁻¹ * (n : Real)⁻¹ ≤ 1 := by
      have hinvNonneg : 0 ≤ (n : Real)⁻¹ := by positivity
      nlinarith [mul_nonneg hinvNonneg (sub_nonneg.mpr hinvLe)]
    calc
      C₀ * (2 : Real) ^ n * (n : Real)⁻¹ *
            (n : Real)⁻¹ * (n : Real)⁻¹ * (n : Real)⁻¹ *
            (4 : Real) ^ start *
            ((1 / 3 : Real) * ((2 : Real) ^ (n - 1))⁻¹) =
          (2 * C₀ / 3) * (4 : Real) ^ start *
            ((n : Real)⁻¹ * (n : Real)⁻¹) *
            ((n : Real)⁻¹ * (n : Real)⁻¹) := by
        calc
          _ = (C₀ / 3 * (4 : Real) ^ start *
                ((n : Real)⁻¹ * (n : Real)⁻¹) *
                ((n : Real)⁻¹ * (n : Real)⁻¹)) *
              ((2 : Real) ^ n * ((2 : Real) ^ (n - 1))⁻¹) := by
            ring
          _ = _ := by rw [hpowCancel]; ring
      _ ≤ (2 * C₀ / 3) * (4 : Real) ^ start *
            ((n : Real)⁻¹ * (n : Real)⁻¹) * 1 := by
        gcongr
      _ = (4 * C₀ / 3) * (4 : Real) ^ start *
          (((n : Real) ^ (2 : Nat)) * 2)⁻¹ := by
        field_simp
        ring
  exact hintegral.trans (by simpa only [f] using hfinal)

/-- The ultra-near diagonal likewise has its `O(1/n)` bound at every cutoff
in the scheduled envelope. -/
theorem exists_harper1144LogBallot_nearDiagonal_integral_le_envelope :
    ∃ C > 0, ∃ J : Nat, ∀ start : Nat, J ≤ start →
      ∀ n y : Nat, 0 < n →
        Problem520.harperBlockEndpoint (start + n) ≤ y →
        y < Problem520.harperBlockEndpoint (start + n + 1) →
        (∫ ts in harperTerminalNearDiagonalStrip n,
            harperTwoHeightCorrelation y ts.1 ts.2 *
              (harperTwoHeightCubeLaw y ts.1 ts.2).real
                (harper1144LogBallotCubeEvent y start n ts.1 ∩
                  harper1144LogBallotCubeEvent y start n ts.2)
          ∂(volume.restrict harperLowerVerticalBand).prod
            (volume.restrict harperLowerVerticalBand)) ≤
          C * (4 : Real) ^ start * (n : Real)⁻¹ := by
  obtain ⟨C₀, hC₀, J, hterminal⟩ :=
    exists_harperTerminalCapped_correlation_probability_le_powTwo_mul_four_pow_div_sq_envelope
  refine ⟨C₀ / 3, by positivity, J, ?_⟩
  intro start hstart n y hn hlower hupper
  let f : Real × Real → Real := fun ts ↦
    harperTwoHeightCorrelation y ts.1 ts.2 *
      (harperTwoHeightCubeLaw y ts.1 ts.2).real
        (harper1144LogBallotCubeEvent y start n ts.1 ∩
          harper1144LogBallotCubeEvent y start n ts.2)
  let K : Real := C₀ * (4 : Real) ^ start
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hnOne : (1 : Real) ≤ n := by exact_mod_cast hn
  have hinvLe : (n : Real)⁻¹ ≤ 1 := (inv_le_one₀ hnR).2 hnOne
  have hbound : ∀ ts,
      ts.1 ∈ harperLowerVerticalBand →
      ts.2 ∈ harperLowerVerticalBand →
      f ts ≤ K * (2 : Real) ^ n * (n : Real)⁻¹ := by
    intro ts ht hs
    have hmeasure :
        (harperTwoHeightCubeLaw y ts.1 ts.2).real
            (harper1144LogBallotCubeEvent y start n ts.1 ∩
              harper1144LogBallotCubeEvent y start n ts.2) ≤
          (harperTwoHeightCubeLaw y ts.1 ts.2).real
            (harperTerminalCappedCentralLowerBallotCubeEvent
                  y start n ts.1 ∩
              harperTerminalCappedCentralLowerBallotCubeEvent
                  y start n ts.2) :=
      measureReal_mono
        (harper1144LogBallotCubeEvent_inter_subset_terminalCapped
          y start n ts.1 ts.2 hn)
    have hbase := hterminal start n y hstart hn hlower hupper
      ts.1 ht ts.2 hs
    calc
      f ts ≤ harperTwoHeightCorrelation y ts.1 ts.2 *
          (harperTwoHeightCubeLaw y ts.1 ts.2).real
            (harperTerminalCappedCentralLowerBallotCubeEvent
                  y start n ts.1 ∩
              harperTerminalCappedCentralLowerBallotCubeEvent
                  y start n ts.2) :=
        mul_le_mul_of_nonneg_left hmeasure
          (harperTwoHeightCorrelation_pos y ts.1 ts.2).le
      _ ≤ C₀ * (2 : Real) ^ n * (n : Real)⁻¹ *
            (n : Real)⁻¹ * (n : Real)⁻¹ * (n : Real)⁻¹ *
              (4 : Real) ^ start := hbase
      _ ≤ C₀ * (2 : Real) ^ n * (n : Real)⁻¹ * 1 * 1 * 1 *
              (4 : Real) ^ start := by gcongr
      _ = K * (2 : Real) ^ n * (n : Real)⁻¹ := by
        dsimp only [K]
        ring
  have hresult := integral_harperTerminalNearDiagonalStrip_le_of_bound
    n hn f K hK
    (fun ts ↦ mul_nonneg
      (harperTwoHeightCorrelation_pos y ts.1 ts.2).le measureReal_nonneg)
    hbound
  calc
    (∫ ts in harperTerminalNearDiagonalStrip n,
        harperTwoHeightCorrelation y ts.1 ts.2 *
          (harperTwoHeightCubeLaw y ts.1 ts.2).real
            (harper1144LogBallotCubeEvent y start n ts.1 ∩
              harper1144LogBallotCubeEvent y start n ts.2)
      ∂(volume.restrict harperLowerVerticalBand).prod
        (volume.restrict harperLowerVerticalBand)) ≤
        K / 3 * (n : Real)⁻¹ := by simpa only [f] using hresult
    _ = (C₀ / 3) * (4 : Real) ^ start * (n : Real)⁻¹ := by
      dsimp only [K]
      ring

/-- Summing the terminal strip and every overlap shell gives the complete
`O(1/n)` two-height partition bound at arbitrary cutoffs. -/
theorem exists_harper1144LogBallot_partitioned_integral_le_envelope :
    ∃ C > 0, ∃ J : Nat, ∀ start : Nat, J ≤ start →
      ∀ n y : Nat, 0 < n →
        Problem520.harperBlockEndpoint (start + n) ≤ y →
        y < Problem520.harperBlockEndpoint (start + n + 1) →
        let f : Real × Real → Real := fun ts ↦
          harperTwoHeightCorrelation y ts.1 ts.2 *
            (harperTwoHeightCubeLaw y ts.1 ts.2).real
              (harper1144LogBallotCubeEvent y start n ts.1 ∩
                harper1144LogBallotCubeEvent y start n ts.2)
        (∫ ts in harperTerminalNearDiagonalStrip n, f ts
            ∂(volume.restrict harperLowerVerticalBand).prod
              (volume.restrict harperLowerVerticalBand)) +
          ∑ r ∈ Finset.range n,
            ∫ ts in harper1144OverlapShell r, f ts
              ∂(volume.restrict harperLowerVerticalBand).prod
                (volume.restrict harperLowerVerticalBand) ≤
          C * (4 : Real) ^ start * (n : Real)⁻¹ := by
  obtain ⟨C₀, hC₀, J₀, hnatural⟩ :=
    exists_harper1144LogBallot_naturalShell_integral_le_envelope
  obtain ⟨C₁, hC₁, J₁, hterminal⟩ :=
    exists_harper1144LogBallot_terminalShell_integral_le_envelope
  obtain ⟨C₂, hC₂, J₂, hnear⟩ :=
    exists_harper1144LogBallot_nearDiagonal_integral_le_envelope
  let Cshell : Real := C₀ + C₁
  let C : Real := 4 * Cshell + C₂
  let J : Nat := max (max J₀ J₁) J₂
  refine ⟨C, by dsimp only [C, Cshell]; positivity, J, ?_⟩
  intro start hstart n y hn hlower hupper
  dsimp only
  let f : Real × Real → Real := fun ts ↦
    harperTwoHeightCorrelation y ts.1 ts.2 *
      (harperTwoHeightCubeLaw y ts.1 ts.2).real
        (harper1144LogBallotCubeEvent y start n ts.1 ∩
          harper1144LogBallotCubeEvent y start n ts.2)
  have hstart₀ : J₀ ≤ start :=
    (le_max_left J₀ J₁).trans
      ((le_max_left (max J₀ J₁) J₂).trans hstart)
  have hstart₁ : J₁ ≤ start :=
    (le_max_right J₀ J₁).trans
      ((le_max_left (max J₀ J₁) J₂).trans hstart)
  have hstart₂ : J₂ ≤ start :=
    (le_max_right (max J₀ J₁) J₂).trans hstart
  have hshell (r : Nat) (hr : r < n) :
      (∫ ts in harper1144OverlapShell r, f ts
          ∂(volume.restrict harperLowerVerticalBand).prod
            (volume.restrict harperLowerVerticalBand)) ≤
        Cshell * (4 : Real) ^ start *
          harper1144OverlapShellWeight n r := by
    by_cases hnonterminal : r + 2 ≤ n
    · have hmain := hnatural start hstart₀ n r y hnonterminal
        hlower hupper
      have hweight := harper1144OverlapShellWeight_nonneg n r
      calc
        (∫ ts in harper1144OverlapShell r, f ts
            ∂(volume.restrict harperLowerVerticalBand).prod
              (volume.restrict harperLowerVerticalBand)) ≤
            C₀ * (4 : Real) ^ start *
              harper1144OverlapShellWeight n r := by
          simpa only [f] using hmain
        _ ≤ Cshell * (4 : Real) ^ start *
              harper1144OverlapShellWeight n r := by
          have : C₀ ≤ Cshell := by dsimp only [Cshell]; linarith
          gcongr
    · have hrLast : r = n - 1 := by omega
      subst r
      have hmain := hterminal start hstart₁ n y hn hlower hupper
      have hweight := harper1144OverlapShellWeight_nonneg n (n - 1)
      calc
        (∫ ts in harper1144OverlapShell (n - 1), f ts
            ∂(volume.restrict harperLowerVerticalBand).prod
              (volume.restrict harperLowerVerticalBand)) ≤
            C₁ * (4 : Real) ^ start *
              harper1144OverlapShellWeight n (n - 1) := by
          simpa only [f] using hmain
        _ ≤ Cshell * (4 : Real) ^ start *
              harper1144OverlapShellWeight n (n - 1) := by
          have : C₁ ≤ Cshell := by dsimp only [Cshell]; linarith
          gcongr
  have hsum := sum_harper1144OverlapShell_integrals_le_of_bound
    n hn (Cshell * (4 : Real) ^ start) (by positivity) f
      (fun r hr ↦ hshell r hr)
  have hnear' := hnear start hstart₂ n y hn hlower hupper
  calc
    (∫ ts in harperTerminalNearDiagonalStrip n, f ts
        ∂(volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) +
        ∑ r ∈ Finset.range n,
          ∫ ts in harper1144OverlapShell r, f ts
            ∂(volume.restrict harperLowerVerticalBand).prod
              (volume.restrict harperLowerVerticalBand) ≤
      C₂ * (4 : Real) ^ start * (n : Real)⁻¹ +
        4 * (Cshell * (4 : Real) ^ start) * (n : Real)⁻¹ :=
      add_le_add (by simpa only [f] using hnear') hsum
    _ = C * (4 : Real) ^ start * (n : Real)⁻¹ := by
      dsimp only [C]
      ring

end

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.exists_eventually_harperScheduledPrimeBlock_partial_correlation_le
#print axioms Erdos.Problem1144.exists_harper1144LogBallot_naturalShell_pointwise_le_envelope
#print axioms Erdos.Problem1144.exists_harper1144LogBallot_naturalShell_integral_le_envelope
#print axioms Erdos.Problem1144.exists_harper1144LogBallot_terminalShell_integral_le_envelope
#print axioms Erdos.Problem1144.exists_harper1144LogBallot_nearDiagonal_integral_le_envelope
#print axioms Erdos.Problem1144.exists_harper1144LogBallot_partitioned_integral_le_envelope
