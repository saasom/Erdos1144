import Erdos.Problem1144.HarperTwoHeightCharacteristic
import Erdos.Problem520.HarperMovingHeightVerticalCumulative

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Dyadic overlap shells for the two-height ballot

This file fixes the geometric decomposition used by the remaining
two-dimensional comparison.  Shell `r` consists of pairs whose height gap is
between `2^(-(r+1))` and `2^(-r)`.  Together with the terminal strip of radius
`2^(-n)`, the first `n` shells cover the whole lower vertical band.

The analytic shell estimate is designed to have weight

`1 / ((r+1)^2 * (n-r+1))`.

The last theorem below proves once and for all that these weights sum to
`O(1/n)`.  Thus the genuinely missing input is local: prove the advertised
bound on one shell.  No further summability issue remains after that.
-/

/-- The `r`th dyadic height-gap shell. -/
def harper1144OverlapShell (r : Nat) : Set (Real × Real) :=
  harperNearDiagonalStrip (((2 : Real) ^ r)⁻¹) \
    harperNearDiagonalStrip (((2 : Real) ^ (r + 1))⁻¹)

theorem measurableSet_harper1144OverlapShell (r : Nat) :
    MeasurableSet (harper1144OverlapShell r) := by
  exact (measurableSet_harperNearDiagonalStrip _).diff
    (measurableSet_harperNearDiagonalStrip _)

theorem mem_harper1144OverlapShell_iff
    {r : Nat} {ts : Real × Real} :
    ts ∈ harper1144OverlapShell r ↔
      (((2 : Real) ^ (r + 1))⁻¹ < |ts.1 - ts.2| ∧
        |ts.1 - ts.2| ≤ ((2 : Real) ^ r)⁻¹) := by
  simp only [harper1144OverlapShell, harperNearDiagonalStrip,
    Set.mem_diff, Set.mem_setOf_eq, not_le]
  tauto

theorem harper1144OverlapShell_subset_nearDiagonal (r : Nat) :
    harper1144OverlapShell r ⊆
      harperNearDiagonalStrip (((2 : Real) ^ r)⁻¹) :=
  diff_subset

/-- Outside the terminal strip, the first `n` shells exhaust the unit
diagonal strip.  This is the finite dyadic partition used below. -/
theorem exists_mem_harper1144OverlapShell_of_mem_terminalZero_diff_terminal
    {n : Nat} {ts : Real × Real}
    (hts : ts ∈ harperTerminalNearDiagonalStrip 0 \
      harperTerminalNearDiagonalStrip n) :
    ∃ r < n, ts ∈ harper1144OverlapShell r := by
  induction n with
  | zero =>
      exact False.elim (hts.2 hts.1)
  | succ n ih =>
      by_cases hn : ts ∈ harperTerminalNearDiagonalStrip n
      · refine ⟨n, Nat.lt_succ_self n, ?_⟩
        exact ⟨hn, hts.2⟩
      · obtain ⟨r, hr, hrs⟩ := ih ⟨hts.1, hn⟩
        exact ⟨r, hr.trans (Nat.lt_succ_self n), hrs⟩

/-- Every pair in the lower vertical band is either in the terminal strip or
in one of the first `n` overlap shells. -/
theorem harperLowerVerticalBand_pair_terminal_or_overlapShell
    (n : Nat) {ts : Real × Real}
    (hts : ts ∈ harperLowerVerticalBand ×ˢ harperLowerVerticalBand) :
    ts ∈ harperTerminalNearDiagonalStrip n ∨
      ∃ r < n, ts ∈ harper1144OverlapShell r := by
  by_cases hterminal : ts ∈ harperTerminalNearDiagonalStrip n
  · exact Or.inl hterminal
  · right
    apply exists_mem_harper1144OverlapShell_of_mem_terminalZero_diff_terminal
    refine ⟨?_, hterminal⟩
    unfold harperTerminalNearDiagonalStrip harperNearDiagonalStrip
    simp only [Set.mem_setOf_eq, Nat.cast_ofNat, pow_zero, inv_one]
    rw [abs_le]
    rcases hts with ⟨⟨htLower, htUpper⟩, hsLower, hsUpper⟩
    constructor <;> linarith

/-- The shell measure has the expected dyadic upper bound. -/
theorem measureReal_harper1144OverlapShell_le (r : Nat) :
    ((volume.restrict harperLowerVerticalBand).prod
        (volume.restrict harperLowerVerticalBand)).real
          (harper1144OverlapShell r) ≤
      (1 / 3 : Real) * (((2 : Real) ^ r)⁻¹) := by
  have hbandFinite : volume harperLowerVerticalBand ≠ ∞ := by
    simp [harperLowerVerticalBand, Real.volume_Icc]
  let nu : Measure Real := volume.restrict harperLowerVerticalBand
  letI : IsFiniteMeasure nu := isFiniteMeasure_restrict.2 hbandFinite
  have hnearFinite :
      (nu.prod nu) (harperNearDiagonalStrip (((2 : Real) ^ r)⁻¹)) ≠ ∞ :=
    measure_ne_top _ _
  have hmono := measureReal_mono
    (μ := nu.prod nu)
    (harper1144OverlapShell_subset_nearDiagonal r) hnearFinite
  exact hmono.trans
    (by
      simpa only [nu, harperTerminalNearDiagonalStrip] using
        measureReal_harperTerminalNearDiagonalStrip_le r)

/-- The numerical weight predicted by the pinched two-height estimate. -/
noncomputable def harper1144OverlapShellWeight (n r : Nat) : Real :=
  ((((r + 1 : Nat) : Real) ^ (2 : Nat)) *
    ((n - r + 1 : Nat) : Real))⁻¹

theorem harper1144OverlapShellWeight_nonneg (n r : Nat) :
    0 ≤ harper1144OverlapShellWeight n r := by
  unfold harper1144OverlapShellWeight
  positivity

/-- Partial fractions for a single overlap-shell weight. -/
theorem harper1144OverlapShellWeight_eq
    {n r : Nat} (hr : r < n) :
    harper1144OverlapShellWeight n r =
      (((n + 2 : Nat) : Real))⁻¹ *
          ((((r + 1 : Nat) : Real) ^ (2 : Nat))⁻¹) +
        (((n + 2 : Nat) : Real) ^ (2 : Nat))⁻¹ *
          ((((r + 1 : Nat) : Real))⁻¹ +
            (((n - r + 1 : Nat) : Real))⁻¹) := by
  have ha : (0 : Real) < ((r + 1 : Nat) : Real) := by positivity
  have hb : (0 : Real) < ((n - r + 1 : Nat) : Real) := by positivity
  have hN : (0 : Real) < ((n + 2 : Nat) : Real) := by positivity
  have hadd : ((r + 1 : Nat) : Real) + ((n - r + 1 : Nat) : Real) =
      ((n + 2 : Nat) : Real) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    rw [Nat.cast_sub (Nat.le_of_lt hr)]
    ring
  unfold harper1144OverlapShellWeight
  field_simp
  nlinarith

/-- Each reciprocal appearing in the harmless harmonic part is at most one. -/
private theorem overlapShell_harmonic_term_le_two
    {n r : Nat} (hr : r < n) :
    (((r + 1 : Nat) : Real))⁻¹ +
        (((n - r + 1 : Nat) : Real))⁻¹ ≤ 2 := by
  have ha : (1 : Real) ≤ ((r + 1 : Nat) : Real) := by
    exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hb : (1 : Real) ≤ ((n - r + 1 : Nat) : Real) := by
    exact_mod_cast (show 1 ≤ n - r + 1 by omega)
  have haInv : (((r + 1 : Nat) : Real))⁻¹ ≤ 1 := by
    simpa using (inv_le_one₀ (by positivity) |>.2 ha)
  have hbInv : (((n - r + 1 : Nat) : Real))⁻¹ ≤ 1 := by
    simpa using (inv_le_one₀ (by positivity) |>.2 hb)
  linarith

/-- The overlap-shell weights are summable at the exact scale required by
the restricted second moment. -/
theorem sum_harper1144OverlapShellWeight_le
    (n : Nat) (hn : 0 < n) :
    (∑ r ∈ Finset.range n, harper1144OverlapShellWeight n r) ≤
      4 * (n : Real)⁻¹ := by
  have hdecomp :
      (∑ r ∈ Finset.range n, harper1144OverlapShellWeight n r) =
        (((n + 2 : Nat) : Real))⁻¹ *
            (∑ r ∈ Finset.range n,
              ((((r + 1 : Nat) : Real) ^ (2 : Nat))⁻¹)) +
          (((n + 2 : Nat) : Real) ^ (2 : Nat))⁻¹ *
            (∑ r ∈ Finset.range n,
              ((((r + 1 : Nat) : Real))⁻¹ +
                (((n - r + 1 : Nat) : Real))⁻¹)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    exact harper1144OverlapShellWeight_eq (Finset.mem_range.mp hr)
  have hsquare :
      (∑ r ∈ Finset.range n,
        ((((r + 1 : Nat) : Real) ^ (2 : Nat))⁻¹)) ≤ 2 :=
    Problem520.sum_range_inv_nat_succ_sq_le_two n
  have hharmonic :
      (∑ r ∈ Finset.range n,
        ((((r + 1 : Nat) : Real))⁻¹ +
          (((n - r + 1 : Nat) : Real))⁻¹)) ≤ 2 * n := by
    calc
      _ ≤ ∑ _r ∈ Finset.range n, (2 : Real) := by
        apply Finset.sum_le_sum
        intro r hr
        exact overlapShell_harmonic_term_le_two (Finset.mem_range.mp hr)
      _ = 2 * n := by simp [mul_comm]
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hN : (n : Real) ≤ ((n + 2 : Nat) : Real) := by norm_num
  have hNpos : (0 : Real) < ((n + 2 : Nat) : Real) := by positivity
  have hinvN : (((n + 2 : Nat) : Real))⁻¹ ≤ (n : Real)⁻¹ :=
    (inv_le_inv₀ hNpos hnR).2 hN
  have hinvNSq : (((n + 2 : Nat) : Real) ^ (2 : Nat))⁻¹ ≤
      ((n : Real) ^ (2 : Nat))⁻¹ := by
    exact (inv_le_inv₀ (sq_pos_of_pos hNpos) (sq_pos_of_pos hnR)).2
      (pow_le_pow_left₀ hnR.le hN 2)
  rw [hdecomp]
  calc
    _ ≤ (((n + 2 : Nat) : Real))⁻¹ * 2 +
        (((n + 2 : Nat) : Real) ^ (2 : Nat))⁻¹ * (2 * n) := by
      gcongr
    _ ≤ (n : Real)⁻¹ * 2 +
        ((n : Real) ^ (2 : Nat))⁻¹ * (2 * n) := by
      gcongr
    _ = 4 * (n : Real)⁻¹ := by
      field_simp
      ring

/-! ## Exact statement and deterministic summation handoff -/

/-- The remaining overlap-shell theorem, stated directly for the final
pinched event and the actual tilted Rademacher law.  This is the grouped-block
Rademacher version of Harper's two-height local-limit/ballot estimate. -/
def Harper1144TwoHeightOverlapShellStatement : Prop :=
  ∃ C > 0, ∃ J : Nat, ∀ n : Nat, 0 < n →
    let start := harperTerminalGuardStart J n
    let y := Problem520.harperBlockEndpoint (start + n)
    ∀ r < n,
      (∫ ts in harper1144OverlapShell r,
          harperTwoHeightCorrelation y ts.1 ts.2 *
            (harperTwoHeightCubeLaw y ts.1 ts.2).real
              (harper1144LogBallotCubeEvent y start n ts.1 ∩
                harper1144LogBallotCubeEvent y start n ts.2)
        ∂(volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) ≤
        C * harper1144OverlapShellWeight n r

/-- Once the local shell estimate is known, its entire separated-height sum
is at most `4C/n`.  This is the deterministic last line of the overlap-shell
argument. -/
theorem sum_harper1144OverlapShell_integrals_le_of_bound
    (n : Nat) (hn : 0 < n) (C : Real) (hC : 0 ≤ C)
    (f : Real × Real → Real)
    (hlocal : ∀ r < n,
      (∫ ts in harper1144OverlapShell r, f ts
        ∂(volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) ≤
        C * harper1144OverlapShellWeight n r) :
    (∑ r ∈ Finset.range n,
      ∫ ts in harper1144OverlapShell r, f ts
        ∂(volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) ≤
      4 * C * (n : Real)⁻¹ := by
  calc
    _ ≤ ∑ r ∈ Finset.range n,
        C * harper1144OverlapShellWeight n r := by
      apply Finset.sum_le_sum
      intro r hr
      exact hlocal r (Finset.mem_range.mp hr)
    _ = C * (∑ r ∈ Finset.range n,
        harper1144OverlapShellWeight n r) := by
      rw [Finset.mul_sum]
    _ ≤ C * (4 * (n : Real)⁻¹) :=
      mul_le_mul_of_nonneg_left
        (sum_harper1144OverlapShellWeight_le n hn) hC
    _ = 4 * C * (n : Real)⁻¹ := by ring

end
end Problem1144
end Erdos

#print axioms Erdos.Problem1144.measureReal_harper1144OverlapShell_le
#print axioms Erdos.Problem1144.sum_harper1144OverlapShellWeight_le
#print axioms Erdos.Problem1144.harperLowerVerticalBand_pair_terminal_or_overlapShell
#print axioms Erdos.Problem1144.sum_harper1144OverlapShell_integrals_le_of_bound
