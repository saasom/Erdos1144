import Erdos.Problem1144.HarperTerminalComplementCorrelation

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# The independent partial-block screen

For an arbitrary ambient cutoff `y`, the scheduled walk can stop partway
through its last prime block.  The resulting coordinates are independent of
the completed lower blocks.  This file shows that this one-block screen has
uniform reciprocal-prime mass and hence uniformly bounded two-height
correlation.  It is the device that removes the former exact-endpoint
restriction from the logarithmic-ballot certificate.
-/

/-- A partially exposed late scheduled block has no more reciprocal-prime
mass than the corresponding completed block. -/
theorem exists_eventually_harperScheduledPrimeBlock_partial_inv_upper :
    ∃ J : Nat, ∀ j : Nat, J ≤ j → ∀ y : Nat,
      (∑ p ∈ Problem520.harperScheduledPrimeBlock y j,
          (p.1 : Real)⁻¹) ≤ 3 / 2 := by
  obtain ⟨J, hJ⟩ :=
    Problem520.exists_eventually_harperScheduledPrimeBlock_inv_bounds
  refine ⟨J, ?_⟩
  intro j hj y
  let Y : Nat := Problem520.harperBlockEndpoint (j + 1)
  let ey : Problem520.HarperPrimeIndex y ↪ Nat :=
    Function.Embedding.subtype _
  let eY : Problem520.HarperPrimeIndex Y ↪ Nat :=
    Function.Embedding.subtype _
  have hsubset :
      (Problem520.harperScheduledPrimeBlock y j).map ey ⊆
        Problem520.freshPrimes (Problem520.harperBlockEndpoint j) Y := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
    have hqInterval :=
      (Problem520.mem_harperScheduledPrimeBlock q).mp hq
    have hqPrime := Nat.prime_of_mem_primesBelow q.property
    exact Problem520.mem_freshPrimes.mpr
      ⟨hqPrime, hqInterval.1, hqInterval.2⟩
  calc
    (∑ p ∈ Problem520.harperScheduledPrimeBlock y j,
        (p.1 : Real)⁻¹) =
        ∑ p ∈ (Problem520.harperScheduledPrimeBlock y j).map ey,
          (p : Real)⁻¹ := by
            rw [Finset.sum_map]
            rfl
    _ ≤ ∑ p ∈ Problem520.freshPrimes
          (Problem520.harperBlockEndpoint j) Y, (p : Real)⁻¹ := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
              (fun _ _ _ => by positivity)
    _ = ∑ p ∈ Problem520.harperScheduledPrimeBlock Y j,
          (p.1 : Real)⁻¹ := by
            symm
            exact Problem520.sum_harperScheduledPrimeBlock_inv_eq_freshReciprocalSum
              (y := Y) (j := j) (by simp [Y])
    _ ≤ 3 / 2 := (hJ j hj Y (by simp [Y])).2

/-- The fresh coordinates in the partially exposed last block contribute
only an absolute correlation factor.  No height separation is needed. -/
theorem exists_eventually_harperScheduledPrimeBlock_partial_correlation_le :
    ∃ D > 0, ∃ J : Nat, ∀ j : Nat, J ≤ j → ∀ y : Nat,
      ∀ t s : Real,
        harperSubsetCorrelation y
            (Problem520.harperScheduledPrimeBlock y j) t s ≤ D := by
  obtain ⟨J, hmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_partial_inv_upper
  refine ⟨Real.exp 24, Real.exp_pos 24, J, ?_⟩
  intro j hj y t s
  let S := Problem520.harperScheduledPrimeBlock y j
  have hterm : ∀ p ∈ S,
      4 * Real.cos (t * Real.log (p.1 : Real)) *
            Real.cos (s * Real.log (p.1 : Real)) * (p.1 : Real)⁻¹ +
          12 * (p.1 : Real)⁻¹ ^ (2 : Nat) ≤
        16 * (p.1 : Real)⁻¹ := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primesBelow p.property
    have hpOne : (1 : Real) ≤ p.1 := by exact_mod_cast hpPrime.one_le
    have hinv0 : (0 : Real) ≤ (p.1 : Real)⁻¹ := by positivity
    have hinv1 : (p.1 : Real)⁻¹ ≤ 1 :=
      (inv_le_one₀ (by positivity)).2 hpOne
    have hct : |Real.cos (t * Real.log (p.1 : Real))| ≤ 1 :=
      Real.abs_cos_le_one _
    have hcs : |Real.cos (s * Real.log (p.1 : Real))| ≤ 1 :=
      Real.abs_cos_le_one _
    have hprod : Real.cos (t * Real.log (p.1 : Real)) *
        Real.cos (s * Real.log (p.1 : Real)) ≤ 1 := by
      calc
        Real.cos (t * Real.log (p.1 : Real)) *
              Real.cos (s * Real.log (p.1 : Real)) ≤
            |Real.cos (t * Real.log (p.1 : Real)) *
              Real.cos (s * Real.log (p.1 : Real))| := le_abs_self _
        _ = |Real.cos (t * Real.log (p.1 : Real))| *
              |Real.cos (s * Real.log (p.1 : Real))| := abs_mul _ _
        _ ≤ 1 * 1 := mul_le_mul hct hcs (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hlinear : 4 *
          (Real.cos (t * Real.log (p.1 : Real)) *
            Real.cos (s * Real.log (p.1 : Real))) * (p.1 : Real)⁻¹ ≤
        4 * (p.1 : Real)⁻¹ := by
      calc
        (4 : Real) *
              (Real.cos (t * Real.log (p.1 : Real)) *
                Real.cos (s * Real.log (p.1 : Real))) * (p.1 : Real)⁻¹ ≤
            4 * 1 * (p.1 : Real)⁻¹ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : Real) ≤ 4))
            hinv0
        _ = 4 * (p.1 : Real)⁻¹ := by ring
    have hsquare : (p.1 : Real)⁻¹ ^ (2 : Nat) ≤ (p.1 : Real)⁻¹ := by
      simpa only [pow_two] using
        mul_le_of_le_one_right hinv0 hinv1
    nlinarith
  have hlog :
      Real.log (harperSubsetCorrelation y S t s) ≤ 24 := by
    calc
      Real.log (harperSubsetCorrelation y S t s) ≤
          ∑ p ∈ S,
            (4 * Real.cos (t * Real.log (p.1 : Real)) *
                Real.cos (s * Real.log (p.1 : Real)) * (p.1 : Real)⁻¹ +
              12 * (p.1 : Real)⁻¹ ^ (2 : Nat)) :=
        log_harperSubsetCorrelation_le y S t s
      _ ≤ ∑ p ∈ S, 16 * (p.1 : Real)⁻¹ :=
        Finset.sum_le_sum hterm
      _ = 16 * (∑ p ∈ S, (p.1 : Real)⁻¹) := by
        rw [Finset.mul_sum]
      _ ≤ 16 * (3 / 2 : Real) := by
        gcongr
        exact hmass j hj y
      _ = 24 := by norm_num
  rw [← Real.exp_log (harperSubsetCorrelation_pos y S t s)]
  exact Real.exp_le_exp.mpr hlog

/-- If `y` lies in the next scheduled block, the complement of a completed
initial range is the lower prefix, the completed later range, and exactly one
partial independent screen block. -/
theorem harperScheduledPrimeRangeFrom_compl_eq_prefix_union_tail_union_partial
    {y start r n : Nat} (hrn : r ≤ n)
    (hlower : Problem520.harperBlockEndpoint (start + n) ≤ y)
    (hupper : y < Problem520.harperBlockEndpoint (start + n + 1)) :
    (Problem520.harperScheduledPrimeRangeFrom y start r)ᶜ =
      (harperScheduledPrimePrefix y start ∪
        Problem520.harperScheduledPrimeRangeFrom y (start + r) (n - r)) ∪
          Problem520.harperScheduledPrimeBlock y (start + n) := by
  ext p
  have hpY : p.1 ≤ y := by
    have hp := Nat.mem_primesBelow.mp p.property
    omega
  simp only [Finset.mem_compl, Finset.mem_union,
    Problem520.mem_harperScheduledPrimeRangeFrom,
    mem_harperScheduledPrimePrefix,
    Problem520.mem_harperScheduledPrimeBlock]
  rw [show start + r + (n - r) = start + n by omega]
  have hendpointMono : Problem520.harperBlockEndpoint (start + r) ≤
      Problem520.harperBlockEndpoint (start + n) :=
    Problem520.monotone_harperBlockEndpoint (by omega)
  omega

/-- The lower prefix and completed tail are disjoint from the unfinished
screen block. -/
theorem disjoint_harperPrefix_union_tail_partialBlock
    (y start r n : Nat) (hrn : r ≤ n) :
    Disjoint
      (harperScheduledPrimePrefix y start ∪
        Problem520.harperScheduledPrimeRangeFrom y (start + r) (n - r))
      (Problem520.harperScheduledPrimeBlock y (start + n)) := by
  rw [Finset.disjoint_left]
  intro p hp hpartial
  rcases Finset.mem_union.mp hp with hpPrefix | hpTail
  · have hpUpper := (mem_harperScheduledPrimePrefix p).mp hpPrefix
    have hpLower :=
      (Problem520.mem_harperScheduledPrimeBlock p).mp hpartial |>.1
    have hmono : Problem520.harperBlockEndpoint start ≤
        Problem520.harperBlockEndpoint (start + n) :=
      Problem520.monotone_harperBlockEndpoint (by omega)
    omega
  · have hpUpper :=
      (Problem520.mem_harperScheduledPrimeRangeFrom p).mp hpTail |>.2
    have hpLower :=
      (Problem520.mem_harperScheduledPrimeBlock p).mp hpartial |>.1
    rw [show start + r + (n - r) = start + n by omega] at hpUpper
    omega

/-- Arbitrary-cutoff shell complement bound.  The completed tail has the
usual off-diagonal constant, and the sole unfinished block is paid for by
the independent-screen constant above. -/
theorem exists_harperScheduledPrefixComplement_shell_le_four_pow_start_envelope :
    ∃ D > 0, ∃ J : Nat,
      ∀ q start r n y : Nat, J ≤ start → r ≤ n →
        J + (q + 1) ≤ start + r →
        Problem520.harperBlockEndpoint (start + n) ≤ y →
        y < Problem520.harperBlockEndpoint (start + n + 1) →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (q + 1) < |t - s| →
                harperSubsetCorrelation y
                    (Problem520.harperScheduledPrimeRangeFrom y start r)ᶜ
                    t s ≤ D * (4 : Real) ^ start := by
  obtain ⟨D₀, hD₀, J₀, hprefix⟩ :=
    exists_harperScheduledPrimePrefix_correlation_le_four_pow
  obtain ⟨D₁, hD₁, J₁, htail⟩ :=
    exists_harperScheduledPostCommonRange_correlation_le_constant
  obtain ⟨D₂, hD₂, J₂, hpartial⟩ :=
    exists_eventually_harperScheduledPrimeBlock_partial_correlation_le
  let D : Real := D₀ * D₁ * D₂
  let J : Nat := max (max J₀ J₁) J₂
  refine ⟨D, mul_pos (mul_pos hD₀ hD₁) hD₂, J, ?_⟩
  intro q start r n y hstart hrn hcoh hlower hupper t ht s hs hsep
  have hstart₀ : J₀ ≤ start :=
    (le_max_left J₀ J₁).trans
      ((le_max_left (max J₀ J₁) J₂).trans hstart)
  have hstart₁ : J₁ + (q + 1) ≤ start + r := by
    have hJ₁ : J₁ ≤ J :=
      (le_max_right J₀ J₁).trans (le_max_left _ _)
    omega
  have hstart₂ : J₂ ≤ start + n := by
    have hJ₂ : J₂ ≤ J := le_max_right _ _
    omega
  have hstartEndpoint : Problem520.harperBlockEndpoint start ≤ y :=
    (Problem520.monotone_harperBlockEndpoint
      (show start ≤ start + n by omega)).trans hlower
  have htailEndpoint :
      Problem520.harperBlockEndpoint (start + r + (n - r)) ≤ y := by
    simpa only [show start + r + (n - r) = start + n by omega] using hlower
  have hpref := hprefix start y hstart₀ hstartEndpoint t ht s hs
  have hlate := htail q (start + r) (n - r) y hstart₁
    htailEndpoint t ht s hs hsep
  have hpart := hpartial (start + n) hstart₂ y t s
  have hdisPrefixTail : Disjoint (harperScheduledPrimePrefix y start)
      (Problem520.harperScheduledPrimeRangeFrom y (start + r) (n - r)) := by
    rw [Finset.disjoint_left]
    intro p hpPrefix hpTail
    have hpUpper := (mem_harperScheduledPrimePrefix p).mp hpPrefix
    have hpLower :=
      (Problem520.mem_harperScheduledPrimeRangeFrom p).mp hpTail |>.1
    have hmono : Problem520.harperBlockEndpoint start ≤
        Problem520.harperBlockEndpoint (start + r) :=
      Problem520.monotone_harperBlockEndpoint (by omega)
    omega
  have hdisPartial :=
    disjoint_harperPrefix_union_tail_partialBlock y start r n hrn
  rw [harperScheduledPrimeRangeFrom_compl_eq_prefix_union_tail_union_partial
        hrn hlower hupper,
    harperSubsetCorrelation_union y hdisPartial,
    harperSubsetCorrelation_union y hdisPrefixTail]
  calc
    (harperSubsetCorrelation y (harperScheduledPrimePrefix y start) t s *
          harperSubsetCorrelation y
            (Problem520.harperScheduledPrimeRangeFrom y (start + r) (n - r))
            t s) *
        harperSubsetCorrelation y
          (Problem520.harperScheduledPrimeBlock y (start + n)) t s ≤
      ((D₀ * (4 : Real) ^ start) * D₁) * D₂ := by
        exact mul_le_mul (mul_le_mul hpref hlate
            (harperSubsetCorrelation_pos y _ t s).le (by positivity))
          hpart (harperSubsetCorrelation_pos y _ t s).le (by positivity)
    _ = D * (4 : Real) ^ start := by
      dsimp only [D]
      ring

/-- At an arbitrary cutoff in the next scheduled block, the terminal range
has only the lower prefix and the one unfinished screen block outside it. -/
theorem harperScheduledPrimeRangeFrom_compl_eq_prefix_union_partial
    {y start n : Nat}
    (hlower : Problem520.harperBlockEndpoint (start + n) ≤ y)
    (hupper : y < Problem520.harperBlockEndpoint (start + n + 1)) :
    (Problem520.harperScheduledPrimeRangeFrom y start n)ᶜ =
      harperScheduledPrimePrefix y start ∪
        Problem520.harperScheduledPrimeBlock y (start + n) := by
  simpa using
    harperScheduledPrimeRangeFrom_compl_eq_prefix_union_tail_union_partial
      (y := y) (start := start) (r := n) (n := n) (le_rfl)
        hlower hupper

/-- Arbitrary-cutoff terminal complement correlation bound. -/
theorem exists_harperTerminal_complementCorrelation_le_four_pow_envelope :
    ∃ D > 0, ∃ J : Nat, ∀ start n y : Nat, J ≤ start →
      Problem520.harperBlockEndpoint (start + n) ≤ y →
      y < Problem520.harperBlockEndpoint (start + n + 1) →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            harperSubsetCorrelation y
                (Problem520.harperScheduledPrimeRangeFrom y start n)ᶜ t s ≤
              D * (4 : Real) ^ start := by
  obtain ⟨D₀, hD₀, J₀, hprefix⟩ :=
    exists_harperScheduledPrimePrefix_correlation_le_four_pow
  obtain ⟨D₁, hD₁, J₁, hpartial⟩ :=
    exists_eventually_harperScheduledPrimeBlock_partial_correlation_le
  let D : Real := D₀ * D₁
  let J : Nat := max J₀ J₁
  refine ⟨D, mul_pos hD₀ hD₁, J, ?_⟩
  intro start n y hstart hlower hupper t ht s hs
  have hstart₀ : J₀ ≤ start := (le_max_left _ _).trans hstart
  have hstart₁ : J₁ ≤ start + n := by
    have : J₁ ≤ start := (le_max_right _ _).trans hstart
    omega
  have hendpoint : Problem520.harperBlockEndpoint start ≤ y :=
    (Problem520.monotone_harperBlockEndpoint (by omega)).trans hlower
  have hpref := hprefix start y hstart₀ hendpoint t ht s hs
  have hpart := hpartial (start + n) hstart₁ y t s
  have hdis : Disjoint (harperScheduledPrimePrefix y start)
      (Problem520.harperScheduledPrimeBlock y (start + n)) := by
    have h :=
      disjoint_harperPrefix_union_tail_partialBlock y start n n le_rfl
    rw [Finset.disjoint_left] at ⊢
    intro p hpPrefix hpPartial
    exact (Finset.disjoint_left.mp h)
      (Finset.mem_union_left _ hpPrefix) hpPartial
  rw [harperScheduledPrimeRangeFrom_compl_eq_prefix_union_partial hlower hupper,
    harperSubsetCorrelation_union y hdis]
  calc
    harperSubsetCorrelation y (harperScheduledPrimePrefix y start) t s *
        harperSubsetCorrelation y
          (Problem520.harperScheduledPrimeBlock y (start + n)) t s ≤
      (D₀ * (4 : Real) ^ start) * D₁ :=
        mul_le_mul hpref hpart
          (harperSubsetCorrelation_pos y _ t s).le (by positivity)
    _ = D * (4 : Real) ^ start := by
      dsimp only [D]
      ring

/-- Terminal likelihood localization remains valid at every cutoff between
two scheduled endpoints: the completed path pays the usual fourth-power
pinch and the unfinished upper-prime screen costs only the constant above. -/
theorem
    exists_harperTerminalCapped_correlation_probability_le_powTwo_mul_four_pow_div_sq_envelope :
    ∃ C > 0, ∃ J : Nat, ∀ start n y : Nat, J ≤ start →
      0 < n →
      Problem520.harperBlockEndpoint (start + n) ≤ y →
      y < Problem520.harperBlockEndpoint (start + n + 1) →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            harperTwoHeightCorrelation y t s *
                (harperTwoHeightCubeLaw y t s).real
                  (harperTerminalCappedCentralLowerBallotCubeEvent
                      y start n t ∩
                    harperTerminalCappedCentralLowerBallotCubeEvent
                      y start n s) ≤
              C * (2 : Real) ^ n * (n : Real)⁻¹ *
                (n : Real)⁻¹ * (n : Real)⁻¹ *
                (n : Real)⁻¹ * (4 : Real) ^ start := by
  obtain ⟨B, hB, Jballot, hballot⟩ :=
    exists_harperTerminalCapped_correlation_probability_le_powTwo_div_compl
  obtain ⟨D, hD, Jcorr, hcorr⟩ :=
    exists_harperTerminal_complementCorrelation_le_four_pow_envelope
  let C : Real := B * D
  let J : Nat := max (Jballot + 1) Jcorr
  refine ⟨C, mul_pos hB hD, J, ?_⟩
  intro start n y hstart hn hlower hupper t ht s hs
  have hstartBallot : Jballot + 1 ≤ start :=
    (le_max_left _ _).trans hstart
  have hstartCorr : Jcorr ≤ start :=
    (le_max_right _ _).trans hstart
  have hloc := hballot start n y hstartBallot hn hlower t ht s hs
  have hcomp := hcorr start n y hstartCorr hlower hupper t ht s hs
  calc
    harperTwoHeightCorrelation y t s *
          (harperTwoHeightCubeLaw y t s).real
            (harperTerminalCappedCentralLowerBallotCubeEvent y start n t ∩
              harperTerminalCappedCentralLowerBallotCubeEvent y start n s) ≤
        B * (2 : Real) ^ n * (n : Real)⁻¹ * (n : Real)⁻¹ *
          (n : Real)⁻¹ * (n : Real)⁻¹ *
          harperSubsetCorrelation y
            (Problem520.harperScheduledPrimeRangeFrom y start n)ᶜ t s := hloc
    _ ≤ B * (2 : Real) ^ n * (n : Real)⁻¹ * (n : Real)⁻¹ *
          (n : Real)⁻¹ * (n : Real)⁻¹ *
          (D * (4 : Real) ^ start) := by
      exact mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = C * (2 : Real) ^ n * (n : Real)⁻¹ *
          (n : Real)⁻¹ * (n : Real)⁻¹ *
          (n : Real)⁻¹ * (4 : Real) ^ start := by
      dsimp only [C]
      ring

end

end Problem1144
end Erdos
