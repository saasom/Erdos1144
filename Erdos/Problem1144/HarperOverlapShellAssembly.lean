import Erdos.Problem1144.HarperGaussianSuffixBallot

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Rooted overlap-shell assembly

This module combines the two genuinely different prefix scales in Harper's
separated-height argument.  On shell `q`, the rooted-density pinch is taken
after `q+1` common-history blocks.  The two-walk suffix may begin later, after
`d` blocks, leaving an unrestricted oscillatory buffer between the two.
-/

/-- Pointwise shell estimate before choosing the Gaussian decorrelation
cutoff `d`.  The shell-dependent Euler correlation above the common-history
cutoff is already absorbed; the lower omitted prefix remains explicitly as
`4^start`. -/
theorem exists_harper1144LogBallot_shell_pointwise_le :
    ∃ C > 0, ∃ J : Nat,
      ∀ start q d m y : Nat, J ≤ start → q + 1 ≤ d → 4 ≤ m →
        Problem520.harperBlockEndpoint (start + (d + m)) = y →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (q + 1) < |t - s| →
              (∀ i : Fin m,
                4 * ((2 * (d + m) : Nat) : Real) ^ (6 : Nat) ≤
                  Real.sqrt
                    (Problem520.harperBlockEndpoint
                      (start + d + i.val) : Real)) →
              (∀ i : Fin m,
                1048576 * ((2 * (d + m) : Nat) : Real) ^ (48 : Nat) ≤
                  Real.sqrt
                    (Problem520.harperBlockEndpoint
                      (start + d + i.val) : Real)) →
              (∀ i : Fin m,
                |harperTwoHeightBlockCoordinateCovariance y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + d + i.val)) t s t s| ≤
                  1 / ((2 * (d + m) : Nat) : Real) ^ (40 : Nat)) →
              (∀ i : Fin m,
                |harperTwoHeightRelativeBlockDrift y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + d + i.val)) t s t t| ≤
                  1 / ((2 * (d + m) : Nat) : Real) ^ (2 : Nat)) →
              (∀ i : Fin m,
                |harperTwoHeightRelativeBlockDrift y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + d + i.val)) t s s s| ≤
                  1 / ((2 * (d + m) : Nat) : Real) ^ (2 : Nat)) →
              (∀ i : Fin m,
                (1 / 3 : Real) <
                    harperTwoHeightBlockCoordinateCovariance y
                      (Problem520.harperScheduledPrimeBlock y
                        (start + d + i.val)) t s t t ∧
                  harperTwoHeightBlockCoordinateCovariance y
                      (Problem520.harperScheduledPrimeBlock y
                        (start + d + i.val)) t s t t < (3 / 8 : Real)) →
              (∀ i : Fin m,
                (1 / 3 : Real) <
                    harperTwoHeightBlockCoordinateCovariance y
                      (Problem520.harperScheduledPrimeBlock y
                        (start + d + i.val)) t s s s ∧
                  harperTwoHeightBlockCoordinateCovariance y
                      (Problem520.harperScheduledPrimeBlock y
                        (start + d + i.val)) t s s s < (3 / 8 : Real)) →
                harperTwoHeightCorrelation y t s *
                    (harperTwoHeightCubeLaw y t s).real
                      (harper1144LogBallotCubeEvent y start (d + m) t ∩
                        harper1144LogBallotCubeEvent y start (d + m) s) ≤
                  C * (4 : Real) ^ start *
                    (2 : Real) ^ (q + 1) /
                    (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
                    (5000 * (64 * (d : Real) + 4) ^ (2 : Nat) *
                      (m : Real)⁻¹) := by
  obtain ⟨B, hB, Jroot, hroot⟩ :=
    exists_harper1144LogBallot_rooted_commonPrefix_suffix_le
  obtain ⟨D, hD, Jcorr, hcorr⟩ :=
    exists_harperScheduledPrefixComplement_shell_le_four_pow_start
  let C : Real := B * D
  let J : Nat := max (Jroot + 1) Jcorr
  refine ⟨C, mul_pos hB hD, J, ?_⟩
  intro start q d m y hstart hqd hm hy t ht s hs hsep
    hfrequency hendpoint hcovariance hdriftFirst hdriftSecond
    hvarianceFirst hvarianceSecond
  have hstartRoot : Jroot + 1 ≤ start :=
    (le_max_left (Jroot + 1) Jcorr).trans hstart
  have hstartCorr : Jcorr ≤ start :=
    (le_max_right (Jroot + 1) Jcorr).trans hstart
  have hrooted := hroot start (q + 1) d m y hstartRoot
    (by omega) hqd hm hy.le t ht s hs hfrequency hendpoint hcovariance
      hdriftFirst hdriftSecond hvarianceFirst hvarianceSecond
  dsimp only at hrooted
  have hcomp := hcorr q start (q + 1) (d + m) y hstartCorr
    (by omega) (by omega) hy t ht s hs hsep
  have hleftNonneg :
      0 ≤ B * (2 : Real) ^ (q + 1) /
        (((q + 1 : Nat) : Real) ^ (4 : Nat)) := by positivity
  have hsuffixNonneg :
      0 ≤ 5000 * (64 * (d : Real) + 4) ^ (2 : Nat) *
        (m : Real)⁻¹ := by positivity
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
          (5000 * (64 * (d : Real) + 4) ^ (2 : Nat) *
            (m : Real)⁻¹) := hrooted
    _ ≤ ((B * (2 : Real) ^ (q + 1) /
              (((q + 1 : Nat) : Real) ^ (4 : Nat))) *
            (D * (4 : Real) ^ start)) *
          (5000 * (64 * (d : Real) + 4) ^ (2 : Nat) *
            (m : Real)⁻¹) := by
      gcongr
    _ = C * (4 : Real) ^ start * (2 : Real) ^ (q + 1) /
          (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
          (5000 * (64 * (d : Real) + 4) ^ (2 : Nat) *
            (m : Real)⁻¹) := by
      dsimp only [C]
      ring

/-! ## Natural-coherence shell bound -/

/-- The natural-coherence suffix comparison removes all auxiliary
covariance, drift, frequency, and minimum-suffix-length hypotheses from the
pointwise shell estimate.  The only omitted correlation is the fixed lower
prime prefix. -/
theorem exists_harper1144LogBallot_naturalShell_pointwise_le :
    ∃ C > 0, ∃ J : Nat,
      ∀ start q d m y : Nat, J <= start -> q + 1 <= d -> 0 < m ->
        Problem520.harperBlockEndpoint (start + (d + m)) = y ->
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (q + 1) < |t - s| ->
                harperTwoHeightCorrelation y t s *
                    (harperTwoHeightCubeLaw y t s).real
                      (harper1144LogBallotCubeEvent y start (d + m) t ∩
                        harper1144LogBallotCubeEvent y start (d + m) s) <=
                  C * (4 : Real) ^ start *
                    (2 : Real) ^ (q + 1) /
                    (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
                    ((((d + 1 : Nat) : Real) ^ (2 : Nat)) *
                      (m : Real)⁻¹) := by
  obtain ⟨B, hB, L, hL, Jroot, hroot⟩ :=
    exists_harper1144LogBallot_rooted_naturalSuffix_le
  obtain ⟨D, hD, Jcorr, hcorr⟩ :=
    exists_harperScheduledPrefixComplement_shell_le_four_pow_start
  let K : Real :=
    4 * Real.exp 4 * (4096 * 68 * (536 * L + 68))
  let C : Real := B * D * K
  let J : Nat := max Jroot Jcorr
  refine ⟨C, by dsimp only [C, K]; positivity, J, ?_⟩
  intro start q d m y hstart hqd hm hy t ht s hs hsep
  have hstartRoot : Jroot <= start :=
    (le_max_left Jroot Jcorr).trans hstart
  have hstartCorr : Jcorr <= start :=
    (le_max_right Jroot Jcorr).trans hstart
  have hyRoot : Problem520.harperBlockEndpoint (start + d + m) <= y := by
    simpa only [add_assoc] using hy.le
  have hrooted := hroot start q d m y hstartRoot hqd hm hyRoot
    t ht s hs hsep
  dsimp only at hrooted
  have hcomp := hcorr q start (q + 1) (d + m) y hstartCorr
    (by omega) (by omega) hy t ht s hs hsep
  have hleftNonneg :
      0 <= B * (2 : Real) ^ (q + 1) /
        (((q + 1 : Nat) : Real) ^ (4 : Nat)) := by positivity
  have hsuffixNonneg :
      0 <= 4 * Real.exp 4 *
        ((4096 * 68 * (536 * L + 68)) *
          (((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹) := by
    positivity
  calc
    harperTwoHeightCorrelation y t s *
          (harperTwoHeightCubeLaw y t s).real
            (harper1144LogBallotCubeEvent y start (d + m) t ∩
              harper1144LogBallotCubeEvent y start (d + m) s) <=
        ((B * (2 : Real) ^ (q + 1) /
              (((q + 1 : Nat) : Real) ^ (4 : Nat))) *
            harperSubsetCorrelation y
              (Problem520.harperScheduledPrimeRangeFrom
                y start (q + 1))ᶜ t s) *
          (4 * Real.exp 4 *
            ((4096 * 68 * (536 * L + 68)) *
              (((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹)) :=
        hrooted
    _ <= ((B * (2 : Real) ^ (q + 1) /
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

/-- Shell integration cancels the natural rooted factor `2^(q+1)` against
the dyadic shell width, without changing the suffix factor. -/
theorem integral_harper1144OverlapShell_le_of_naturalRooted_bound
    (q start d m : Nat) (C : Real) (hC : 0 <= C)
    (f : Real × Real -> Real) (hfNonneg : ∀ ts, 0 <= f ts)
    (hpoint : ∀ ts ∈ harperLowerVerticalBand ×ˢ harperLowerVerticalBand,
      ts ∈ harper1144OverlapShell q ->
        f ts <= C * (4 : Real) ^ start * (2 : Real) ^ (q + 1) /
          (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
          ((((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹)) :
    (∫ ts in harper1144OverlapShell q, f ts
        ∂(volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) <=
      (2 * C / 3) * (4 : Real) ^ start /
        (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
        ((((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹) := by
  let nu : Measure Real := volume.restrict harperLowerVerticalBand
  let mu : Measure (Real × Real) := nu.prod nu
  let M : Real := C * (4 : Real) ^ start * (2 : Real) ^ (q + 1) /
    (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
    ((((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹)
  have hbandFinite : volume harperLowerVerticalBand ≠ ∞ := by
    simp [harperLowerVerticalBand, Real.volume_Icc]
  letI : IsFiniteMeasure nu := isFiniteMeasure_restrict.2 hbandFinite
  have hband : ∀ᵐ ts ∂mu,
      ts ∈ harperLowerVerticalBand ×ˢ harperLowerVerticalBand := by
    rw [Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_harperLowerVerticalBand.prod
        measurableSet_harperLowerVerticalBand)]
    filter_upwards [ae_restrict_mem measurableSet_harperLowerVerticalBand]
      with t ht
    filter_upwards [ae_restrict_mem measurableSet_harperLowerVerticalBand]
      with s hs
    exact ⟨ht, hs⟩
  have hstripFinite : mu (harper1144OverlapShell q) < ∞ :=
    measure_lt_top _ _
  have hnorm :
      ‖∫ ts in harper1144OverlapShell q, f ts ∂mu‖ <=
        M * mu.real (harper1144OverlapShell q) := by
    apply norm_setIntegral_le_of_norm_le_const_ae' hstripFinite
    filter_upwards [hband] with ts hts
    rw [Real.norm_eq_abs, abs_of_nonneg (hfNonneg ts)]
    exact hpoint ts hts
  have hintegralNonneg :
      0 <= ∫ ts in harper1144OverlapShell q, f ts ∂mu :=
    integral_nonneg_of_ae (ae_of_all _ fun ts => hfNonneg ts)
  have hmeasure := measureReal_harper1144OverlapShell_le q
  have hMnonneg : 0 <= M := by
    dsimp only [M]
    positivity
  calc
    (∫ ts in harper1144OverlapShell q, f ts ∂
        (volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) =
        ∫ ts in harper1144OverlapShell q, f ts ∂mu := by rfl
    _ <= ‖∫ ts in harper1144OverlapShell q, f ts ∂mu‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hintegralNonneg]
    _ <= M * mu.real (harper1144OverlapShell q) := hnorm
    _ <= M * ((1 / 3 : Real) * ((2 : Real) ^ q)⁻¹) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [mu, nu] using hmeasure)
        hMnonneg
    _ = (2 * C / 3) * (4 : Real) ^ start /
          (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
          ((((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹) := by
      dsimp only [M]
      have hpow : (2 : Real) ^ q ≠ 0 := by positivity
      rw [pow_succ]
      field_simp

/-- The elementary choice `d=q+1`, `m=n-(q+1)` converts the natural suffix
factor into the summable overlap-shell weight, away from the final shell. -/
theorem harper1144_naturalShell_numeric_le_weight
    {n q : Nat} (hq : q + 2 <= n) :
    (2 / 3 : Real) /
          (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
        ((((q + 2 : Nat) : Real) ^ (2 : Nat)) *
          ((n - (q + 1) : Nat) : Real)⁻¹) <=
      8 * harper1144OverlapShellWeight n q := by
  let a : Real := ((q + 1 : Nat) : Real)
  let m : Real := ((n - (q + 1) : Nat) : Real)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hmNat : 0 < n - (q + 1) := by omega
  have hm : 0 < m := by
    change (0 : Real) < ((n - (q + 1) : Nat) : Real)
    exact_mod_cast hmNat
  have hmOne : 1 <= m := by
    change (1 : Real) <= ((n - (q + 1) : Nat) : Real)
    exact_mod_cast hmNat
  have hqLinear : ((q + 2 : Nat) : Real) <= 2 * a := by
    dsimp only [a]
    exact_mod_cast (show q + 2 <= 2 * (q + 1) by omega)
  have hqSquare :
      (((q + 2 : Nat) : Real) ^ (2 : Nat)) <= 4 * a ^ (2 : Nat) := by
    nlinarith [sq_nonneg (((q + 2 : Nat) : Real)), sq_nonneg a]
  have htailNat : n - q + 1 = (n - (q + 1)) + 2 := by omega
  have htail : ((n - q + 1 : Nat) : Real) = m + 2 := by
    dsimp only [m]
    exact_mod_cast htailNat
  have hmInvLe : m⁻¹ <= 1 := (inv_le_one₀ hm).2 hmOne
  have hinvTail : m⁻¹ <= 3 * (m + 2)⁻¹ := by
    rw [show 3 * (m + 2)⁻¹ = 3 / (m + 2) by
      rw [div_eq_mul_inv]]
    apply (le_div_iff₀ (by linarith : 0 < m + 2)).2
    have hmne : m ≠ 0 := ne_of_gt hm
    have hid : m⁻¹ * (m + 2) = 1 + 2 * m⁻¹ := by
      field_simp
    rw [hid]
    linarith
  unfold harper1144OverlapShellWeight
  calc
    (2 / 3 : Real) /
          (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
        ((((q + 2 : Nat) : Real) ^ (2 : Nat)) *
          ((n - (q + 1) : Nat) : Real)⁻¹) <=
        (2 / 3 : Real) /
          (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
        ((4 * (((q + 1 : Nat) : Real) ^ (2 : Nat))) *
          (3 * ((((n - q + 1 : Nat) : Real)))⁻¹)) := by
      have hleft : 0 <= (2 / 3 : Real) /
          (((q + 1 : Nat) : Real) ^ (4 : Nat)) := by positivity
      apply mul_le_mul_of_nonneg_left _ hleft
      apply mul_le_mul hqSquare (by simpa only [htail] using hinvTail)
        (by positivity) (by positivity)
    _ = 8 *
        ((((q + 1 : Nat) : Real) ^ (2 : Nat)) *
          (((n - (q + 1) : Nat) : Real) + 2))⁻¹ := by
      rw [htail]
      field_simp
      ring
    _ = 8 *
        ((((q + 1 : Nat) : Real) ^ (2 : Nat)) *
          ((n - q + 1 : Nat) : Real))⁻¹ := by rw [htail]

/-- All nonterminal shells satisfy the advertised summable bound at one
fixed scheduled start. -/
theorem exists_harper1144LogBallot_fixedStart_naturalShell_integral_le :
    ∃ C > 0, ∃ J : Nat, ∀ start : Nat, J <= start ->
      ∀ n q : Nat, q + 2 <= n ->
        let y := Problem520.harperBlockEndpoint (start + n)
        (∫ ts in harper1144OverlapShell q,
            harperTwoHeightCorrelation y ts.1 ts.2 *
              (harperTwoHeightCubeLaw y ts.1 ts.2).real
                (harper1144LogBallotCubeEvent y start n ts.1 ∩
                  harper1144LogBallotCubeEvent y start n ts.2)
          ∂(volume.restrict harperLowerVerticalBand).prod
            (volume.restrict harperLowerVerticalBand)) <=
          C * (4 : Real) ^ start *
            harper1144OverlapShellWeight n q := by
  obtain ⟨C₀, hC₀, J, hpoint⟩ :=
    exists_harper1144LogBallot_naturalShell_pointwise_le
  refine ⟨8 * C₀, by positivity, J, ?_⟩
  intro start hstart n q hq
  dsimp only
  let d : Nat := q + 1
  let m : Nat := n - (q + 1)
  let y : Nat := Problem520.harperBlockEndpoint (start + n)
  have hm : 0 < m := by dsimp only [m]; omega
  have hsum : d + m = n := by dsimp only [d, m]; omega
  let f : Real × Real -> Real := fun ts =>
    harperTwoHeightCorrelation y ts.1 ts.2 *
      (harperTwoHeightCubeLaw y ts.1 ts.2).real
        (harper1144LogBallotCubeEvent y start n ts.1 ∩
          harper1144LogBallotCubeEvent y start n ts.2)
  have hfNonneg : ∀ ts, 0 <= f ts := fun ts =>
    mul_nonneg (harperTwoHeightCorrelation_pos y ts.1 ts.2).le
      measureReal_nonneg
  have hpoint' : ∀ ts ∈
      harperLowerVerticalBand ×ˢ harperLowerVerticalBand,
      ts ∈ harper1144OverlapShell q ->
        f ts <= C₀ * (4 : Real) ^ start * (2 : Real) ^ (q + 1) /
          (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
          ((((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹) := by
    intro ts hband hshell
    have hsepInv := (mem_harper1144OverlapShell_iff.mp hshell).1
    have hsep : (1 / 2 : Real) ^ (q + 1) < |ts.1 - ts.2| := by
      rw [show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num, inv_pow]
      exact hsepInv
    have hyEq :
        Problem520.harperBlockEndpoint (start + (d + m)) = y := by
      dsimp only [y]
      rw [hsum]
    have hmain := hpoint start q d m y hstart (by simp [d]) hm
      hyEq ts.1 hband.1 ts.2 hband.2 hsep
    simpa only [f, hsum] using hmain
  have hintegral :=
    integral_harper1144OverlapShell_le_of_naturalRooted_bound
      q start d m C₀ hC₀.le f hfNonneg hpoint'
  have hnumeric := harper1144_naturalShell_numeric_le_weight hq
  have hfactor :
      (2 * C₀ / 3) * (4 : Real) ^ start /
          (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
          ((((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹) <=
        (8 * C₀) * (4 : Real) ^ start *
          harper1144OverlapShellWeight n q := by
    dsimp only [d, m]
    have hmul : 0 <= C₀ * (4 : Real) ^ start := by positivity
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
      _ <= (C₀ * (4 : Real) ^ start) *
          (8 * harper1144OverlapShellWeight n q) :=
        mul_le_mul_of_nonneg_left hnumeric hmul
      _ = (8 * C₀) * (4 : Real) ^ start *
          harper1144OverlapShellWeight n q := by ring
  exact hintegral.trans (by simpa only [f, y, hsum] using hfactor)

/-- Integrating a uniform nonnegative pointwise bound over one dyadic shell
costs only the shell's explicit width. -/
theorem integral_harper1144OverlapShell_le_of_bound
    (q : Nat) (M : Real) (hM : 0 <= M)
    (f : Real × Real -> Real) (hfNonneg : ∀ ts, 0 <= f ts)
    (hpoint : ∀ ts ∈ harperLowerVerticalBand ×ˢ harperLowerVerticalBand,
      ts ∈ harper1144OverlapShell q -> f ts <= M) :
    (∫ ts in harper1144OverlapShell q, f ts
        ∂(volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) <=
      M * ((1 / 3 : Real) * ((2 : Real) ^ q)⁻¹) := by
  let nu : Measure Real := volume.restrict harperLowerVerticalBand
  let mu : Measure (Real × Real) := nu.prod nu
  have hbandFinite : volume harperLowerVerticalBand ≠ ∞ := by
    simp [harperLowerVerticalBand, Real.volume_Icc]
  letI : IsFiniteMeasure nu := isFiniteMeasure_restrict.2 hbandFinite
  have hband : ∀ᵐ ts ∂mu,
      ts ∈ harperLowerVerticalBand ×ˢ harperLowerVerticalBand := by
    rw [Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_harperLowerVerticalBand.prod
        measurableSet_harperLowerVerticalBand)]
    filter_upwards [ae_restrict_mem measurableSet_harperLowerVerticalBand]
      with t ht
    filter_upwards [ae_restrict_mem measurableSet_harperLowerVerticalBand]
      with s hs
    exact ⟨ht, hs⟩
  have hstripFinite : mu (harper1144OverlapShell q) < ∞ :=
    measure_lt_top _ _
  have hnorm :
      ‖∫ ts in harper1144OverlapShell q, f ts ∂mu‖ <=
        M * mu.real (harper1144OverlapShell q) := by
    apply norm_setIntegral_le_of_norm_le_const_ae' hstripFinite
    filter_upwards [hband] with ts hts
    rw [Real.norm_eq_abs, abs_of_nonneg (hfNonneg ts)]
    exact hpoint ts hts
  have hintegralNonneg :
      0 <= ∫ ts in harper1144OverlapShell q, f ts ∂mu :=
    integral_nonneg_of_ae (ae_of_all _ fun ts => hfNonneg ts)
  have hmeasure := measureReal_harper1144OverlapShell_le q
  calc
    (∫ ts in harper1144OverlapShell q, f ts ∂
        (volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) =
        ∫ ts in harper1144OverlapShell q, f ts ∂mu := by rfl
    _ <= ‖∫ ts in harper1144OverlapShell q, f ts ∂mu‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hintegralNonneg]
    _ <= M * mu.real (harper1144OverlapShell q) := hnorm
    _ <= M * ((1 / 3 : Real) * ((2 : Real) ^ q)⁻¹) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [mu, nu] using hmeasure) hM

/-- The last dyadic shell is paid for by the terminal fourth-power pinch.
It satisfies the same summable shell weight without invoking a zero-length
suffix. -/
theorem exists_harper1144LogBallot_fixedStart_terminalShell_integral_le :
    ∃ C > 0, ∃ J : Nat, ∀ start : Nat, J <= start ->
      ∀ n : Nat, 0 < n ->
        let y := Problem520.harperBlockEndpoint (start + n)
        (∫ ts in harper1144OverlapShell (n - 1),
            harperTwoHeightCorrelation y ts.1 ts.2 *
              (harperTwoHeightCubeLaw y ts.1 ts.2).real
                (harper1144LogBallotCubeEvent y start n ts.1 ∩
                  harper1144LogBallotCubeEvent y start n ts.2)
          ∂(volume.restrict harperLowerVerticalBand).prod
            (volume.restrict harperLowerVerticalBand)) <=
          C * (4 : Real) ^ start *
            harper1144OverlapShellWeight n (n - 1) := by
  obtain ⟨C₀, hC₀, J, hterminal⟩ :=
    exists_harperTerminalCapped_correlation_probability_le_powTwo_mul_four_pow_div_sq
  refine ⟨4 * C₀ / 3, by positivity, J, ?_⟩
  intro start hstart n hn
  dsimp only
  let y := Problem520.harperBlockEndpoint (start + n)
  let f : Real × Real -> Real := fun ts =>
    harperTwoHeightCorrelation y ts.1 ts.2 *
      (harperTwoHeightCubeLaw y ts.1 ts.2).real
        (harper1144LogBallotCubeEvent y start n ts.1 ∩
          harper1144LogBallotCubeEvent y start n ts.2)
  let M : Real := C₀ * (2 : Real) ^ n * (n : Real)⁻¹ *
    (n : Real)⁻¹ * (n : Real)⁻¹ * (n : Real)⁻¹ *
      (4 : Real) ^ start
  have hfNonneg : ∀ ts, 0 <= f ts := fun ts =>
    mul_nonneg (harperTwoHeightCorrelation_pos y ts.1 ts.2).le
      measureReal_nonneg
  have hM : 0 <= M := by dsimp only [M]; positivity
  have hpoint : ∀ ts ∈
      harperLowerVerticalBand ×ˢ harperLowerVerticalBand,
      ts ∈ harper1144OverlapShell (n - 1) -> f ts <= M := by
    intro ts hband _hshell
    have hmeasure :
        (harperTwoHeightCubeLaw y ts.1 ts.2).real
            (harper1144LogBallotCubeEvent y start n ts.1 ∩
              harper1144LogBallotCubeEvent y start n ts.2) <=
          (harperTwoHeightCubeLaw y ts.1 ts.2).real
            (harperTerminalCappedCentralLowerBallotCubeEvent
                  y start n ts.1 ∩
              harperTerminalCappedCentralLowerBallotCubeEvent
                  y start n ts.2) :=
      measureReal_mono
        (harper1144LogBallotCubeEvent_inter_subset_terminalCapped
          y start n ts.1 ts.2 hn)
    have hbase := hterminal start n y hstart hn rfl
      ts.1 hband.1 ts.2 hband.2
    calc
      f ts <= harperTwoHeightCorrelation y ts.1 ts.2 *
          (harperTwoHeightCubeLaw y ts.1 ts.2).real
            (harperTerminalCappedCentralLowerBallotCubeEvent
                  y start n ts.1 ∩
              harperTerminalCappedCentralLowerBallotCubeEvent
                  y start n ts.2) :=
        mul_le_mul_of_nonneg_left hmeasure
          (harperTwoHeightCorrelation_pos y ts.1 ts.2).le
      _ <= M := by simpa only [M, y] using hbase
  have hintegral := integral_harper1144OverlapShell_le_of_bound
    (n - 1) M hM f hfNonneg hpoint
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hnOne : (1 : Real) <= n := by exact_mod_cast hn
  have hinvLe : (n : Real)⁻¹ <= 1 := (inv_le_one₀ hnR).2 hnOne
  have hpowCancel :
      (2 : Real) ^ n * ((2 : Real) ^ (n - 1))⁻¹ = 2 := by
    have hnSplit : n = (n - 1) + 1 := by omega
    have hpowN : (2 : Real) ^ n = (2 : Real) ^ (n - 1) * 2 := by
      exact (congrArg (fun k : Nat => (2 : Real) ^ k) hnSplit).trans
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
      M * ((1 / 3 : Real) * ((2 : Real) ^ (n - 1))⁻¹) <=
        (4 * C₀ / 3) * (4 : Real) ^ start *
          harper1144OverlapShellWeight n (n - 1) := by
    rw [hweight]
    dsimp only [M]
    have hsq : (n : Real)⁻¹ * (n : Real)⁻¹ <= 1 := by
      have hinvNonneg : 0 <= (n : Real)⁻¹ := by positivity
      nlinarith [mul_nonneg hinvNonneg (sub_nonneg.mpr hinvLe)]
    have hnonneg : 0 <=
        (2 * C₀ / 3) * (4 : Real) ^ start *
          ((n : Real)⁻¹ * (n : Real)⁻¹) := by positivity
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
      _ <= (2 * C₀ / 3) * (4 : Real) ^ start *
            ((n : Real)⁻¹ * (n : Real)⁻¹) * 1 := by
        gcongr
      _ = (4 * C₀ / 3) * (4 : Real) ^ start *
          (((n : Real) ^ (2 : Nat)) * 2)⁻¹ := by
        field_simp
        ring
  exact hintegral.trans (by simpa only [f, y] using hfinal)

/-- Fixed-start replacement for the older guarded overlap-shell statement.
Every dyadic shell now has the exact summable weight, with one absolute
constant and one start independent of the path length. -/
def Harper1144TwoHeightFixedStartOverlapShellStatement : Prop :=
  ∃ C > 0, ∃ start : Nat, ∀ n : Nat, 0 < n ->
    let y := Problem520.harperBlockEndpoint (start + n)
    ∀ r < n,
      (∫ ts in harper1144OverlapShell r,
          harperTwoHeightCorrelation y ts.1 ts.2 *
            (harperTwoHeightCubeLaw y ts.1 ts.2).real
              (harper1144LogBallotCubeEvent y start n ts.1 ∩
                harper1144LogBallotCubeEvent y start n ts.2)
        ∂(volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) <=
        C * harper1144OverlapShellWeight n r

/-- The natural-coherence suffix and terminal fourth-power pinch instantiate
the complete fixed-start overlap-shell statement unconditionally. -/
theorem harper1144TwoHeightFixedStartOverlapShellStatement_unconditional :
    Harper1144TwoHeightFixedStartOverlapShellStatement := by
  obtain ⟨C₀, hC₀, J₀, hnatural⟩ :=
    exists_harper1144LogBallot_fixedStart_naturalShell_integral_le
  obtain ⟨C₁, hC₁, J₁, hterminal⟩ :=
    exists_harper1144LogBallot_fixedStart_terminalShell_integral_le
  let start : Nat := max J₀ J₁
  let C : Real := (C₀ + C₁) * (4 : Real) ^ start
  refine ⟨C, by dsimp only [C]; positivity, start, ?_⟩
  intro n hn
  dsimp only
  let y := Problem520.harperBlockEndpoint (start + n)
  intro r hr
  have hstart₀ : J₀ <= start := le_max_left _ _
  have hstart₁ : J₁ <= start := le_max_right _ _
  by_cases hnonterminal : r + 2 <= n
  · have hmain := hnatural start hstart₀ n r hnonterminal
    have hweight := harper1144OverlapShellWeight_nonneg n r
    calc
      (∫ ts in harper1144OverlapShell r,
          harperTwoHeightCorrelation y ts.1 ts.2 *
            (harperTwoHeightCubeLaw y ts.1 ts.2).real
              (harper1144LogBallotCubeEvent y start n ts.1 ∩
                harper1144LogBallotCubeEvent y start n ts.2)
        ∂(volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) <=
          C₀ * (4 : Real) ^ start *
            harper1144OverlapShellWeight n r := by
        simpa only [y] using hmain
      _ <= (C₀ + C₁) * (4 : Real) ^ start *
            harper1144OverlapShellWeight n r := by
        have : C₀ <= C₀ + C₁ := by linarith
        gcongr
      _ = C * harper1144OverlapShellWeight n r := by
        dsimp only [C]
  · have hrLast : r = n - 1 := by omega
    subst r
    have hmain := hterminal start hstart₁ n hn
    have hweight := harper1144OverlapShellWeight_nonneg n (n - 1)
    calc
      (∫ ts in harper1144OverlapShell (n - 1),
          harperTwoHeightCorrelation y ts.1 ts.2 *
            (harperTwoHeightCubeLaw y ts.1 ts.2).real
              (harper1144LogBallotCubeEvent y start n ts.1 ∩
                harper1144LogBallotCubeEvent y start n ts.2)
        ∂(volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) <=
          C₁ * (4 : Real) ^ start *
            harper1144OverlapShellWeight n (n - 1) := by
        simpa only [y] using hmain
      _ <= (C₀ + C₁) * (4 : Real) ^ start *
            harper1144OverlapShellWeight n (n - 1) := by
        have : C₁ <= C₀ + C₁ := by linarith
        gcongr
      _ = C * harper1144OverlapShellWeight n (n - 1) := by
        dsimp only [C]

/-- Consequently the sum of all separated-height shell integrals is
`O(1/n)` at one fixed start. -/
theorem exists_harper1144LogBallot_fixedStart_overlapShellSum_le :
    ∃ C > 0, ∃ start : Nat, ∀ n : Nat, 0 < n ->
      let y := Problem520.harperBlockEndpoint (start + n)
      let f : Real × Real -> Real := fun ts =>
        harperTwoHeightCorrelation y ts.1 ts.2 *
          (harperTwoHeightCubeLaw y ts.1 ts.2).real
            (harper1144LogBallotCubeEvent y start n ts.1 ∩
              harper1144LogBallotCubeEvent y start n ts.2)
      (∑ r ∈ Finset.range n,
        ∫ ts in harper1144OverlapShell r, f ts
          ∂(volume.restrict harperLowerVerticalBand).prod
            (volume.restrict harperLowerVerticalBand)) <=
        C * (n : Real)⁻¹ := by
  obtain ⟨C₀, hC₀, start, hshell⟩ :=
    harper1144TwoHeightFixedStartOverlapShellStatement_unconditional
  refine ⟨4 * C₀, by positivity, start, ?_⟩
  intro n hn
  dsimp only
  let y := Problem520.harperBlockEndpoint (start + n)
  let f : Real × Real -> Real := fun ts =>
    harperTwoHeightCorrelation y ts.1 ts.2 *
      (harperTwoHeightCubeLaw y ts.1 ts.2).real
        (harper1144LogBallotCubeEvent y start n ts.1 ∩
          harper1144LogBallotCubeEvent y start n ts.2)
  have hsum := sum_harper1144OverlapShell_integrals_le_of_bound
    n hn C₀ hC₀.le f (fun r hr => by
      simpa only [f, y] using hshell n hn r hr)
  simpa only [f, y] using hsum

/-- Uniform fixed-start form of the terminal-strip estimate.  The displayed
`4^start` is harmless because `start` will be chosen once and for all. -/
theorem exists_harper1144LogBallot_fixedStart_nearDiagonal_uniform_le :
    ∃ C > 0, ∃ J : Nat, ∀ start : Nat, J <= start ->
      ∀ n : Nat, 0 < n ->
        let y := Problem520.harperBlockEndpoint (start + n)
        (∫ ts in harperTerminalNearDiagonalStrip n,
            harperTwoHeightCorrelation y ts.1 ts.2 *
              (harperTwoHeightCubeLaw y ts.1 ts.2).real
                (harper1144LogBallotCubeEvent y start n ts.1 ∩
                  harper1144LogBallotCubeEvent y start n ts.2)
          ∂(volume.restrict harperLowerVerticalBand).prod
            (volume.restrict harperLowerVerticalBand)) <=
          C * (4 : Real) ^ start * (n : Real)⁻¹ := by
  obtain ⟨C₀, hC₀, J, hterminal⟩ :=
    exists_harperTerminalCapped_correlation_probability_le_powTwo_mul_four_pow_div_sq
  refine ⟨C₀ / 3, by positivity, J, ?_⟩
  intro start hstart n hn
  dsimp only
  let y := Problem520.harperBlockEndpoint (start + n)
  let f : Real × Real -> Real := fun ts =>
    harperTwoHeightCorrelation y ts.1 ts.2 *
      (harperTwoHeightCubeLaw y ts.1 ts.2).real
        (harper1144LogBallotCubeEvent y start n ts.1 ∩
          harper1144LogBallotCubeEvent y start n ts.2)
  let K : Real := C₀ * (4 : Real) ^ start
  have hK : 0 <= K := by dsimp only [K]; positivity
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hnOne : (1 : Real) <= n := by exact_mod_cast hn
  have hinvLe : (n : Real)⁻¹ <= 1 := (inv_le_one₀ hnR).2 hnOne
  have hbound : ∀ ts,
      ts.1 ∈ harperLowerVerticalBand ->
      ts.2 ∈ harperLowerVerticalBand ->
      f ts <= K * (2 : Real) ^ n * (n : Real)⁻¹ := by
    intro ts ht hs
    have hmeasure :
        (harperTwoHeightCubeLaw y ts.1 ts.2).real
            (harper1144LogBallotCubeEvent y start n ts.1 ∩
              harper1144LogBallotCubeEvent y start n ts.2) <=
          (harperTwoHeightCubeLaw y ts.1 ts.2).real
            (harperTerminalCappedCentralLowerBallotCubeEvent
                  y start n ts.1 ∩
              harperTerminalCappedCentralLowerBallotCubeEvent
                  y start n ts.2) :=
      measureReal_mono
        (harper1144LogBallotCubeEvent_inter_subset_terminalCapped
          y start n ts.1 ts.2 hn)
    have hbase := hterminal start n y hstart hn rfl
      ts.1 ht ts.2 hs
    calc
      f ts <= harperTwoHeightCorrelation y ts.1 ts.2 *
          (harperTwoHeightCubeLaw y ts.1 ts.2).real
            (harperTerminalCappedCentralLowerBallotCubeEvent
                  y start n ts.1 ∩
              harperTerminalCappedCentralLowerBallotCubeEvent
                  y start n ts.2) :=
        mul_le_mul_of_nonneg_left hmeasure
          (harperTwoHeightCorrelation_pos y ts.1 ts.2).le
      _ <= C₀ * (2 : Real) ^ n * (n : Real)⁻¹ *
            (n : Real)⁻¹ * (n : Real)⁻¹ * (n : Real)⁻¹ *
              (4 : Real) ^ start := hbase
      _ <= C₀ * (2 : Real) ^ n * (n : Real)⁻¹ * 1 * 1 * 1 *
              (4 : Real) ^ start := by gcongr
      _ = K * (2 : Real) ^ n * (n : Real)⁻¹ := by
        dsimp only [K]
        ring
  have hresult := integral_harperTerminalNearDiagonalStrip_le_of_bound
    n hn f K hK
    (fun ts => mul_nonneg
      (harperTwoHeightCorrelation_pos y ts.1 ts.2).le measureReal_nonneg)
    hbound
  calc
    (∫ ts in harperTerminalNearDiagonalStrip n,
        harperTwoHeightCorrelation
            (Problem520.harperBlockEndpoint (start + n)) ts.1 ts.2 *
          (harperTwoHeightCubeLaw
            (Problem520.harperBlockEndpoint (start + n)) ts.1 ts.2).real
            (harper1144LogBallotCubeEvent
                  (Problem520.harperBlockEndpoint (start + n)) start n ts.1 ∩
              harper1144LogBallotCubeEvent
                  (Problem520.harperBlockEndpoint (start + n)) start n ts.2)
      ∂(volume.restrict harperLowerVerticalBand).prod
        (volume.restrict harperLowerVerticalBand)) <=
        K / 3 * (n : Real)⁻¹ := by simpa only [f, y] using hresult
    _ = (C₀ / 3) * (4 : Real) ^ start * (n : Real)⁻¹ := by
      dsimp only [K]
      ring

/-- Integrating the pointwise rooted estimate over shell `q` cancels the
factor `2^(q+1)` against the shell width. -/
theorem integral_harper1144OverlapShell_le_of_rooted_bound
    (q start d m : Nat) (C : Real) (hC : 0 ≤ C)
    (f : Real × Real → Real) (hfNonneg : ∀ ts, 0 ≤ f ts)
    (hpoint : ∀ ts ∈ harperLowerVerticalBand ×ˢ harperLowerVerticalBand,
      ts ∈ harper1144OverlapShell q →
        f ts ≤ C * (4 : Real) ^ start * (2 : Real) ^ (q + 1) /
          (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
          (5000 * (64 * (d : Real) + 4) ^ (2 : Nat) *
            (m : Real)⁻¹)) :
    (∫ ts in harper1144OverlapShell q, f ts
        ∂(volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) ≤
      (2 * C / 3) * (4 : Real) ^ start /
        (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
        (5000 * (64 * (d : Real) + 4) ^ (2 : Nat) *
          (m : Real)⁻¹) := by
  let nu : Measure Real := volume.restrict harperLowerVerticalBand
  let mu : Measure (Real × Real) := nu.prod nu
  let M : Real := C * (4 : Real) ^ start * (2 : Real) ^ (q + 1) /
    (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
    (5000 * (64 * (d : Real) + 4) ^ (2 : Nat) * (m : Real)⁻¹)
  have hbandFinite : volume harperLowerVerticalBand ≠ ∞ := by
    simp [harperLowerVerticalBand, Real.volume_Icc]
  letI : IsFiniteMeasure nu := isFiniteMeasure_restrict.2 hbandFinite
  have hband : ∀ᵐ ts ∂mu,
      ts ∈ harperLowerVerticalBand ×ˢ harperLowerVerticalBand := by
    rw [Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_harperLowerVerticalBand.prod
        measurableSet_harperLowerVerticalBand)]
    filter_upwards [ae_restrict_mem measurableSet_harperLowerVerticalBand]
      with t ht
    filter_upwards [ae_restrict_mem measurableSet_harperLowerVerticalBand]
      with s hs
    exact ⟨ht, hs⟩
  have hstripFinite : mu (harper1144OverlapShell q) < ∞ :=
    measure_lt_top _ _
  have hnorm :
      ‖∫ ts in harper1144OverlapShell q, f ts ∂mu‖ ≤
        M * mu.real (harper1144OverlapShell q) := by
    apply norm_setIntegral_le_of_norm_le_const_ae' hstripFinite
    filter_upwards [hband] with ts hts
    rw [Real.norm_eq_abs, abs_of_nonneg (hfNonneg ts)]
    exact hpoint ts hts
  have hintegralNonneg :
      0 ≤ ∫ ts in harper1144OverlapShell q, f ts ∂mu :=
    integral_nonneg_of_ae (ae_of_all _ fun ts ↦ hfNonneg ts)
  have hmeasure := measureReal_harper1144OverlapShell_le q
  have hMnonneg : 0 ≤ M := by
    dsimp only [M]
    positivity
  calc
    (∫ ts in harper1144OverlapShell q, f ts ∂
        (volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) =
        ∫ ts in harper1144OverlapShell q, f ts ∂mu := by rfl
    _ ≤ ‖∫ ts in harper1144OverlapShell q, f ts ∂mu‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hintegralNonneg]
    _ ≤ M * mu.real (harper1144OverlapShell q) := hnorm
    _ ≤ M * ((1 / 3 : Real) * ((2 : Real) ^ q)⁻¹) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [mu, nu] using hmeasure)
        hMnonneg
    _ = (2 * C / 3) * (4 : Real) ^ start /
          (((q + 1 : Nat) : Real) ^ (4 : Nat)) *
          (5000 * (64 * (d : Real) + 4) ^ (2 : Nat) *
            (m : Real)⁻¹) := by
      dsimp only [M]
      have hpow : (2 : Real) ^ q ≠ 0 := by positivity
      rw [pow_succ]
      field_simp

/-- The ultra-near diagonal also works with one fixed initial block.  The
terminal fourth-power pinch has three spare powers of `n`, so no growing
guard is needed for this upper bound. -/
theorem exists_harper1144LogBallotFixedStart_nearDiagonal_integral_le :
    ∃ C > 0, ∃ start : Nat, ∀ n : Nat, 0 < n →
      let y := Problem520.harperBlockEndpoint (start + n)
      (∫ ts in harperTerminalNearDiagonalStrip n,
          harperTwoHeightCorrelation y ts.1 ts.2 *
            (harperTwoHeightCubeLaw y ts.1 ts.2).real
              (harper1144LogBallotCubeEvent y start n ts.1 ∩
                harper1144LogBallotCubeEvent y start n ts.2)
        ∂(volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) ≤
        C * (n : Real)⁻¹ := by
  obtain ⟨C₀, hC₀, J₀, hterminal⟩ :=
    exists_harperTerminalCapped_correlation_probability_le_powTwo_mul_four_pow_div_sq
  let C : Real := C₀ * (4 : Real) ^ J₀ / 3
  refine ⟨C, by dsimp only [C]; positivity, J₀, ?_⟩
  intro n hn
  dsimp only
  let y := Problem520.harperBlockEndpoint (J₀ + n)
  let f : Real × Real → Real := fun ts ↦
    harperTwoHeightCorrelation y ts.1 ts.2 *
      (harperTwoHeightCubeLaw y ts.1 ts.2).real
        (harper1144LogBallotCubeEvent y J₀ n ts.1 ∩
          harper1144LogBallotCubeEvent y J₀ n ts.2)
  have hpoint (ts : Real × Real)
      (ht : ts.1 ∈ harperLowerVerticalBand)
      (hs : ts.2 ∈ harperLowerVerticalBand) :
      f ts ≤ (C₀ * (4 : Real) ^ J₀) *
        (2 : Real) ^ n * (n : Real)⁻¹ := by
    have hmeasure :
        (harperTwoHeightCubeLaw y ts.1 ts.2).real
            (harper1144LogBallotCubeEvent y J₀ n ts.1 ∩
              harper1144LogBallotCubeEvent y J₀ n ts.2) ≤
          (harperTwoHeightCubeLaw y ts.1 ts.2).real
            (harperTerminalCappedCentralLowerBallotCubeEvent
                  y J₀ n ts.1 ∩
              harperTerminalCappedCentralLowerBallotCubeEvent
                  y J₀ n ts.2) :=
      measureReal_mono
        (harper1144LogBallotCubeEvent_inter_subset_terminalCapped
          y J₀ n ts.1 ts.2 hn)
    have hbase := hterminal J₀ n y le_rfl hn rfl ts.1 ht ts.2 hs
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
    have hinvLe : (n : Real)⁻¹ ≤ 1 :=
      (inv_le_one₀ (by positivity)).2 hnR
    calc
      f ts ≤ harperTwoHeightCorrelation y ts.1 ts.2 *
          (harperTwoHeightCubeLaw y ts.1 ts.2).real
            (harperTerminalCappedCentralLowerBallotCubeEvent
                  y J₀ n ts.1 ∩
              harperTerminalCappedCentralLowerBallotCubeEvent
                  y J₀ n ts.2) :=
        mul_le_mul_of_nonneg_left hmeasure
          (harperTwoHeightCorrelation_pos y ts.1 ts.2).le
      _ ≤ C₀ * (2 : Real) ^ n * (n : Real)⁻¹ *
          (n : Real)⁻¹ * (n : Real)⁻¹ * (n : Real)⁻¹ *
            (4 : Real) ^ J₀ := hbase
      _ ≤ C₀ * (2 : Real) ^ n * (n : Real)⁻¹ *
          1 * 1 * 1 * (4 : Real) ^ J₀ := by gcongr
      _ = (C₀ * (4 : Real) ^ J₀) *
          (2 : Real) ^ n * (n : Real)⁻¹ := by ring
  have hintegral := integral_harperTerminalNearDiagonalStrip_le_of_bound
    n hn f (C₀ * (4 : Real) ^ J₀) (by positivity)
    (fun ts ↦ mul_nonneg
      (harperTwoHeightCorrelation_pos y ts.1 ts.2).le measureReal_nonneg)
    hpoint
  simpa only [f, y, C] using hintegral

end

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.exists_harper1144LogBallot_shell_pointwise_le
#print axioms Erdos.Problem1144.integral_harper1144OverlapShell_le_of_rooted_bound
#print axioms Erdos.Problem1144.exists_harper1144LogBallotFixedStart_nearDiagonal_integral_le
#print axioms Erdos.Problem1144.exists_harper1144LogBallot_naturalShell_pointwise_le
#print axioms Erdos.Problem1144.harper1144_naturalShell_numeric_le_weight
#print axioms Erdos.Problem1144.exists_harper1144LogBallot_fixedStart_naturalShell_integral_le
#print axioms Erdos.Problem1144.exists_harper1144LogBallot_fixedStart_terminalShell_integral_le
#print axioms Erdos.Problem1144.harper1144TwoHeightFixedStartOverlapShellStatement_unconditional
#print axioms Erdos.Problem1144.exists_harper1144LogBallot_fixedStart_overlapShellSum_le
#print axioms Erdos.Problem1144.exists_harper1144LogBallot_fixedStart_nearDiagonal_uniform_le
