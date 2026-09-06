import Erdos.Problem1144.HarperGaussianDecorrelation

open Finset MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# A concrete summable cutoff for the two-height block comparison

For a path of length `n`, take the Fejer cutoff `T = n^6` and tail parameter
`r = n^4`.  The enlargement of each increment rectangle is then `4/n^2`,
whereas the local tail/retention loss is `O(n^-4)`.  For the path corridors,
whose widths are at most `65n`, post-coherence covariance `n^-40` and block
endpoint square root at least `2^20 n^48` make the two Fourier errors
`O(n^-4)` as well.

This is deliberately wasteful.  Its purpose is to replace the qualitative
instruction “choose summable cutoffs” by one explicit schedule with ample
room for the later ballot recursion.
-/

set_option maxHeartbeats 800000 in
/-- The concrete cutoff schedule turns the full one-block comparison into a
path-corridor rectangle estimate with enlargement `4/n^2` and error `6/n^4`.
The width `65n` is the deterministic corridor budget of the forward-pinched
event. -/
theorem harperScheduledTwoHeightCorridorRectangleMass_le_independentGaussian_cutoff
    (y j n : Nat) (t s : Real) {a b c d : Real}
    (hn : 4 ≤ n)
    (hab : a ≤ b) (hcd : c ≤ d)
    (habWidth : b - a ≤ 65 * (n : Real))
    (hcdWidth : d - c ≤ 65 * (n : Real))
    (hfrequency :
      4 * (n : Real) ^ (6 : Nat) ≤
        Real.sqrt (Problem520.harperBlockEndpoint j : Real))
    (hendpoint :
      1048576 * (n : Real) ^ (48 : Nat) ≤
        Real.sqrt (Problem520.harperBlockEndpoint j : Real))
    (hcovariance :
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y j) t s t s| ≤
        1 / (n : Real) ^ (40 : Nat)) :
    ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat) *
        (harperTwoHeightPrimeBlockVectorLaw y
          (Problem520.harperScheduledPrimeBlock y j) t s).real
            (Ioc a b ×ˢ Ioc c d) ≤
      (harperTwoHeightIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y j) t s).real
          (Ioc (a - 4 * (1 / (n : Real) ^ (2 : Nat)))
              (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
            Ioc (c - 4 * (1 / (n : Real) ^ (2 : Nat)))
              (d + 4 * (1 / (n : Real) ^ (2 : Nat)))) +
        6 / (n : Real) ^ (4 : Nat) := by
  let N : Real := n
  have hN : 4 ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hN2pos : 0 < N ^ (2 : Nat) := pow_pos hNpos _
  have hN4pos : 0 < N ^ (4 : Nat) := pow_pos hNpos _
  have hN8pos : 0 < N ^ (8 : Nat) := pow_pos hNpos _
  have hN40pos : 0 < N ^ (40 : Nat) := pow_pos hNpos _
  have hN48pos : 0 < N ^ (48 : Nat) := pow_pos hNpos _
  have hratio : N ^ (4 : Nat) / N ^ (6 : Nat) = 1 / N ^ (2 : Nat) := by
    field_simp
  have hdelta : 1 / N ^ (2 : Nat) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ hN2pos (by norm_num : (0 : Real) < 16)]
    nlinarith [sq_nonneg (N - 4)]
  have hpiInv : (2 * Real.pi)⁻¹ ≤ (1 : Real) := by
    apply inv_le_one_of_one_le₀
    linarith [Real.pi_gt_three]
  have hpiInv0 : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hpiFactor : (2 * Real.pi)⁻¹ ^ (2 : Nat) ≤ (1 : Real) := by
    nlinarith [sq_nonneg ((2 * Real.pi)⁻¹ - 1)]
  have hfactorG1 :
      |(b + 3 * (1 / N ^ (2 : Nat))) -
          (a - 3 * (1 / N ^ (2 : Nat)))| ≤ 66 * N := by
    rw [abs_of_nonneg]
    · nlinarith
    · nlinarith [div_nonneg (by norm_num : (0 : Real) ≤ 1) hN2pos.le]
  have hfactorG2 :
      |(d + 3 * (1 / N ^ (2 : Nat))) -
          (c - 3 * (1 / N ^ (2 : Nat)))| ≤ 66 * N := by
    rw [abs_of_nonneg]
    · nlinarith
    · nlinarith [div_nonneg (by norm_num : (0 : Real) ≤ 1) hN2pos.le]
  have hfactorR1 :
      |(b + 1 / N ^ (2 : Nat)) -
          (a - 1 / N ^ (2 : Nat))| ≤ 66 * N := by
    rw [abs_of_nonneg]
    · nlinarith
    · nlinarith [div_nonneg (by norm_num : (0 : Real) ≤ 1) hN2pos.le]
  have hfactorR2 :
      |(d + 1 / N ^ (2 : Nat)) -
          (c - 1 / N ^ (2 : Nat))| ≤ 66 * N := by
    rw [abs_of_nonneg]
    · nlinarith
    · nlinarith [div_nonneg (by norm_num : (0 : Real) ≤ 1) hN2pos.le]
  let covariance : Real :=
    |harperTwoHeightBlockCoordinateCovariance y
      (Problem520.harperScheduledPrimeBlock y j) t s t s|
  let EG : Real :=
    (2 * Real.pi)⁻¹ ^ (2 : Nat) *
      |(b + 3 * (1 / N ^ (2 : Nat))) -
        (a - 3 * (1 / N ^ (2 : Nat)))| *
      |(d + 3 * (1 / N ^ (2 : Nat))) -
        (c - 3 * (1 / N ^ (2 : Nat)))| *
      (16 * covariance * (N ^ (6 : Nat)) ^ (4 : Nat))
  have hEG : EG ≤ 1 / N ^ (4 : Nat) := by
    have hcov : covariance ≤ 1 / N ^ (40 : Nat) := by
      simpa only [covariance, N] using hcovariance
    calc
      EG ≤ 1 * (66 * N) * (66 * N) *
          (16 * (1 / N ^ (40 : Nat)) *
            (N ^ (6 : Nat)) ^ (4 : Nat)) := by
        dsimp only [EG]
        gcongr
      _ = 69696 / N ^ (14 : Nat) := by
        field_simp
        ring
      _ ≤ 1 / N ^ (4 : Nat) := by
        have hN14pos : 0 < N ^ (14 : Nat) := pow_pos hNpos _
        have hN10 : (69696 : Real) ≤ N ^ (10 : Nat) := by
          calc
            (69696 : Real) ≤ 4 ^ (10 : Nat) := by norm_num
            _ ≤ N ^ (10 : Nat) := by gcongr
        rw [div_le_div_iff₀ hN14pos hN4pos]
        calc
          (69696 : Real) * N ^ (4 : Nat) ≤
              N ^ (10 : Nat) * N ^ (4 : Nat) := by gcongr
          _ = 1 * N ^ (14 : Nat) := by ring
  have hbasePos : 0 < 1048576 * N ^ (48 : Nat) := by positivity
  have hsqrtPos :
      0 < Real.sqrt (Problem520.harperBlockEndpoint j : Real) :=
    hbasePos.trans_le (by simpa only [N] using hendpoint)
  have hinvEndpoint :
      (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ ≤
        (1048576 * N ^ (48 : Nat))⁻¹ := by
    rw [inv_le_inv₀ hsqrtPos hbasePos]
    simpa only [N] using hendpoint
  have hpow30 : N ^ (30 : Nat) ≤ N ^ (36 : Nat) := by
    calc
      N ^ (30 : Nat) = N ^ (30 : Nat) * 1 := by ring
      _ ≤ N ^ (30 : Nat) * N ^ (6 : Nat) := by
        gcongr
        exact one_le_pow₀ hN1
      _ = N ^ (36 : Nat) := by ring
  have hpoly :
      512 * (N ^ (6 : Nat)) ^ (5 : Nat) +
          128 * (N ^ (6 : Nat)) ^ (6 : Nat) ≤
        640 * N ^ (36 : Nat) := by
    calc
      _ = 512 * N ^ (30 : Nat) + 128 * N ^ (36 : Nat) := by ring
      _ ≤ 512 * N ^ (36 : Nat) + 128 * N ^ (36 : Nat) := by gcongr
      _ = 640 * N ^ (36 : Nat) := by ring
  let ER : Real :=
    (2 * Real.pi)⁻¹ ^ (2 : Nat) *
      |(b + 1 / N ^ (2 : Nat)) - (a - 1 / N ^ (2 : Nat))| *
      |(d + 1 / N ^ (2 : Nat)) - (c - 1 / N ^ (2 : Nat))| *
      (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
        (512 * (N ^ (6 : Nat)) ^ (5 : Nat) +
          128 * (N ^ (6 : Nat)) ^ (6 : Nat))
  have hER : ER ≤ 1 / N ^ (4 : Nat) := by
    calc
      ER ≤ 1 * (66 * N) * (66 * N) *
          (1048576 * N ^ (48 : Nat))⁻¹ *
          (640 * N ^ (36 : Nat)) := by
        dsimp only [ER]
        gcongr
      _ = (5445 / 2048 : Real) / N ^ (10 : Nat) := by
        field_simp
        ring
      _ ≤ 1 / N ^ (4 : Nat) := by
        have hN10pos : 0 < N ^ (10 : Nat) := pow_pos hNpos _
        rw [div_le_div_iff₀ hN10pos hN4pos]
        have hsmall : (5445 / 2048 : Real) ≤ N ^ (6 : Nat) := by
          calc
            (5445 / 2048 : Real) ≤ 4 ^ (6 : Nat) := by norm_num
            _ ≤ N ^ (6 : Nat) := by gcongr
        calc
          (5445 / 2048 : Real) * N ^ (4 : Nat) ≤
              N ^ (6 : Nat) * N ^ (4 : Nat) :=
            mul_le_mul_of_nonneg_right hsmall hN4pos.le
          _ = 1 * N ^ (10 : Nat) := by ring
  let beta : Real := (1 - 2 / N ^ (4 : Nat)) ^ (2 : Nat)
  have hN4geTwo : (2 : Real) ≤ N ^ (4 : Nat) := by
    calc
      (2 : Real) ≤ 4 := by norm_num
      _ ≤ N := hN
      _ = N * 1 := by ring
      _ ≤ N * N ^ (3 : Nat) := by
        gcongr
        exact one_le_pow₀ hN1
      _ = N ^ (4 : Nat) := by ring
  have hTwoDiv : 2 / N ^ (4 : Nat) ≤ 1 := by
    rw [div_le_one hN4pos]
    exact hN4geTwo
  have hbeta0 : 0 ≤ beta := by dsimp only [beta]; positivity
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    apply pow_le_one₀
    · exact sub_nonneg.mpr hTwoDiv
    · exact sub_le_self 1 (by positivity)
  have hlocal :=
    harperScheduledTwoHeightRectangleMass_le_independentGaussian_explicit
      y j t s (N ^ (6 : Nat)) (N ^ (4 : Nat)) hab hcd
        (pow_pos hNpos _)
        hN4geTwo
        (by simpa only [N] using hfrequency)
  rw [hratio] at hlocal
  change beta ^ (2 : Nat) *
      (harperTwoHeightPrimeBlockVectorLaw y
        (Problem520.harperScheduledPrimeBlock y j) t s).real
          (Ioc a b ×ˢ Ioc c d) ≤ _
  calc
    _ ≤ (harperTwoHeightIndependentGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y j) t s).real
            (Ioc (a - 4 * (1 / N ^ (2 : Nat)))
                (b + 4 * (1 / N ^ (2 : Nat))) ×ˢ
              Ioc (c - 4 * (1 / N ^ (2 : Nat)))
                (d + 4 * (1 / N ^ (2 : Nat)))) +
          2 / N ^ (4 : Nat) + EG +
          beta * (2 / N ^ (4 : Nat) + ER) := by
      simpa only [beta, EG, ER, covariance] using hlocal
    _ ≤ (harperTwoHeightIndependentGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y j) t s).real
            (Ioc (a - 4 * (1 / N ^ (2 : Nat)))
                (b + 4 * (1 / N ^ (2 : Nat))) ×ˢ
              Ioc (c - 4 * (1 / N ^ (2 : Nat)))
                (d + 4 * (1 / N ^ (2 : Nat)))) +
          6 / N ^ (4 : Nat) := by
      have hinner :
          2 / N ^ (4 : Nat) + ER ≤ 3 / N ^ (4 : Nat) := by
        calc
          2 / N ^ (4 : Nat) + ER ≤
              2 / N ^ (4 : Nat) + 1 / N ^ (4 : Nat) :=
            add_le_add le_rfl hER
          _ = 3 / N ^ (4 : Nat) := by ring
      have hbetaTerm :
          beta * (2 / N ^ (4 : Nat) + ER) ≤
            3 / N ^ (4 : Nat) := by
        calc
          beta * (2 / N ^ (4 : Nat) + ER) ≤
              beta * (3 / N ^ (4 : Nat)) :=
            mul_le_mul_of_nonneg_left hinner hbeta0
          _ ≤ 1 * (3 / N ^ (4 : Nat)) :=
            mul_le_mul_of_nonneg_right hbeta1 (by positivity)
          _ = 3 / N ^ (4 : Nat) := by ring
      have htotal :
          2 / N ^ (4 : Nat) + EG +
              beta * (2 / N ^ (4 : Nat) + ER) ≤
            6 / N ^ (4 : Nat) := by
        calc
          2 / N ^ (4 : Nat) + EG +
              beta * (2 / N ^ (4 : Nat) + ER) ≤
            2 / N ^ (4 : Nat) + 1 / N ^ (4 : Nat) +
              3 / N ^ (4 : Nat) := add_le_add (add_le_add le_rfl hEG)
                hbetaTerm
          _ = 6 / N ^ (4 : Nat) := by ring
      convert add_le_add le_rfl htotal using 1 <;> ring
    _ = _ := by rfl

/-- Along at most `n` blocks, the scheduled rectangle enlargement totals at
most `4/n`. -/
theorem harperTwoHeightCutoff_totalExpansion_le
    {m n : Nat} (hn : 1 ≤ n) (hm : m ≤ n) :
    (m : Real) * (4 / (n : Real) ^ (2 : Nat)) ≤ 4 / (n : Real) := by
  have hNpos : 0 < (n : Real) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hmReal : (m : Real) ≤ (n : Real) := by exact_mod_cast hm
  calc
    (m : Real) * (4 / (n : Real) ^ (2 : Nat)) ≤
        (n : Real) * (4 / (n : Real) ^ (2 : Nat)) := by
      gcongr
    _ = 4 / (n : Real) := by
      field_simp

/-- Along at most `n` blocks, the local comparison errors total at most
`6/n^3`. -/
theorem harperTwoHeightCutoff_totalError_le
    {m n : Nat} (hn : 1 ≤ n) (hm : m ≤ n) :
    (m : Real) * (6 / (n : Real) ^ (4 : Nat)) ≤
      6 / (n : Real) ^ (3 : Nat) := by
  have hNpos : 0 < (n : Real) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hmReal : (m : Real) ≤ (n : Real) := by exact_mod_cast hm
  calc
    (m : Real) * (6 / (n : Real) ^ (4 : Nat)) ≤
        (n : Real) * (6 / (n : Real) ^ (4 : Nat)) := by
      gcongr
    _ = 6 / (n : Real) ^ (3 : Nat) := by
      field_simp

/-- The product of the local Fejer-retention factors loses at most `8/n^3`
over a path of at most `n` blocks. -/
theorem one_sub_eight_div_cube_le_harperTwoHeightCutoff_retention
    {m n : Nat} (hn : 2 ≤ n) (hm : m ≤ n) :
    1 - 8 / (n : Real) ^ (3 : Nat) ≤
      (((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)) ^ m := by
  let N : Real := n
  have hN : 2 ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hNpos : 0 < N := by linarith
  have hmReal : (m : Real) ≤ N := by
    dsimp only [N]
    exact_mod_cast hm
  have hbudget :
      (m : Real) * (8 / N ^ (4 : Nat)) ≤ 8 / N ^ (3 : Nat) := by
    calc
      (m : Real) * (8 / N ^ (4 : Nat)) ≤
          N * (8 / N ^ (4 : Nat)) := by gcongr
      _ = 8 / N ^ (3 : Nat) := by
        field_simp
  have hq : 2 / N ^ (4 : Nat) ≤ 2 := by
    have hpow : (1 : Real) ≤ N ^ (4 : Nat) := one_le_pow₀ (by linarith)
    rw [div_le_iff₀ (pow_pos hNpos (4 : Nat))]
    nlinarith
  have hbern := one_add_mul_le_pow
    (a := -(2 / N ^ (4 : Nat))) (by linarith) (4 * m)
  calc
    1 - 8 / N ^ (3 : Nat) ≤
        1 - (m : Real) * (8 / N ^ (4 : Nat)) := by linarith
    _ = 1 + ((4 * m : Nat) : Real) * (-(2 / N ^ (4 : Nat))) := by
      push_cast
      ring
    _ ≤ (1 - 2 / N ^ (4 : Nat)) ^ (4 * m) := by
      rw [sub_eq_add_neg]
      exact hbern
    _ = (((1 - 2 / N ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)) ^ m := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega

/-- For every fixed path length, a single post-coherence shift makes all
later blocks satisfy the frequency, endpoint, and covariance hypotheses of
the concrete cutoff theorem.  The later availability argument only has to
show that this shift fits below the ambient cutoff. -/
theorem exists_harperTwoHeightCorridorCutoffBlockHypotheses
    {n : Nat} (hn : 4 ≤ n) :
    ∃ J : Nat, ∀ r j y : Nat, J + (r + 1) ≤ j →
      Problem520.harperBlockEndpoint (j + 1) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (r + 1) < |t - s| →
              4 * (n : Real) ^ (6 : Nat) ≤
                  Real.sqrt (Problem520.harperBlockEndpoint j : Real) ∧
                1048576 * (n : Real) ^ (48 : Nat) ≤
                  Real.sqrt (Problem520.harperBlockEndpoint j : Real) ∧
                |harperTwoHeightBlockCoordinateCovariance y
                    (Problem520.harperScheduledPrimeBlock y j) t s t s| ≤
                  1 / (n : Real) ^ (40 : Nat) := by
  have hN : (4 : Real) ≤ n := by exact_mod_cast hn
  have hNpos : (0 : Real) < n := by linarith
  have hsmall : 0 < 1 / (n : Real) ^ (40 : Nat) := by positivity
  obtain ⟨Jcov, hcov⟩ :=
    exists_eventually_harperTwoHeightScheduledCovariance_postCoherence_small
      hsmall
  have hend : Tendsto
      (fun j : Nat ↦ (Problem520.harperBlockEndpoint j : Real))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      Problem520.strictMono_harperBlockEndpoint.tendsto_atTop
  have hsqrt : Tendsto
      (fun j : Nat ↦ Real.sqrt
        (Problem520.harperBlockEndpoint j : Real)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hend
  have hendEventually : ∀ᶠ j : Nat in atTop,
      1048576 * (n : Real) ^ (48 : Nat) ≤
        Real.sqrt (Problem520.harperBlockEndpoint j : Real) :=
    hsqrt.eventually_ge_atTop _
  obtain ⟨Jend, hJend⟩ := Filter.eventually_atTop.1 hendEventually
  let J := max Jcov Jend
  refine ⟨J, ?_⟩
  intro r j y hj hy t ht s hs hsep
  have hjCov : Jcov + (r + 1) ≤ j := by
    have : Jcov ≤ J := le_max_left _ _
    omega
  have hjEnd : Jend ≤ j := by
    have : Jend ≤ J := le_max_right _ _
    omega
  have hlarge := hJend j hjEnd
  have hN42 : (1 : Real) ≤ (n : Real) ^ (42 : Nat) :=
    one_le_pow₀ (by linarith)
  have hfrequencyToLarge :
      4 * (n : Real) ^ (6 : Nat) ≤
        1048576 * (n : Real) ^ (48 : Nat) := by
    calc
      4 * (n : Real) ^ (6 : Nat) ≤
          1048576 * (n : Real) ^ (6 : Nat) := by gcongr <;> norm_num
      _ = 1048576 * ((n : Real) ^ (6 : Nat) * 1) := by ring
      _ ≤ 1048576 * ((n : Real) ^ (6 : Nat) *
          (n : Real) ^ (42 : Nat)) := by gcongr
      _ = 1048576 * (n : Real) ^ (48 : Nat) := by ring
  refine ⟨hfrequencyToLarge.trans hlarge, hlarge, ?_⟩
  exact (hcov r j y hjCov hy t ht s hs hsep).le

#print axioms Erdos.Problem1144.harperTwoHeightCutoff_totalExpansion_le
#print axioms Erdos.Problem1144.harperTwoHeightCutoff_totalError_le
#print axioms Erdos.Problem1144.one_sub_eight_div_cube_le_harperTwoHeightCutoff_retention
#print axioms Erdos.Problem1144.exists_harperTwoHeightCorridorCutoffBlockHypotheses

#print axioms Erdos.Problem1144.harperScheduledTwoHeightCorridorRectangleMass_le_independentGaussian_cutoff

end

end Problem1144
end Erdos
