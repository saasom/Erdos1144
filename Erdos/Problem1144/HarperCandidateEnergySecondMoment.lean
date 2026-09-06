import Erdos.Problem1144.HarperCandidateEnergyNaturalShell
import Erdos.Problem1144.HarperCandidateEnergyTerminalIntegral
import Erdos.Problem1144.HarperLogBallotCertificate
import Erdos.Problem1144.HarperRankinTwoHeightLaw

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos.Problem1144

theorem candidate_integrable_rankinTwoHeightCubeMass_of_graph
    {y : Nat} {a : ℝ} {G : Set (Real × Problem520.Omega)}
    (hG : MeasurableSet G)
    (A : Real → Set (Problem520.HarperPrimeCube y))
    (hsection : ∀ t omega,
      (t, omega) ∈ G ↔ Problem520.harperPrimeRestriction y omega ∈ A t) :
    Integrable (fun ts : Real × Real ↦
        harperRankinTwoHeightCubeMass y a ts.1 ts.2 (A ts.1 ∩ A ts.2))
      ((volume.restrict harperLowerVerticalBand).prod
        (volume.restrict harperLowerVerticalBand)) := by
  let nu : Measure Real := volume.restrict harperLowerVerticalBand
  let F : Real × Problem520.Omega → Real := fun w ↦
    G.indicator
      (fun z : Real × Problem520.Omega ↦
        harperRankinEulerDensity y a z.2 z.1) w
  let H : (Real × Real) × Problem520.Omega → Real := fun w ↦
    F (w.1.1, w.2) * F (w.1.2, w.2)
  have hfinite : volume harperLowerVerticalBand ≠ ∞ := by
    simp [harperLowerVerticalBand, Real.volume_Icc]
  letI : IsFiniteMeasure nu := isFiniteMeasure_restrict.2 hfinite
  have hFmeas : Measurable F := by
    simpa only [F] using
      (measurable_harperRankinEulerDensity_joint y a).indicator hG
  have hHmeas : Measurable H := by
    apply Measurable.mul
    · exact hFmeas.comp (by fun_prop)
    · exact hFmeas.comp (by fun_prop)
  let U : Real := harperRankinEulerDensityUniformBound y a
  have hFbounds (w : Real × Problem520.Omega) :
      0 ≤ F w ∧ F w ≤ U := by
    by_cases hw : w ∈ G
    · simp only [F, Set.indicator_of_mem hw]
      exact ⟨harperRankinEulerDensity_nonneg y a w.2 w.1,
        harperRankinEulerDensity_le_uniformBound y a w.2 w.1⟩
    · simp [F, hw, U,
        harperRankinEulerDensityUniformBound_nonneg]
  have hH : Integrable H ((nu.prod nu).prod Problem520.μ) := by
    apply Integrable.of_bound hHmeas.aestronglyMeasurable (U ^ (2 : Nat))
    exact ae_of_all _ fun w ↦ by
      have hleft := hFbounds (w.1.1, w.2)
      have hright := hFbounds (w.1.2, w.2)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hleft.1 hright.1)]
      rw [pow_two]
      exact mul_le_mul hleft.2 hright.2 hright.1
        (harperRankinEulerDensityUniformBound_nonneg y a)
  have hinner (ts : Real × Real) :
      (∫ omega, H (ts, omega) ∂Problem520.μ) =
        harperRankinTwoHeightCubeMass y a ts.1 ts.2 (A ts.1 ∩ A ts.2) := by
    simpa only [H, F] using
      integral_graphIndicator_harperRankinEulerDensity_mul_eq_twoHeightCubeMass
        A hsection ts.1 ts.2
  have hint := hH.integral_prod_left
  have hmass : Integrable (fun ts : Real × Real ↦
      harperRankinTwoHeightCubeMass y a ts.1 ts.2 (A ts.1 ∩ A ts.2))
      (nu.prod nu) := hint.congr (ae_of_all (nu.prod nu) hinner)
  simpa only [nu] using hmass

/-- The actual shifted same-graph two-height integral.  Its start and
multiplicative constant are absolute; all Rankin dependence is the displayed
polynomial and a fixed terminal gap, absorbed by the path length. -/
theorem candidate_exists_rankinLogBallot_twoHeight_integral_le_polynomial :
    ∃ C > 0, ∃ J : Nat, ∀ V : ℝ, 0 ≤ V → ∃ gap₀ : Nat,
      ∀ start n gap y : Nat, J ≤ start → 0 < n → gap₀ ≤ gap →
        Problem520.harperBlockEndpoint (start + n + gap) ≤ y →
        y < Problem520.harperBlockEndpoint (start + n + gap + 1) →
        (1 + 4 * V) * Real.log 4 ≤ Real.log y →
        (4 : ℝ) ^ gap ≤ (n : ℝ) ^ 3 →
        ∀ ha : 0 ≤ 4 * V / Real.log (y : ℝ),
        (∫ ts, harperRankinTwoHeightCorrelation y (4 * V / Real.log y) ts.1 ts.2 *
          (harperRankinTwoHeightCubeLaw y (4 * V / Real.log y) ha ts.1 ts.2).real
            (harperRankinLogBallotCubeEvent y start n (4 * V / Real.log y) ts.1 ∩
              harperRankinLogBallotCubeEvent y start n (4 * V / Real.log y) ts.2)
          ∂(volume.restrict harperLowerVerticalBand).prod (volume.restrict harperLowerVerticalBand)) ≤
        C * (candidateRankinNormalizerRatioConstant * (1 + 4 * V)) ^ 72 *
          (4 : ℝ) ^ start * (n : ℝ)⁻¹ := by
  obtain ⟨Cn, hCn, Jn, hnatural⟩ := candidate_exists_rankinLogBallot_naturalShell_integral_le
  obtain ⟨Ct, hCt, Jt, hterminal⟩ := candidate_exists_rankinLogBallot_nearDiagonal_integral_le_polynomial
  obtain ⟨Cp, hCp, Jp, hpoint⟩ := candidate_exists_rankinLogBallot_terminal_correlation_probability_le
  refine ⟨Ct + 4 * Cn + 2 * Cp / 3, by positivity, max Jn (max Jt Jp), ?_⟩
  intro V hV
  obtain ⟨gap₀, hnatural⟩ := hnatural V hV
  refine ⟨gap₀, ?_⟩
  intro start n gap y hstart hn hgap hy hyupper hsize habs ha
  have hsN : Jn ≤ start := (le_max_left _ _).trans hstart
  have hsT : Jt ≤ start := (le_max_left Jt Jp).trans ((le_max_right _ _).trans hstart)
  have hsP : Jp ≤ start := (le_max_right Jt Jp).trans ((le_max_right _ _).trans hstart)
  let R : ℝ := (candidateRankinNormalizerRatioConstant * (1 + 4 * V)) ^ 72
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  let f : ℝ × ℝ → ℝ := fun ts => harperRankinTwoHeightCorrelation y (4 * V / Real.log y) ts.1 ts.2 *
          (harperRankinTwoHeightCubeLaw y (4 * V / Real.log y) ha ts.1 ts.2).real
            (harperRankinLogBallotCubeEvent y start n (4 * V / Real.log y) ts.1 ∩
              harperRankinLogBallotCubeEvent y start n (4 * V / Real.log y) ts.2)
  let μh := (volume.restrict harperLowerVerticalBand).prod (volume.restrict harperLowerVerticalBand)
  have hf : ∀ ts, 0 ≤ f ts := fun ts =>
    mul_nonneg (harperRankinTwoHeightCorrelation_pos y ha ts.1 ts.2).le measureReal_nonneg
  have hterminal' : (∫ ts in harperTerminalNearDiagonalStrip n, f ts ∂μh) ≤
      Ct * R * (4 : ℝ) ^ start * (n : ℝ)⁻¹ :=
    hterminal V hV start n gap y hsT hn hy hyupper hsize habs ha
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfrac : (4 : ℝ) ^ gap / (n : ℝ) ^ 4 ≤ (n : ℝ)⁻¹ := by
    calc
      _ ≤ (n : ℝ) ^ 3 / (n : ℝ) ^ 4 := div_le_div_of_nonneg_right habs (by positivity)
      _ = _ := by field_simp
  have hp (ts : ℝ × ℝ) (hb : ts ∈ harperLowerVerticalBand ×ˢ harperLowerVerticalBand) :
      f ts ≤ (Cp * R * (4 : ℝ) ^ start) * (2 : ℝ) ^ n * (n : ℝ)⁻¹ := by
    have h := hpoint V hV start n gap y hsP hn hy hyupper hsize ts.1 hb.1 ts.2 hb.2 ha
    calc
      _ ≤ Cp * R * (4 : ℝ) ^ (start + gap) * (2 : ℝ) ^ n / (n : ℝ) ^ 4 := h
      _ = (Cp * R * (4 : ℝ) ^ start * (2 : ℝ) ^ n) *
          ((4 : ℝ) ^ gap / (n : ℝ) ^ 4) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfrac (by positivity)
  have hlast : (∫ ts in harper1144OverlapShell (n - 1), f ts ∂μh) ≤
      (2 * Cp / 3) * R * (4 : ℝ) ^ start * (n : ℝ)⁻¹ := by
    have hi := integral_harper1144OverlapShell_le_of_bound (n - 1)
      ((Cp * R * (4 : ℝ) ^ start) * (2 : ℝ) ^ n * (n : ℝ)⁻¹)
      (by positivity) f hf (fun ts hb _ => hp ts hb)
    have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
      ring
    apply hi.trans_eq
    rw [hpow]
    have hne : (2 : ℝ) ^ (n - 1) ≠ 0 := by positivity
    field_simp
  have hnatSum : (∑ q ∈ Finset.range (n - 1), ∫ ts in harper1144OverlapShell q, f ts ∂μh) ≤
      4 * Cn * R * (4 : ℝ) ^ start * (n : ℝ)⁻¹ := by
    calc
      _ ≤ ∑ q ∈ Finset.range (n - 1),
          (Cn * R * (4 : ℝ) ^ start) * harper1144OverlapShellWeight n q := by
        apply Finset.sum_le_sum
        intro q hq
        exact hnatural start n q gap y hsN (by have := Finset.mem_range.mp hq; omega)
          hgap hy hyupper hsize ha
      _ = (Cn * R * (4 : ℝ) ^ start) *
          ∑ q ∈ Finset.range (n - 1), harper1144OverlapShellWeight n q := by rw [Finset.mul_sum]
      _ ≤ (Cn * R * (4 : ℝ) ^ start) *
          ∑ q ∈ Finset.range n, harper1144OverlapShellWeight n q := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        intro q _ _
        unfold harper1144OverlapShellWeight
        positivity
      _ ≤ (Cn * R * (4 : ℝ) ^ start) * (4 * (n : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (sum_harper1144OverlapShellWeight_le n hn) (by positivity)
      _ = _ := by ring
  have hsum : (∑ q ∈ Finset.range n, ∫ ts in harper1144OverlapShell q, f ts ∂μh) ≤
      (4 * Cn + 2 * Cp / 3) * R * (4 : ℝ) ^ start * (n : ℝ)⁻¹ := by
    have hsumEq : (∑ q ∈ Finset.range n, ∫ ts in harper1144OverlapShell q, f ts ∂μh) =
        (∑ q ∈ Finset.range (n - 1), ∫ ts in harper1144OverlapShell q, f ts ∂μh) +
          ∫ ts in harper1144OverlapShell (n - 1), f ts ∂μh := by
      simpa only [show n - 1 + 1 = n by omega] using
        Finset.sum_range_succ (fun q => ∫ ts in harper1144OverlapShell q, f ts ∂μh) (n - 1)
    rw [hsumEq]
    convert add_le_add hnatSum hlast using 1 <;> ring
  let A : ℝ → Set (Problem520.HarperPrimeCube y) :=
    fun t => harperRankinLogBallotCubeEvent y start n (4 * V / Real.log y) t
  let mass : ℝ × ℝ → ℝ := fun ts =>
    harperRankinTwoHeightCubeMass y (4 * V / Real.log y) ts.1 ts.2 (A ts.1 ∩ A ts.2)
  let E := harperRankinPrimeEnergyNormalizer y (4 * V / Real.log y)
  have hE : 0 < E := harperRankinPrimeEnergyNormalizer_pos y _
  have hmass : Integrable mass μh := candidate_integrable_rankinTwoHeightCubeMass_of_graph
    (measurableSet_harperRankinLogBallotGraph y start n _) A (fun _ _ => Iff.rfl)
  have heq (ts : ℝ × ℝ) : mass ts = E ^ 2 * f ts := by
    dsimp only [mass, E, f, A]
    rw [harperRankinTwoHeightCubeMass_eq_normalizer_mul_probability y _ ha,
      harperRankinTwoHeightNormalizer_eq_energy_sq_mul_correlation]
    ring
  have hfi : Integrable f μh := by
    apply (hmass.const_mul (E ^ 2)⁻¹).congr
    exact ae_of_all _ fun ts => by
      change (E ^ 2)⁻¹ * mass ts = f ts
      rw [heq]
      field_simp [hE.ne']
  have hcover := integral_le_terminal_add_overlapShells n f hfi hf
  apply hcover.trans
  convert add_le_add hterminal' hsum using 1 <;> dsimp only [R] <;> ring

/-- Polynomial second moment of the literal shifted restricted ballot graph.
No two-height probability estimate remains as a premise. -/
theorem candidate_exists_rankinLogBallotGraph_secondMoment_le_polynomial :
    ∃ C > 0, ∃ J : Nat, ∀ V : ℝ, 0 ≤ V → ∃ gap₀ : Nat,
      ∀ start n gap y : Nat, J ≤ start → 0 < n → gap₀ ≤ gap →
        Problem520.harperBlockEndpoint (start + n + gap) ≤ y →
        y < Problem520.harperBlockEndpoint (start + n + gap + 1) →
        (1 + 4 * V) * Real.log 4 ≤ Real.log y →
        (4 : ℝ) ^ gap ≤ (n : ℝ) ^ 3 →
        (∫ omega, harperRankinRestrictedGraphEnergy y (4 * V / Real.log y)
          (harperRankinLogBallotGraph y start n (4 * V / Real.log y)) omega ^ 2
          ∂Problem520.μ) ≤
        C * (candidateRankinNormalizerRatioConstant * (1 + 4 * V)) ^ 72 *
          (4 : ℝ) ^ start * (n : ℝ)⁻¹ := by
  obtain ⟨C₀, hC₀, J, hmain⟩ := candidate_exists_rankinLogBallot_twoHeight_integral_le_polynomial
  let K : ℝ := Real.exp (1 - Real.log (Real.log 2) + 2 * (Real.log 4 + 4) / Real.log 2)
  have hK : 0 < K := Real.exp_pos _
  refine ⟨(16 / 25 : ℝ) * K ^ 2 * C₀, by positivity, J, ?_⟩
  intro V hV
  obtain ⟨gap₀, hmain⟩ := hmain V hV
  refine ⟨gap₀, ?_⟩
  intro start n gap y hstart hn hgap hy hyupper hsize habs
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hlog : 0 < Real.log (y : ℝ) :=
    (mul_pos (by linarith : 0 < 1 + 4 * V) hlog4).trans_le hsize
  have hy2 : 2 ≤ y := by
    by_contra h
    have hyle : y ≤ 1 := by omega
    interval_cases y <;> norm_num at hlog
  let a := 4 * V / Real.log (y : ℝ)
  have ha : 0 ≤ a := div_nonneg (by positivity) hlog.le
  let G := harperRankinLogBallotGraph y start n a
  let A : ℝ → Set (Problem520.HarperPrimeCube y) :=
    fun t => harperRankinLogBallotCubeEvent y start n a t
  let E := harperRankinPrimeEnergyNormalizer y a
  let R := (candidateRankinNormalizerRatioConstant * (1 + 4 * V)) ^ 72
  let f : ℝ × ℝ → ℝ := fun ts =>
    harperRankinTwoHeightCorrelation y a ts.1 ts.2 *
      (harperRankinTwoHeightCubeLaw y a ha ts.1 ts.2).real (A ts.1 ∩ A ts.2)
  let μh := (volume.restrict harperLowerVerticalBand).prod (volume.restrict harperLowerVerticalBand)
  have hbound : (∫ ts, f ts ∂μh) ≤ C₀ * R * (4 : ℝ) ^ start * (n : ℝ)⁻¹ :=
    hmain start n gap y hstart hn hgap hy hyupper hsize habs ha
  have hnormal : E ≤ K * Real.log (y : ℝ) := by
    apply (candidate_rankinNormalizer_antitone_shift y ha).trans
    have heq : harperRankinPrimeEnergyNormalizer y 0 = Problem520.primeEnergyNormalizer y := by
      unfold harperRankinPrimeEnergyNormalizer Problem520.primeEnergyNormalizer
      apply Finset.prod_congr rfl
      intro p hp
      exact harperRankinEulerNormalizer_zero (Nat.prime_of_mem_primesBelow hp).pos
    rw [heq]
    exact Problem520.primeEnergyNormalizer_le_mertensConstant_mul_log hy2
  have hE : 0 < E := harperRankinPrimeEnergyNormalizer_pos y a
  have hnormsq : E ^ 2 ≤ (K * Real.log (y : ℝ)) ^ 2 := by gcongr
  have hmass : (∫ ts, harperRankinTwoHeightCubeMass y a ts.1 ts.2 (A ts.1 ∩ A ts.2) ∂μh) =
      E ^ 2 * ∫ ts, f ts ∂μh := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun ts => by
      dsimp only [f, E]
      rw [harperRankinTwoHeightCubeMass_eq_normalizer_mul_probability y a ha,
        harperRankinTwoHeightNormalizer_eq_energy_sq_mul_correlation]
      ring
  have hsq := integral_sq_harperRankinRestrictedGraphEnergy_eq_twoHeightCubeMass (a := a)
    (measurableSet_harperRankinLogBallotGraph y start n a) A (fun _ _ => Iff.rfl)
  change (∫ omega, harperRankinRestrictedGraphEnergy y a G omega ^ 2 ∂Problem520.μ) ≤ _
  rw [hsq, hmass]
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  calc
    (16 / 25 : ℝ) * (E ^ 2 * ∫ ts, f ts ∂μh) / Real.log (y : ℝ) ^ 2 ≤
        (16 / 25 : ℝ) * (E ^ 2 * (C₀ * R * (4 : ℝ) ^ start * (n : ℝ)⁻¹)) /
          Real.log (y : ℝ) ^ 2 := by gcongr
    _ ≤ (16 / 25 : ℝ) * ((K * Real.log (y : ℝ)) ^ 2 *
        (C₀ * R * (4 : ℝ) ^ start * (n : ℝ)⁻¹)) / Real.log (y : ℝ) ^ 2 := by gcongr
    _ = _ := by dsimp only [R]; field_simp

end Erdos.Problem1144
