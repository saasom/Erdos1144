import Erdos.Problem1144.HarperCandidateEnergyGraphMoments
import Erdos.Problem1144.RestrictedEnergyHalfMoment
import Erdos.Problem1144.HarperCandidateEnergyBallotUniform
import Erdos.Problem1144.HarperCandidateEnergySecondMoment
import Erdos.Problem1144.HarperCandidateEnergyGapSchedule

open MeasureTheory Set Filter
open scoped Topology
namespace Erdos.Problem1144

private theorem graph_halfMoment_lower
    {y : ℕ} (hy : 1 < y) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {G : Set (ℝ × Problem520.Omega)} (hG : MeasurableSet G)
    {c C K : ℝ} (hc : 0 < c) (hC : 0 < C) (hK : 0 < K)
    (hmean : c * K ≤ ∫ omega, harperRankinRestrictedGraphEnergy y a G omega ∂Problem520.μ)
    (hsecond : (∫ omega, harperRankinRestrictedGraphEnergy y a G omega ^ (2 : ℕ) ∂Problem520.μ)
      ≤ (C * K) ^ (2 : ℕ)) :
    (c ^ ((3 : ℝ) / 2) / C) * K ^ ((1 : ℝ) / 2) ≤
      ∫ omega, harperSquarefreeShiftedNormalizedEnergy y a omega ^ ((1 : ℝ) / 2) ∂Problem520.μ := by
  let R := harperRankinRestrictedGraphEnergy y a G
  let Z := harperSquarefreeShiftedNormalizedEnergy y a
  let d : ℝ := c ^ ((3 : ℝ) / 2) / C
  have hd : 0 < d := div_pos (Real.rpow_pos_of_pos hc _) hC
  have hRnonneg : ∀ omega, 0 ≤ R omega := harperRankinRestrictedGraphEnergy_nonneg hy a G
  have hRle : ∀ omega, R omega ≤ Z omega :=
    harperRankinRestrictedGraphEnergy_le_shiftedNormalized hy ha ha1 hG
  have hRint := integrable_harperRankinRestrictedGraphEnergy (y := y) a hG
  have hRsqInt := candidate_integrable_sq_rankinRestrictedGraphEnergy hy a hG
  have hRhalfInt :
      Integrable (fun omega => R omega ^ ((1 : Real) / 2)) Problem520.μ :=
    Problem520.integrable_rpow_of_integrable_nonneg
      hRint hRnonneg (by norm_num) (by norm_num)
  have hZhalfInt := integrable_harperSquarefreeShiftedNormalizedEnergy_half a hy ha
  have hbase :=
    integral_sq_pos_and_rpow_half_lower_of_restricted_first_second
      (nu := Problem520.μ) (Z := Z) (R := R)
      hRnonneg hRle hRint hRhalfInt hRsqInt
      hZhalfInt
      (mul_pos hc hK |>.trans_le hmean)
  let B : Real :=
    integral Problem520.μ (fun omega => R omega ^ (2 : Nat))
  have hD : 0 < C * K := mul_pos hC hK
  have hsqrt : Real.sqrt B <= C * K := by
    rw [Real.sqrt_le_iff]
    exact ⟨hD.le, by simpa only [B] using hsecond⟩
  have hcoeff : 0 <= d * K ^ ((1 : Real) / 2) :=
    mul_nonneg hd.le (Real.rpow_nonneg hK.le _)
  have hscale :
      (d * K ^ ((1 : Real) / 2)) * (C * K) =
        (c * K) ^ ((3 : Real) / 2) := by
    calc
      (d * K ^ ((1 : Real) / 2)) * (C * K) =
          c ^ ((3 : Real) / 2) *
            (K ^ ((1 : Real) / 2) * K) := by
        dsimp only [d]
        field_simp [hC.ne']
      _ = c ^ ((3 : Real) / 2) * K ^ ((3 : Real) / 2) := by
        congr 1
        calc
          K ^ ((1 : Real) / 2) * K =
              K ^ ((1 : Real) / 2) * K ^ (1 : Real) := by rw [Real.rpow_one]
          _ = K ^ ((1 : Real) / 2 + 1) :=
            (Real.rpow_add_of_nonneg hK.le (by norm_num) (by norm_num)).symm
          _ = K ^ ((3 : Real) / 2) := by norm_num
      _ = (c * K) ^ ((3 : Real) / 2) := by
        rw [Real.mul_rpow hc.le hK.le]
  have hnum :
      (c * K) ^ ((3 : Real) / 2) <=
        (integral Problem520.μ R) ^ ((3 : Real) / 2) := by
    exact Real.rpow_le_rpow (mul_nonneg hc.le hK.le)
      hmean (by norm_num)
  have hratio :
      d * K ^ ((1 : Real) / 2) <=
        (integral Problem520.μ R) ^ ((3 : Real) / 2) /
          Real.sqrt B := by
    rw [le_div_iff₀ (Real.sqrt_pos.2 (by simpa only [B] using hbase.1))]
    calc
      (d * K ^ ((1 : Real) / 2)) * Real.sqrt B <=
          (d * K ^ ((1 : Real) / 2)) * (C * K) :=
        mul_le_mul_of_nonneg_left hsqrt hcoeff
      _ = (c * K) ^ ((3 : Real) / 2) := hscale
      _ <= (integral Problem520.μ R) ^ ((3 : Real) / 2) := hnum
  exact hratio.trans (by simpa only [B, Z, d] using hbase.2)

private theorem polynomial_half_coefficient
    {b D L : ℝ} (hb : 0 < b) (hD : 0 < D) (hL : 1 ≤ L) :
    (b ^ ((3 : ℝ) / 2) / D) / L ^ (38 : ℕ) ≤
      (b / L) ^ ((3 : ℝ) / 2) / (D * L ^ (36 : ℕ)) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hpow : L ^ ((3 : ℝ) / 2) ≤ L ^ (2 : ℕ) := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (3 : ℝ) / 2 ≤ (2 : ℝ))
  rw [Real.div_rpow hb.le hL0.le]
  have h := div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hb ((3 : ℝ) / 2)).le
    (Real.rpow_pos_of_pos hL0 ((3 : ℝ) / 2)) hpow
  calc
    _ = (b ^ ((3 : ℝ) / 2) / L ^ (2 : ℕ)) / (D * L ^ (36 : ℕ)) := by
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right h (mul_nonneg hD.le (pow_nonneg hL0.le _))

private theorem exists_exp_rankin_polynomial_absorption
    {d M : ℝ} (hd : 0 < d) (hM : 0 < M) :
    ∃ V : ℝ, 0 ≤ V ∧ Real.exp (-V) * M ≤ (d / (1 + 4 * V) ^ (38 : ℕ)) / 2 := by
  have hdecay : Tendsto (fun V : ℝ => (1 + 4 * V) ^ (38 : ℕ) * Real.exp (-V))
      atTop (nhds 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 38).comp
      (tendsto_atTop_add_const_left atTop (1 / 4 : ℝ) tendsto_id)
    have hscaled := h.const_mul ((4 : ℝ) ^ (38 : ℕ) * Real.exp (1 / 4))
    simp only [mul_zero, Function.comp_def, id_eq] at hscaled
    convert hscaled using 1
    funext V
    have hexp : Real.exp (1 / 4 : ℝ) * Real.exp (-(1 / 4 + V)) = Real.exp (-V) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hbase : (1 + 4 * V) = 4 * (1 / 4 + V) := by ring
    rw [hbase, mul_pow, ← hexp]
    ring
  have hev := hdecay.eventually (gt_mem_nhds (div_pos hd (mul_pos (by norm_num : (0 : ℝ) < 2) hM)))
  obtain ⟨V, hV, hsmall⟩ := ((eventually_ge_atTop (0 : ℝ)).and hev).exists
  refine ⟨V, hV, ?_⟩
  have hL : 0 < (1 + 4 * V) ^ (38 : ℕ) := pow_pos (by linarith) _
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_div_iff₀ hL]
  have hsmall' := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hM)).mp hsmall
  nlinarith

/-- The actual shifted smooth energy has a lower half moment with polynomial
Rankin loss. The degree 38 comes from the correlation-ratio degree 72,
followed by square-root interpolation and rounding 3/2 upward to 2. -/
theorem candidate_exists_rankinShiftedHalfMoment_polynomial :
    ∃ d > 0, ∀ V : ℝ, 0 ≤ V → ∃ Y : ℕ,
      HarperRankinShiftedHalfMomentLowerBound V (d / (1 + 4 * V) ^ (38 : ℕ)) Y := by
  obtain ⟨Jone, hone⟩ := candidate_exists_uniform_start_rankinLogBallotGraph_firstMoment
  obtain ⟨C, hC, Jtwo, htwo⟩ := candidate_exists_rankinLogBallotGraph_secondMoment_le_polynomial
  let start := max Jone Jtwo
  let b := candidateRankinNormalizerConstant * candidateRankinBallotConstant / 15
  let D := Real.sqrt (3 * C * (4 : ℝ) ^ start) * candidateRankinNormalizerRatioConstant ^ 36
  let d := b ^ ((3 : ℝ) / 2) / D
  have hb : 0 < b := div_pos
    (mul_pos candidateRankinNormalizerConstant_pos candidateRankinBallotConstant_pos) (by norm_num)
  have hD : 0 < D := mul_pos (Real.sqrt_pos.mpr (by positivity))
    (pow_pos candidateRankinNormalizerRatioConstant_pos _)
  have hd : 0 < d := div_pos (Real.rpow_pos_of_pos hb _) hD
  refine ⟨d, hd, ?_⟩
  intro V hV
  obtain ⟨gapOne, hone⟩ := hone V hV
  obtain ⟨gapTwo, htwo⟩ := htwo V hV
  let gap := max gapOne gapTwo
  have hevent : ∀ᶠ y : ℕ in atTop,
      (d / (1 + 4 * V) ^ (38 : ℕ)) * harperInitialCriticalScale y ^ ((1 : ℝ) / 2) ≤
        ∫ omega, harperSquarefreeShiftedNormalizedEnergy y (4 * V / Real.log y) omega ^
          ((1 : ℝ) / 2) ∂Problem520.μ := by
    filter_upwards [candidate_eventually_energyGapSchedule_geometry start gap V hV] with y hy
    dsimp only at hy
    rcases hy with ⟨hy4, hn, hlow, hupp, habs, hsize, ha, ha1, hscale⟩
    let n := Problem520.harperEconomicalPathLength y (start + gap) 0
    let a := 4 * V / Real.log (y : ℝ)
    let G := harperRankinLogBallotGraph y start n a
    let K := harperInitialCriticalScale y
    let L := 1 + 4 * V
    have hL : 1 ≤ L := by dsimp only [L]; linarith
    have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
    have hK : 0 < K := harperInitialCriticalScale_pos hy4
    have hG : MeasurableSet G := measurableSet_harperRankinLogBallotGraph y start n a
    have hyOne : Problem520.harperBlockEndpoint (start + n + gapOne) ≤ y :=
      (Problem520.monotone_harperBlockEndpoint
        (Nat.add_le_add_left (show gapOne ≤ gap from le_max_left _ _) (start + n))).trans hlow
    have hfirst : (b / L) * K ≤
        ∫ omega, harperRankinRestrictedGraphEnergy y a G omega ∂Problem520.μ := by
      have h := hone start n y (le_max_left _ _) hn hy4 hyOne hsize
      convert h using 1 <;> dsimp only [b, L, K, a, G] <;> field_simp
    have hsecond := htwo start n gap y (le_max_right _ _) hn (le_max_right _ _)
      hlow hupp hsize habs
    have hDsq : D ^ 2 = 3 * C * (4 : ℝ) ^ start * candidateRankinNormalizerRatioConstant ^ 72 := by
      dsimp only [D]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have hupper : (∫ omega, harperRankinRestrictedGraphEnergy y a G omega ^ (2 : ℕ)
        ∂Problem520.μ) ≤ ((D * L ^ (36 : ℕ)) * K) ^ (2 : ℕ) := by
      calc
        _ ≤ C * (candidateRankinNormalizerRatioConstant * L) ^ 72 *
            (4 : ℝ) ^ start * (n : ℝ)⁻¹ := hsecond
        _ ≤ C * (candidateRankinNormalizerRatioConstant * L) ^ 72 *
            (4 : ℝ) ^ start * (3 * K ^ 2) := by
          apply mul_le_mul_of_nonneg_left (by simpa only [one_div] using hscale)
          exact mul_nonneg (mul_nonneg hC.le (pow_nonneg
            (mul_nonneg candidateRankinNormalizerRatioConstant_pos.le hLpos.le) _)) (by positivity)
        _ = _ := by rw [mul_pow, mul_pow, mul_pow, hDsq]; ring
    have hbase := graph_halfMoment_lower (by omega : 1 < y) ha ha1 hG
      (div_pos hb hLpos) (mul_pos hD (pow_pos hLpos _)) hK hfirst hupper
    have hpoly := polynomial_half_coefficient hb hD hL
    exact (mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hK.le _)).trans hbase
  obtain ⟨Y, hY⟩ := eventually_atTop.1 hevent
  exact ⟨Y, fun y hy _ => hY y hy⟩

/-- The exponential Rankin tail is absorbed by the proved polynomial lower
half moment. This discharges the shifted-moment certificate outright. -/
theorem candidate_rankinShiftedHalfMomentLowerStatement_unconditional :
    HarperRankinShiftedHalfMomentLowerStatement := by
  obtain ⟨d, hd, hlower⟩ := candidate_exists_rankinShiftedHalfMoment_polynomial
  intro C hC
  obtain ⟨V, hV, habs⟩ := exists_exp_rankin_polynomial_absorption hd
    (Real.rpow_pos_of_pos hC ((3 : ℝ) / 4))
  obtain ⟨Y, hY⟩ := hlower V hV
  refine ⟨V, d / (1 + 4 * V) ^ (38 : ℕ), hV,
    div_pos hd (pow_pos (by linarith) _), habs, Y, hY⟩

/-- The original coefficient-prefix lower half moment follows from the
actual shifted ballot graph and the previously proved localization. -/
theorem candidate_squarefreeCoefficientHalfMomentLowerStatement_unconditional :
    HarperSquarefreeCoefficientHalfMomentLowerStatement :=
  harperSquarefreeCoefficientHalfMomentLowerStatement_of_rankinShifted
    candidate_rankinShiftedHalfMomentLowerStatement_unconditional

/-- The literal coefficient-prefix energy exceeds a fixed multiple of its
critical scale with a fixed positive probability, at every sufficiently
large cutoff. No analytic certificate is assumed. -/
theorem candidate_exists_squarefreeCoefficientCriticalEnergy_fixedProbability :
    ∃ delta : ℝ, 0 < delta ∧ ∃ c : ℝ, 0 < c ∧ ∃ Y : ℕ, ∀ y : ℕ,
      Y ≤ y → delta ≤ Problem520.μ.real
        (halfMomentLargeEvent (harperSquarefreeCoefficientNormalizedEnergy y)
          (c * harperInitialCriticalScale y ^ ((1 : ℝ) / 2))) :=
  exists_harperSquarefreeCoefficientCriticalEnergy_fixedProbability_of_rankinShifted
    candidate_rankinShiftedHalfMomentLowerStatement_unconditional

end Erdos.Problem1144
