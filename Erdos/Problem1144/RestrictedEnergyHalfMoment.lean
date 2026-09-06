import Erdos.Problem1144.HarperPositiveProbabilityEnergy

open MeasureTheory
open scoped ENNReal

namespace Erdos
namespace Problem1144

/-!
# The restricted-energy lower-moment reduction

The lower half-moment input for the positive-probability route can be reduced
to Harper's restricted second-moment device.  If `R <= Z` has first moment
`m` and second moment `B`, Holder gives

`m^(3/2) / sqrt(B) <= E[sqrt Z]`.

Thus the remaining analytic construction only has to produce a restricted
energy whose first moment is of critical order and whose second moment is of
the square of that order.
-/

/-- The exact `q = 1/2` lower interpolation inequality used in Harper's
restricted-energy argument, together with the positivity of its second-
moment denominator. -/
theorem integral_sq_pos_and_rpow_half_lower_of_restricted_first_second
    {Omega : Type*} [MeasurableSpace Omega] {nu : Measure Omega}
    [IsProbabilityMeasure nu] {Z R : Omega -> Real}
    (hRnonneg : forall omega, 0 <= R omega)
    (hRle : forall omega, R omega <= Z omega)
    (hRint : Integrable R nu)
    (hRhalfInt : Integrable (fun omega => R omega ^ ((1 : Real) / 2)) nu)
    (hRsqInt : Integrable (fun omega => R omega ^ (2 : Nat)) nu)
    (hZhalfInt : Integrable (fun omega => Z omega ^ ((1 : Real) / 2)) nu)
    (hfirst : 0 < integral nu R) :
    0 < integral nu (fun omega => R omega ^ (2 : Nat)) ∧
      (integral nu R) ^ ((3 : Real) / 2) /
          Real.sqrt (integral nu (fun omega => R omega ^ (2 : Nat))) <=
        integral nu (fun omega => Z omega ^ ((1 : Real) / 2)) := by
  let f : Omega -> Real := fun omega => R omega ^ ((1 : Real) / 3)
  let g : Omega -> Real := fun omega => R omega ^ ((2 : Real) / 3)
  have hf_nonneg : 0 ≤ᵐ[nu] f :=
    Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (hRnonneg omega) _
  have hg_nonneg : 0 ≤ᵐ[nu] g :=
    Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (hRnonneg omega) _
  have hf : MemLp f (ENNReal.ofReal ((3 : Real) / 2)) nu := by
    have h := Problem520.memLp_rpow_of_integrable_rpow
      (ν := nu) (Z := R) (q := (1 : Real) / 3) (r := (1 : Real) / 2)
      (by norm_num) (by norm_num) hRint hRnonneg hRhalfInt
    norm_num at h ⊢
    exact h
  have hg : MemLp g (ENNReal.ofReal (3 : Real)) nu := by
    have hRsqRpow :
        Integrable (fun omega => R omega ^ (2 : Real)) nu := by
      convert hRsqInt using 1
      funext omega
      exact Real.rpow_natCast (R omega) 2
    have h := Problem520.memLp_rpow_of_integrable_rpow
      (ν := nu) (Z := R) (q := (2 : Real) / 3) (r := (2 : Real))
      (by norm_num) (by norm_num) hRint hRnonneg hRsqRpow
    norm_num at h ⊢
    exact h
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (p := (3 : Real) / 2) (q := (3 : Real)) (μ := nu)
    (Real.holderConjugate_iff.mpr (by norm_num))
    hf_nonneg hg_nonneg hf hg
  have hmul : (fun omega => f omega * g omega) = R := by
    funext omega
    simp only [f, g]
    rw [<- Real.rpow_add_of_nonneg (hRnonneg omega) (by norm_num) (by norm_num)]
    norm_num
  have hfpow :
      (integral nu (fun omega => f omega ^ ((3 : Real) / 2))) =
        integral nu (fun omega => R omega ^ ((1 : Real) / 2)) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun omega => by
      simp only [f]
      rw [<- Real.rpow_mul (hRnonneg omega)]
      norm_num
  have hgpow :
      (integral nu (fun omega => g omega ^ (3 : Real))) =
        integral nu (fun omega => R omega ^ (2 : Nat)) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun omega => by
      simp only [g]
      rw [<- Real.rpow_mul (hRnonneg omega)]
      norm_num
  rw [hmul, hfpow, hgpow] at hholder
  norm_num at hholder
  let A : Real := integral nu (fun omega => R omega ^ ((1 : Real) / 2))
  let B : Real := integral nu (fun omega => R omega ^ (2 : Nat))
  have hA : 0 <= A := integral_nonneg fun omega => Real.rpow_nonneg (hRnonneg omega) _
  have hB : 0 < B := by
    have hRleHolder : integral nu R <= A ^ ((2 : Real) / 3) * B ^ ((1 : Real) / 3) := by
      simpa only [A, B] using hholder
    have hprodPos : 0 < A ^ ((2 : Real) / 3) * B ^ ((1 : Real) / 3) :=
      hfirst.trans_le hRleHolder
    have hBnonneg : 0 <= B := integral_nonneg fun omega => sq_nonneg (R omega)
    by_contra hnot
    have hBzero : B = 0 := le_antisymm (le_of_not_gt hnot) hBnonneg
    rw [hBzero, Real.zero_rpow (by norm_num : (1 / 3 : Real) ≠ 0), mul_zero]
      at hprodPos
    exact (lt_irrefl 0) hprodPos
  have hpow := Real.rpow_le_rpow hfirst.le
    (show integral nu R <= A ^ ((2 : Real) / 3) * B ^ ((1 : Real) / 3) by
      simpa only [A, B] using hholder)
    (by norm_num : (0 : Real) <= 3 / 2)
  have hright :
      (A ^ ((2 : Real) / 3) * B ^ ((1 : Real) / 3)) ^ ((3 : Real) / 2) =
        A * Real.sqrt B := by
    rw [Real.mul_rpow (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB.le _),
      <- Real.rpow_mul hA, <- Real.rpow_mul hB.le, Real.sqrt_eq_rpow]
    norm_num
  rw [hright] at hpow
  have hrestricted :
      (integral nu R) ^ ((3 : Real) / 2) / Real.sqrt B <= A := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 hB)]
    simpa only [mul_comm] using hpow
  have hmono : A <= integral nu (fun omega => Z omega ^ ((1 : Real) / 2)) := by
    exact integral_mono hRhalfInt hZhalfInt fun omega =>
      Real.rpow_le_rpow (hRnonneg omega) (hRle omega) (by norm_num)
  exact ⟨hB, hrestricted.trans hmono⟩

/-- Inequality-only wrapper around
`integral_sq_pos_and_rpow_half_lower_of_restricted_first_second`. -/
theorem integral_rpow_half_lower_of_restricted_first_second
    {Omega : Type*} [MeasurableSpace Omega] {nu : Measure Omega}
    [IsProbabilityMeasure nu] {Z R : Omega -> Real}
    (hRnonneg : forall omega, 0 <= R omega)
    (hRle : forall omega, R omega <= Z omega)
    (hRint : Integrable R nu)
    (hRhalfInt : Integrable (fun omega => R omega ^ ((1 : Real) / 2)) nu)
    (hRsqInt : Integrable (fun omega => R omega ^ (2 : Nat)) nu)
    (hZhalfInt : Integrable (fun omega => Z omega ^ ((1 : Real) / 2)) nu)
    (hfirst : 0 < integral nu R) :
    (integral nu R) ^ ((3 : Real) / 2) /
        Real.sqrt (integral nu (fun omega => R omega ^ (2 : Nat))) <=
      integral nu (fun omega => Z omega ^ ((1 : Real) / 2)) :=
  (integral_sq_pos_and_rpow_half_lower_of_restricted_first_second
    hRnonneg hRle hRint hRhalfInt hRsqInt hZhalfInt hfirst).2

/-! ## The exact remaining Harper certificate -/

/-- A restricted energy at the critical scale, with first moment of order
`K` and second moment of order `K^2`.  This is the smallest concrete
analytic statement extracted from Harper's lower-moment proof. -/
def HarperRestrictedEnergyFirstSecondStatement : Prop :=
  ∃ c C : Real, 0 < c ∧ 0 < C ∧ ∃ Y : Nat, ∀ y : Nat,
    Y <= y -> 4 <= y ->
      ∃ R : Problem520.Omega -> Real,
        (∀ omega, 0 <= R omega) ∧
        (∀ omega, R omega <=
          Problem520.harperInitialNormalizedEnergy y omega) ∧
        Integrable R Problem520.μ ∧
        Integrable (fun omega => R omega ^ (2 : Nat)) Problem520.μ ∧
        c * harperInitialCriticalScale y <=
          integral Problem520.μ R ∧
        integral Problem520.μ (fun omega => R omega ^ (2 : Nat)) <=
          (C * harperInitialCriticalScale y) ^ (2 : Nat)

/-- The restricted first/second-moment certificate implies the sole new
half-moment statement needed by the positive-probability route. -/
theorem harperRademacherInitialHalfMomentLowerStatement_of_restrictedEnergy
    (hrestricted : HarperRestrictedEnergyFirstSecondStatement) :
    HarperRademacherInitialHalfMomentLowerStatement := by
  obtain ⟨c, C, hc, hC, Y, hcert⟩ := hrestricted
  let d : Real := c ^ ((3 : Real) / 2) / C
  have hd : 0 < d := div_pos (Real.rpow_pos_of_pos hc _) hC
  refine ⟨d, hd, Y, ?_⟩
  intro y hyY hy4
  obtain ⟨R, hRnonneg, hRle, hRint, hRsqInt, hmean, hsecond⟩ :=
    hcert y hyY hy4
  let Z : Problem520.Omega -> Real :=
    Problem520.harperInitialNormalizedEnergy y
  let K : Real := harperInitialCriticalScale y
  have hK : 0 < K := harperInitialCriticalScale_pos hy4
  have hy1 : 1 < y := by omega
  have hRhalfInt :
      Integrable (fun omega => R omega ^ ((1 : Real) / 2)) Problem520.μ :=
    Problem520.integrable_rpow_of_integrable_nonneg
      hRint hRnonneg (by norm_num) (by norm_num)
  have hZhalfInt :
      Integrable (fun omega => Z omega ^ ((1 : Real) / 2)) Problem520.μ := by
    simpa only [Z] using integrable_harperInitialNormalizedEnergy_half hy1
  have hbase :=
    integral_sq_pos_and_rpow_half_lower_of_restricted_first_second
      (nu := Problem520.μ) (Z := Z) (R := R)
      hRnonneg (by simpa only [Z] using hRle) hRint hRhalfInt hRsqInt
      hZhalfInt
      (mul_pos hc hK |>.trans_le (by simpa only [K] using hmean))
  let B : Real :=
    integral Problem520.μ (fun omega => R omega ^ (2 : Nat))
  have hD : 0 < C * K := mul_pos hC hK
  have hsqrt : Real.sqrt B <= C * K := by
    rw [Real.sqrt_le_iff]
    exact ⟨hD.le, by simpa only [B, K] using hsecond⟩
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
      (by simpa only [K] using hmean) (by norm_num)
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
  exact hratio.trans (by simpa only [B, Z, K, d] using hbase.2)

end Problem1144
end Erdos
