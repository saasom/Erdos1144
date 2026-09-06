import Erdos.Problem520.HarperFractionalRecursion

open MeasureTheory Set
open scoped ENNReal

namespace Erdos
namespace Problem1144

/-!
# A two-moment positive-probability lemma

Harper's positive-probability energy argument compares a sharp `q = 1/2`
moment with any sharp larger fractional moment.  This file isolates the
measure-theoretic implication.  In particular, the already formalized
`q = 2/3` upper bound from Problem 520 can be used directly; a new `q = 3/4`
upper-moment formalization is unnecessary.
-/

/-- The energy is large when its square root is at least half of the supplied
lower bound for the square-root moment. -/
def halfMomentLargeEvent {Omega : Type*} (Z : Omega → ℝ) (a : ℝ) :
    Set Omega :=
  {omega | a / 2 ≤ Z omega ^ ((1 : ℝ) / 2)}

/-- The exact Holder comparison behind the positive-probability shortcut,
at an arbitrary larger exponent `r > 1/2`. -/
theorem halfMoment_le_half_add_largeEventHolder_of_largerMoment
    {Omega : Type*} [MeasurableSpace Omega] {nu : Measure Omega}
    [IsProbabilityMeasure nu] {Z : Omega → ℝ} {a b r : ℝ}
    (hlarge : MeasurableSet (halfMomentLargeEvent Z a))
    (hZnonneg : ∀ omega, 0 ≤ Z omega)
    (hhalfInt : Integrable (fun omega ↦ Z omega ^ ((1 : ℝ) / 2)) nu)
    (hhalfLp : MemLp (fun omega ↦ Z omega ^ ((1 : ℝ) / 2))
      (ENNReal.ofReal (r / ((1 : ℝ) / 2))) nu)
    (hr : (1 : ℝ) / 2 < r)
    (ha : 0 ≤ a)
    (hhalf : a ≤ ∫ omega, Z omega ^ ((1 : ℝ) / 2) ∂nu)
    (hlarger : (∫ omega, Z omega ^ r ∂nu) ≤ b) :
    a / 2 ≤
      (nu.real (halfMomentLargeEvent Z a)) ^
          (1 - ((1 : ℝ) / 2) / r) *
        b ^ (((1 : ℝ) / 2) / r) := by
  let G : Set Omega := halfMomentLargeEvent Z a
  let W : Omega → ℝ := fun omega ↦ Z omega ^ ((1 : ℝ) / 2)
  have hWnonneg : ∀ omega, 0 ≤ W omega :=
    fun omega ↦ Real.rpow_nonneg (hZnonneg omega) _
  have hsplit :
      ∫ omega, W omega ∂nu =
        (∫ omega in G, W omega ∂nu) +
          ∫ omega in Gᶜ, W omega ∂nu := by
    have hmeasure : nu.restrict G + nu.restrict Gᶜ = nu :=
      Measure.restrict_add_restrict_compl hlarge
    calc
      ∫ omega, W omega ∂nu =
          ∫ omega, W omega ∂(nu.restrict G + nu.restrict Gᶜ) := by
            rw [hmeasure]
      _ = (∫ omega in G, W omega ∂nu) +
          ∫ omega in Gᶜ, W omega ∂nu :=
        integral_add_measure hhalfInt.integrableOn hhalfInt.integrableOn
  have hcomplPoint : ∀ omega ∈ Gᶜ, W omega ≤ a / 2 := by
    intro omega homega
    have hnot : ¬ a / 2 ≤ W omega := by
      simpa only [G, W, halfMomentLargeEvent, Set.mem_compl_iff,
        Set.mem_setOf_eq] using homega
    exact (lt_of_not_ge hnot).le
  have hcompl : (∫ omega in Gᶜ, W omega ∂nu) ≤ a / 2 := by
    calc
      (∫ omega in Gᶜ, W omega ∂nu) ≤
          ∫ _omega in Gᶜ, a / 2 ∂nu := by
        exact setIntegral_mono_on hhalfInt.integrableOn
          (integrableOn_const (measure_ne_top nu Gᶜ)) hlarge.compl hcomplPoint
      _ = nu.real Gᶜ * (a / 2) := by simp
      _ ≤ 1 * (a / 2) := by
        exact mul_le_mul_of_nonneg_right
          (show nu.real Gᶜ ≤ 1 from measureReal_le_one)
          (div_nonneg ha (by norm_num))
      _ = a / 2 := one_mul _
  have hholder :=
    Erdos.Problem520.integralOn_rpow_le_measure_rpow_mul_integral_rpow
      (nu := nu) (Z := Z) (G := G)
      hlarge (q := (1 : ℝ) / 2) (r := r)
      (by norm_num) hr hZnonneg hhalfLp
  have hlargerNonneg : 0 ≤ ∫ omega, Z omega ^ r ∂nu :=
    integral_nonneg fun omega ↦ Real.rpow_nonneg (hZnonneg omega) _
  have hb : 0 ≤ b := hlargerNonneg.trans hlarger
  have hgood :
      (∫ omega in G, W omega ∂nu) ≤
        (nu.real G) ^ (1 - ((1 : ℝ) / 2) / r) *
          b ^ (((1 : ℝ) / 2) / r) := by
    have hmomentPow :
        (∫ omega, Z omega ^ r ∂nu) ^ (((1 : ℝ) / 2) / r) ≤
          b ^ (((1 : ℝ) / 2) / r) := by
      exact Real.rpow_le_rpow hlargerNonneg hlarger
        (div_nonneg (by norm_num) (by linarith [hr]))
    calc
      (∫ omega in G, W omega ∂nu) ≤
          (nu.real G) ^ (1 - ((1 : ℝ) / 2) / r) *
            (∫ omega, Z omega ^ r ∂nu) ^
              (((1 : ℝ) / 2) / r) := by
        simpa only [W] using hholder
      _ ≤ (nu.real G) ^ (1 - ((1 : ℝ) / 2) / r) *
          b ^ (((1 : ℝ) / 2) / r) :=
        mul_le_mul_of_nonneg_left hmomentPow
          (Real.rpow_nonneg (show 0 ≤ nu.real G from measureReal_nonneg) _)
  have htotal :
      a ≤ (nu.real G) ^ (1 - ((1 : ℝ) / 2) / r) *
          b ^ (((1 : ℝ) / 2) / r) + a / 2 := by
    calc
      a ≤ ∫ omega, W omega ∂nu := hhalf
      _ = (∫ omega in G, W omega ∂nu) +
          ∫ omega in Gᶜ, W omega ∂nu := hsplit
      _ ≤ (nu.real G) ^ (1 - ((1 : ℝ) / 2) / r) *
          b ^ (((1 : ℝ) / 2) / r) + a / 2 := add_le_add hgood hcompl
  change a / 2 ≤
    (nu.real G) ^ (1 - ((1 : ℝ) / 2) / r) *
      b ^ (((1 : ℝ) / 2) / r)
  linarith

/-- Concrete `1/2` versus `3/4` form traditionally quoted in Harper's
positive-probability argument. -/
theorem halfMoment_le_half_add_largeEventHolder
    {Omega : Type*} [MeasurableSpace Omega] {nu : Measure Omega}
    [IsProbabilityMeasure nu] {Z : Omega → ℝ} {a b : ℝ}
    (hlarge : MeasurableSet (halfMomentLargeEvent Z a))
    (hZnonneg : ∀ omega, 0 ≤ Z omega)
    (hhalfInt : Integrable (fun omega ↦ Z omega ^ ((1 : ℝ) / 2)) nu)
    (hhalfLp : MemLp (fun omega ↦ Z omega ^ ((1 : ℝ) / 2))
      (ENNReal.ofReal ((3 : ℝ) / 2)) nu)
    (ha : 0 ≤ a)
    (hhalf : a ≤ ∫ omega, Z omega ^ ((1 : ℝ) / 2) ∂nu)
    (hthreeQuarter :
      (∫ omega, Z omega ^ ((3 : ℝ) / 4) ∂nu) ≤ b) :
    a / 2 ≤
      (nu.real (halfMomentLargeEvent Z a)) ^ ((1 : ℝ) / 3) *
        b ^ ((2 : ℝ) / 3) := by
  have h := halfMoment_le_half_add_largeEventHolder_of_largerMoment
    (r := (3 : ℝ) / 4) hlarge hZnonneg hhalfInt
    (by norm_num; exact hhalfLp) (by norm_num) ha hhalf hthreeQuarter
  norm_num at h ⊢
  exact h

/-- The economical `1/2` versus `2/3` form.  This is the useful endpoint for
Problem 1144 because Problem 520 already proves the sharp `2/3` upper moment. -/
theorem halfMoment_le_half_add_largeEventHolder_twoThird
    {Omega : Type*} [MeasurableSpace Omega] {nu : Measure Omega}
    [IsProbabilityMeasure nu] {Z : Omega → ℝ} {a b : ℝ}
    (hlarge : MeasurableSet (halfMomentLargeEvent Z a))
    (hZnonneg : ∀ omega, 0 ≤ Z omega)
    (hhalfInt : Integrable (fun omega ↦ Z omega ^ ((1 : ℝ) / 2)) nu)
    (hhalfLp : MemLp (fun omega ↦ Z omega ^ ((1 : ℝ) / 2))
      (ENNReal.ofReal ((4 : ℝ) / 3)) nu)
    (ha : 0 ≤ a)
    (hhalf : a ≤ ∫ omega, Z omega ^ ((1 : ℝ) / 2) ∂nu)
    (htwoThird :
      (∫ omega, Z omega ^ ((2 : ℝ) / 3) ∂nu) ≤ b) :
    a / 2 ≤
      (nu.real (halfMomentLargeEvent Z a)) ^ ((1 : ℝ) / 4) *
        b ^ ((3 : ℝ) / 4) := by
  have h := halfMoment_le_half_add_largeEventHolder_of_largerMoment
    (r := (2 : ℝ) / 3) hlarge hZnonneg hhalfInt
    (by norm_num; exact hhalfLp) (by norm_num) ha hhalf htwoThird
  norm_num at h ⊢
  exact h

/-- Explicit probability lower bound using the already available `2/3`
moment. -/
theorem rpow_four_halfMoment_twoThird_ratio_le_measureReal_largeEvent
    {Omega : Type*} [MeasurableSpace Omega] {nu : Measure Omega}
    [IsProbabilityMeasure nu] {Z : Omega → ℝ} {a b : ℝ}
    (hlarge : MeasurableSet (halfMomentLargeEvent Z a))
    (hZnonneg : ∀ omega, 0 ≤ Z omega)
    (hhalfInt : Integrable (fun omega ↦ Z omega ^ ((1 : ℝ) / 2)) nu)
    (hhalfLp : MemLp (fun omega ↦ Z omega ^ ((1 : ℝ) / 2))
      (ENNReal.ofReal ((4 : ℝ) / 3)) nu)
    (ha : 0 < a) (hb : 0 < b)
    (hhalf : a ≤ ∫ omega, Z omega ^ ((1 : ℝ) / 2) ∂nu)
    (htwoThird :
      (∫ omega, Z omega ^ ((2 : ℝ) / 3) ∂nu) ≤ b) :
    ((a / 2) / b ^ ((3 : ℝ) / 4)) ^ (4 : ℝ) ≤
      nu.real (halfMomentLargeEvent Z a) := by
  have hroot := halfMoment_le_half_add_largeEventHolder_twoThird
    hlarge hZnonneg hhalfInt hhalfLp ha.le hhalf htwoThird
  have hbpow : 0 < b ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hb _
  have hdiv :
      (a / 2) / b ^ ((3 : ℝ) / 4) ≤
        (nu.real (halfMomentLargeEvent Z a)) ^ ((1 : ℝ) / 4) := by
    exact (div_le_iff₀ hbpow).2 (by simpa [mul_comm] using hroot)
  have hpow := Real.rpow_le_rpow
    (div_nonneg (div_nonneg ha.le (by norm_num)) hbpow.le) hdiv
    (by norm_num : (0 : ℝ) ≤ 4)
  calc
    ((a / 2) / b ^ ((3 : ℝ) / 4)) ^ (4 : ℝ) ≤
        ((nu.real (halfMomentLargeEvent Z a)) ^ ((1 : ℝ) / 4)) ^
          (4 : ℝ) := hpow
    _ = nu.real (halfMomentLargeEvent Z a) := by
      rw [← Real.rpow_mul measureReal_nonneg]
      norm_num

/-- At the critical scale, a sharp lower `1/2` moment and the existing sharp
upper `2/3` moment leave a fixed probability constant independent of `K`. -/
theorem criticalScale_halfMoment_twoThird_probability_lower
    {Omega : Type*} [MeasurableSpace Omega] {nu : Measure Omega}
    [IsProbabilityMeasure nu] {Z : Omega → ℝ} {c C K : ℝ}
    (hlarge : MeasurableSet
      (halfMomentLargeEvent Z (c * K ^ ((1 : ℝ) / 2))))
    (hZnonneg : ∀ omega, 0 ≤ Z omega)
    (hhalfInt : Integrable (fun omega ↦ Z omega ^ ((1 : ℝ) / 2)) nu)
    (hhalfLp : MemLp (fun omega ↦ Z omega ^ ((1 : ℝ) / 2))
      (ENNReal.ofReal ((4 : ℝ) / 3)) nu)
    (hc : 0 < c) (hC : 0 < C) (hK : 0 < K)
    (hhalf :
      c * K ^ ((1 : ℝ) / 2) ≤
        ∫ omega, Z omega ^ ((1 : ℝ) / 2) ∂nu)
    (htwoThird :
      (∫ omega, Z omega ^ ((2 : ℝ) / 3) ∂nu) ≤
        C * K ^ ((2 : ℝ) / 3)) :
    (c / (2 * C ^ ((3 : ℝ) / 4))) ^ (4 : ℝ) ≤
      nu.real (halfMomentLargeEvent Z (c * K ^ ((1 : ℝ) / 2))) := by
  have ha : 0 < c * K ^ ((1 : ℝ) / 2) :=
    mul_pos hc (Real.rpow_pos_of_pos hK _)
  have hb : 0 < C * K ^ ((2 : ℝ) / 3) :=
    mul_pos hC (Real.rpow_pos_of_pos hK _)
  have hraw := rpow_four_halfMoment_twoThird_ratio_le_measureReal_largeEvent
    hlarge hZnonneg hhalfInt hhalfLp ha hb hhalf htwoThird
  have hKhalf : 0 < K ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hK _
  have hden :
      (C * K ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 4) =
        C ^ ((3 : ℝ) / 4) * K ^ ((1 : ℝ) / 2) := by
    rw [Real.mul_rpow hC.le (Real.rpow_nonneg hK.le _),
      ← Real.rpow_mul hK.le]
    congr 2
    norm_num
  have hCpow : 0 < C ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hC _
  have hratio :
      (c * K ^ ((1 : ℝ) / 2) / 2) /
          (C * K ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 4) =
        c / (2 * C ^ ((3 : ℝ) / 4)) := by
    rw [hden]
    field_simp [hKhalf.ne', hCpow.ne']
  rw [hratio] at hraw
  exact hraw

/-- Explicit probability lower bound obtained by cubing the Holder estimate. -/
theorem rpow_three_halfMoment_ratio_le_measureReal_largeEvent
    {Omega : Type*} [MeasurableSpace Omega] {nu : Measure Omega}
    [IsProbabilityMeasure nu] {Z : Omega → ℝ} {a b : ℝ}
    (hlarge : MeasurableSet (halfMomentLargeEvent Z a))
    (hZnonneg : ∀ omega, 0 ≤ Z omega)
    (hhalfInt : Integrable (fun omega ↦ Z omega ^ ((1 : ℝ) / 2)) nu)
    (hhalfLp : MemLp (fun omega ↦ Z omega ^ ((1 : ℝ) / 2))
      (ENNReal.ofReal ((3 : ℝ) / 2)) nu)
    (ha : 0 < a) (hb : 0 < b)
    (hhalf : a ≤ ∫ omega, Z omega ^ ((1 : ℝ) / 2) ∂nu)
    (hthreeQuarter :
      (∫ omega, Z omega ^ ((3 : ℝ) / 4) ∂nu) ≤ b) :
    ((a / 2) / b ^ ((2 : ℝ) / 3)) ^ (3 : ℝ) ≤
      nu.real (halfMomentLargeEvent Z a) := by
  have hroot := halfMoment_le_half_add_largeEventHolder hlarge hZnonneg
    hhalfInt hhalfLp ha.le hhalf hthreeQuarter
  have hbpow : 0 < b ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hb _
  have hdiv :
      (a / 2) / b ^ ((2 : ℝ) / 3) ≤
        (nu.real (halfMomentLargeEvent Z a)) ^ ((1 : ℝ) / 3) := by
    exact (div_le_iff₀ hbpow).2 (by simpa [mul_comm] using hroot)
  have hpow := Real.rpow_le_rpow
    (div_nonneg (div_nonneg ha.le (by norm_num)) hbpow.le) hdiv
    (by norm_num : (0 : ℝ) ≤ 3)
  calc
    ((a / 2) / b ^ ((2 : ℝ) / 3)) ^ (3 : ℝ) ≤
        ((nu.real (halfMomentLargeEvent Z a)) ^ ((1 : ℝ) / 3)) ^
          (3 : ℝ) := hpow
    _ = nu.real (halfMomentLargeEvent Z a) := by
      rw [← Real.rpow_mul measureReal_nonneg]
      norm_num

/-- In particular, matching sharp `1/2` and `3/4` moment bounds give a
strictly positive chance of critical-scale energy. -/
theorem measureReal_halfMomentLargeEvent_pos
    {Omega : Type*} [MeasurableSpace Omega] {nu : Measure Omega}
    [IsProbabilityMeasure nu] {Z : Omega → ℝ} {a b : ℝ}
    (hlarge : MeasurableSet (halfMomentLargeEvent Z a))
    (hZnonneg : ∀ omega, 0 ≤ Z omega)
    (hhalfInt : Integrable (fun omega ↦ Z omega ^ ((1 : ℝ) / 2)) nu)
    (hhalfLp : MemLp (fun omega ↦ Z omega ^ ((1 : ℝ) / 2))
      (ENNReal.ofReal ((3 : ℝ) / 2)) nu)
    (ha : 0 < a) (hb : 0 < b)
    (hhalf : a ≤ ∫ omega, Z omega ^ ((1 : ℝ) / 2) ∂nu)
    (hthreeQuarter :
      (∫ omega, Z omega ^ ((3 : ℝ) / 4) ∂nu) ≤ b) :
    0 < nu.real (halfMomentLargeEvent Z a) := by
  have hbound := rpow_three_halfMoment_ratio_le_measureReal_largeEvent
    hlarge hZnonneg hhalfInt hhalfLp ha hb hhalf hthreeQuarter
  exact (Real.rpow_pos_of_pos
    (div_pos (div_pos ha (by norm_num)) (Real.rpow_pos_of_pos hb _)) _).trans_le
      hbound

/-- Scale-free form used by the critical energy argument.  If the `1/2`
moment is bounded below by `c * K^(1/2)` and the `3/4` moment is bounded above
by `C * K^(3/4)`, then the common scale `K` cancels completely and leaves a
fixed probability lower bound. -/
theorem criticalScale_halfMomentLargeEvent_probability_lower
    {Omega : Type*} [MeasurableSpace Omega] {nu : Measure Omega}
    [IsProbabilityMeasure nu] {Z : Omega → ℝ} {c C K : ℝ}
    (hlarge : MeasurableSet
      (halfMomentLargeEvent Z (c * K ^ ((1 : ℝ) / 2))))
    (hZnonneg : ∀ omega, 0 ≤ Z omega)
    (hhalfInt : Integrable (fun omega ↦ Z omega ^ ((1 : ℝ) / 2)) nu)
    (hhalfLp : MemLp (fun omega ↦ Z omega ^ ((1 : ℝ) / 2))
      (ENNReal.ofReal ((3 : ℝ) / 2)) nu)
    (hc : 0 < c) (hC : 0 < C) (hK : 0 < K)
    (hhalf :
      c * K ^ ((1 : ℝ) / 2) ≤
        ∫ omega, Z omega ^ ((1 : ℝ) / 2) ∂nu)
    (hthreeQuarter :
      (∫ omega, Z omega ^ ((3 : ℝ) / 4) ∂nu) ≤
        C * K ^ ((3 : ℝ) / 4)) :
    (c / (2 * C ^ ((2 : ℝ) / 3))) ^ (3 : ℝ) ≤
      nu.real (halfMomentLargeEvent Z (c * K ^ ((1 : ℝ) / 2))) := by
  have ha : 0 < c * K ^ ((1 : ℝ) / 2) :=
    mul_pos hc (Real.rpow_pos_of_pos hK _)
  have hb : 0 < C * K ^ ((3 : ℝ) / 4) :=
    mul_pos hC (Real.rpow_pos_of_pos hK _)
  have hraw := rpow_three_halfMoment_ratio_le_measureReal_largeEvent
    hlarge hZnonneg hhalfInt hhalfLp ha hb hhalf hthreeQuarter
  have hKhalf : 0 < K ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hK _
  have hden :
      (C * K ^ ((3 : ℝ) / 4)) ^ ((2 : ℝ) / 3) =
        C ^ ((2 : ℝ) / 3) * K ^ ((1 : ℝ) / 2) := by
    rw [Real.mul_rpow hC.le (Real.rpow_nonneg hK.le _),
      ← Real.rpow_mul hK.le]
    congr 2
    norm_num
  have hCpow : 0 < C ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hC _
  have hratio :
      (c * K ^ ((1 : ℝ) / 2) / 2) /
          (C * K ^ ((3 : ℝ) / 4)) ^ ((2 : ℝ) / 3) =
        c / (2 * C ^ ((2 : ℝ) / 3)) := by
    rw [hden]
    field_simp [hKhalf.ne', hCpow.ne']
  rw [hratio] at hraw
  exact hraw

end Problem1144
end Erdos
