import Erdos.Problem1144.HarperBivariateRelativeCell
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Prod

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

local instance unitAddCircleVolume_isProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-!
# Shifted lattice averaging for the two-height path

The local bivariate comparison expands a core interval of width `delta` by
`h` on both sides.  We put that core inside a lattice of period
`delta + 2*h`.  The expanded intervals are then the disjoint full lattice
cells.  Averaging the lattice phase retains exactly the core fraction
`delta / (delta + 2*h)` in each real coordinate.

This file isolates the phase-averaging geometry from the later probability
and path arguments.  We use the Haar probability measure on `UnitAddCircle`
to avoid choosing representatives while averaging.
-/

/-- The half-open arc of normalized length `c` in the unit additive circle,
written using the canonical representative in `(0,1]`. -/
def harperUnitIocArc (c : Real) : Set UnitAddCircle :=
  (AddCircle.measurableEquivIoc 1 0) ⁻¹'
    ((Subtype.val : Set.Ioc (0 : Real) (0 + 1) → Real) ⁻¹' Ioc 0 c)

theorem measurableSet_harperUnitIocArc (c : Real) :
    MeasurableSet (harperUnitIocArc c) := by
  apply (measurableSet_Ioc.preimage measurable_subtype_coe).preimage
  exact (AddCircle.measurableEquivIoc 1 0).measurable

/-- A half-open unit-circle arc has its literal Euclidean length. -/
theorem volume_harperUnitIocArc {c : Real} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    volume (harperUnitIocArc c) = ENNReal.ofReal c := by
  let S : Set (Set.Ioc (0 : Real) (0 + 1)) :=
    (Subtype.val : Set.Ioc (0 : Real) (0 + 1) → Real) ⁻¹' Ioc 0 c
  have hS : MeasurableSet S :=
    measurableSet_Ioc.preimage measurable_subtype_coe
  have hmp := AddCircle.measurePreserving_equivIoc (T := (1 : Real)) (a := (0 : Real))
  change volume ((AddCircle.equivIoc 1 0) ⁻¹' S) = ENNReal.ofReal c
  calc
    volume ((AddCircle.equivIoc 1 0) ⁻¹' S) =
        (Measure.comap Subtype.val volume) S := by
      simpa only [AddCircle.measurableEquivIoc] using
        hmp.measure_preimage hS.nullMeasurableSet
    _ = volume (Subtype.val '' S) :=
      comap_subtype_coe_apply measurableSet_Ioc volume S
    _ = ENNReal.ofReal c := by
      rw [show Subtype.val '' S = Ioc (0 : Real) c by
        ext x
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact hz
        · intro hx
          refine ⟨⟨x, ?_⟩, hx, rfl⟩
          constructor
          · exact hx.1
          · linarith [hx.2], Real.volume_Ioc]
      simp [hc0]

/-- Phases for which a fixed point of the unit circle lies in the core arc.
The subtraction convention is chosen so that the later real lattice has
origin equal to the phase representative. -/
def harperUnitCorePhaseSet (c : Real) (x : UnitAddCircle) :
    Set UnitAddCircle :=
  (fun phi ↦ x - phi) ⁻¹' harperUnitIocArc c

theorem measurableSet_harperUnitCorePhaseSet (c : Real) (x : UnitAddCircle) :
    MeasurableSet (harperUnitCorePhaseSet c x) := by
  exact (measurableSet_harperUnitIocArc c).preimage
    (measurable_const.sub measurable_id)

/-- Every fixed point is captured by exactly the core fraction of all
lattice phases. -/
theorem volume_harperUnitCorePhaseSet {c : Real} (x : UnitAddCircle)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    volume (harperUnitCorePhaseSet c x) = ENNReal.ofReal c := by
  have hmp : MeasurePreserving (fun phi : UnitAddCircle ↦ x - phi) := by
    convert (measurePreserving_add_left volume x).comp
      (Measure.measurePreserving_neg volume) using 1
    ext phi
    simp only [Function.comp_apply, sub_eq_add_neg]
  exact (hmp.measure_preimage
    (measurableSet_harperUnitIocArc c).nullMeasurableSet).trans
      (volume_harperUnitIocArc hc0 hc1)

/-- Coordinatewise phase capture multiplies exactly under the finite product
of unit-circle Haar probability measures. -/
theorem measureReal_pi_harperUnitCorePhaseSet
    {ι : Type*} [Fintype ι] (c : ι → Real) (x : ι → UnitAddCircle)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) :
    (Measure.pi (fun _ : ι ↦ (volume : Measure UnitAddCircle))).real
        (Set.pi Set.univ (fun i ↦ harperUnitCorePhaseSet (c i) (x i))) =
      ∏ i, c i := by
  rw [Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [volume_harperUnitCorePhaseSet (x i) (hc0 i) (hc1 i),
    ENNReal.toReal_ofReal (hc0 i)]

theorem measure_pi_harperUnitCorePhaseSet
    {ι : Type*} [Fintype ι] (c : ι → Real) (x : ι → UnitAddCircle)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) :
    (Measure.pi (fun _ : ι ↦ (volume : Measure UnitAddCircle)))
        (Set.pi Set.univ (fun i ↦ harperUnitCorePhaseSet (c i) (x i))) =
      ∏ i, ENNReal.ofReal (c i) := by
  rw [Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro i _hi
  exact volume_harperUnitCorePhaseSet (x i) (hc0 i) (hc1 i)

/-- Joint relation saying that `omega` lies in `A` and every coordinate is
captured by the corresponding phase. -/
def harperPhaseCaptureRelation
    {Ω ι : Type*} [MeasurableSpace Ω]
    (A : Set Ω) (c : ι → Real) (q : Ω → ι → UnitAddCircle) :
    Set ((ι → UnitAddCircle) × Ω) :=
  (Prod.snd ⁻¹' A) ∩
    ⋂ i, (fun z ↦ q z.2 i - z.1 i) ⁻¹' harperUnitIocArc (c i)

theorem measurableSet_harperPhaseCaptureRelation
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {A : Set Ω} (hA : MeasurableSet A) (c : ι → Real)
    {q : Ω → ι → UnitAddCircle} (hq : Measurable q) :
    MeasurableSet (harperPhaseCaptureRelation A c q) := by
  apply (hA.preimage measurable_snd).inter
  apply MeasurableSet.iInter
  intro i
  apply (measurableSet_harperUnitIocArc (c i)).preimage
  exact ((measurable_pi_apply i).comp (hq.comp measurable_snd)).sub
    ((measurable_pi_apply i).comp measurable_fst)

/-- Fubini plus Haar averaging chooses simultaneous phases retaining the
exact product of all coordinate core fractions. -/
theorem exists_phase_measure_capture_ge_product
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    {A : Set Ω} (hA : MeasurableSet A)
    (c : ι → Real) (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    {q : Ω → ι → UnitAddCircle} (hq : Measurable q) :
    ∃ phi : ι → UnitAddCircle,
      (∏ i, ENNReal.ofReal (c i)) * mu A ≤
        mu (Prod.mk phi ⁻¹' harperPhaseCaptureRelation A c q) := by
  classical
  let H : Measure (ι → UnitAddCircle) :=
    Measure.pi (fun _ : ι ↦ (volume : Measure UnitAddCircle))
  letI : IsProbabilityMeasure H := by
    dsimp only [H]
    infer_instance
  let R : Set ((ι → UnitAddCircle) × Ω) :=
    harperPhaseCaptureRelation A c q
  have hR : MeasurableSet R :=
    measurableSet_harperPhaseCaptureRelation hA c hq
  let C : ENNReal := ∏ i, ENNReal.ofReal (c i)
  have hphaseFiber (omega : Ω) :
      H ((fun phi ↦ (phi, omega)) ⁻¹' R) =
        if omega ∈ A then C else 0 := by
    by_cases homega : omega ∈ A
    · have hset :
          (fun phi ↦ (phi, omega)) ⁻¹' R =
            Set.pi Set.univ
              (fun i ↦ harperUnitCorePhaseSet (c i) (q omega i)) := by
        ext phi
        simp [R, harperPhaseCaptureRelation, homega,
          harperUnitCorePhaseSet]
      rw [hset, measure_pi_harperUnitCorePhaseSet c (q omega) hc0 hc1]
      simp [C, homega]
    · have hset : (fun phi ↦ (phi, omega)) ⁻¹' R = ∅ := by
        ext phi
        simp [R, harperPhaseCaptureRelation, homega]
      rw [hset, measure_empty]
      simp [homega]
  have htotal :
      (H.prod mu) R = C * mu A := by
    rw [Measure.prod_apply_symm hR]
    simp_rw [hphaseFiber]
    have hindicator :
        (fun omega : Ω ↦ if omega ∈ A then C else 0) =
          A.indicator (fun _ ↦ C) := by
      funext omega
      simp only [Set.indicator_apply]
    rw [hindicator, lintegral_indicator_const hA]
  have hfinite :
      (∫⁻ phi, mu (Prod.mk phi ⁻¹' R) ∂H) ≠ ∞ := by
    rw [← Measure.prod_apply hR]
    exact measure_ne_top _ _
  obtain ⟨phi, hphi⟩ :=
    exists_lintegral_le (μ := H)
      (f := fun phi ↦ mu (Prod.mk phi ⁻¹' R)) hfinite
  refine ⟨phi, ?_⟩
  rw [← htotal, Measure.prod_apply hR]
  exact hphi

/-- The real representative of a unit-circle phase in the fundamental
interval `(0,1]`. -/
def harperUnitPhaseRepresentative (phi : UnitAddCircle) : Real :=
  (AddCircle.equivIoc 1 0 phi : Set.Ioc (0 : Real) (0 + 1)).1

/-- The normalized real core lattice of width `c` and unit period. -/
def harperNormalizedCoreUnion (c : Real) (phi : UnitAddCircle) : Set Real :=
  ⋃ z : Int,
    Ioc ((z : Real) + harperUnitPhaseRepresentative phi)
      ((z : Real) + harperUnitPhaseRepresentative phi + c)

/-- Circle capture is literally membership in the corresponding half-open
shifted lattice on the real line. -/
theorem mem_harperNormalizedCoreUnion_iff
    {c q : Real} {phi : UnitAddCircle} (hc1 : c ≤ 1) :
    q ∈ harperNormalizedCoreUnion c phi ↔
      phi ∈ harperUnitCorePhaseSet c (q : UnitAddCircle) := by
  let theta : Real := harperUnitPhaseRepresentative phi
  have htheta : (theta : UnitAddCircle) = phi := by
    dsimp only [theta, harperUnitPhaseRepresentative]
    exact AddCircle.coe_equivIoc
  have hrepr :
      harperUnitPhaseRepresentative
          ((q : UnitAddCircle) - phi) =
        toIocMod (by positivity : (0 : Real) < 1) 0 (q - theta) := by
    dsimp only [harperUnitPhaseRepresentative]
    rw [← htheta]
    change
      ((AddCircle.equivIoc 1 0
          ((q - theta : Real) : UnitAddCircle)).1) = _
    rfl
  rw [harperNormalizedCoreUnion, mem_iUnion]
  change
    (∃ z : Int,
      (z : Real) + theta < q ∧
        q ≤ (z : Real) + theta + c) ↔ _
  rw [harperUnitCorePhaseSet, Set.mem_preimage,
    harperUnitIocArc, Set.mem_preimage, Set.mem_preimage]
  change
    (∃ z : Int,
      (z : Real) + theta < q ∧
        q ≤ (z : Real) + theta + c) ↔
      harperUnitPhaseRepresentative ((q : UnitAddCircle) - phi) ∈ Ioc 0 c
  rw [hrepr]
  constructor
  · rintro ⟨z, hzLower, hzUpper⟩
    have hu : q - theta - (z : Real) ∈ Ioc (0 : Real) c := by
      constructor <;> linarith
    have hmod :
        toIocMod (by positivity : (0 : Real) < 1) 0 (q - theta) =
          q - theta - (z : Real) := by
      apply (toIocMod_eq_iff (by positivity : (0 : Real) < 1)).2
      refine ⟨⟨hu.1, hu.2.trans (by simpa using hc1)⟩, z, ?_⟩
      simp only [zsmul_eq_mul, mul_one]
      ring
    simpa only [hmod] using hu
  · intro hu
    let u := toIocMod (by positivity : (0 : Real) < 1) 0 (q - theta)
    have hu' : u ∈ Ioc (0 : Real) c := hu
    have hdecomp :=
      (toIocMod_eq_iff (by positivity : (0 : Real) < 1)
        (a := (0 : Real)) (b := q - theta) (c := u)).1 rfl
    obtain ⟨_huFund, z, hz⟩ := hdecomp
    refine ⟨z, ?_, ?_⟩
    · have := hu'.1
      simp only [zsmul_eq_mul, mul_one] at hz
      linarith
    · have := hu'.2
      simp only [zsmul_eq_mul, mul_one] at hz
      linarith

/-- Period of the shifted lattice whose core has width `delta` and whose
Gaussian enlargement has radius `h`. -/
def harperShiftedLatticePeriod (delta h : Real) : Real := delta + 2 * h

/-- One half-open core cell in the shifted real lattice. -/
def harperShiftedCoreCell (delta h : Real) (phi : UnitAddCircle) (z : Int) :
    Set Real :=
  Ioc (((z : Real) + harperUnitPhaseRepresentative phi) *
      harperShiftedLatticePeriod delta h)
    (((z : Real) + harperUnitPhaseRepresentative phi) *
        harperShiftedLatticePeriod delta h + delta)

/-- The full cell obtained by enlarging a core cell by `h` on both sides. -/
def harperShiftedFullCell (delta h : Real) (phi : UnitAddCircle) (z : Int) :
    Set Real :=
  Ioc (((z : Real) + harperUnitPhaseRepresentative phi) *
        harperShiftedLatticePeriod delta h - h)
    (((z : Real) + harperUnitPhaseRepresentative phi) *
        harperShiftedLatticePeriod delta h + delta + h)

/-- Union of all shifted core cells. -/
def harperShiftedCoreUnion (delta h : Real) (phi : UnitAddCircle) : Set Real :=
  ⋃ z : Int, harperShiftedCoreCell delta h phi z

/-- Only finitely many cells of a positive-period shifted lattice can meet a
fixed bounded interval. -/
theorem finite_shiftedCoreCell_indices_meeting_Icc
    {delta h R : Real} (phi : UnitAddCircle)
    (hperiod : 0 < harperShiftedLatticePeriod delta h) :
    {z : Int | Set.Nonempty
        (harperShiftedCoreCell delta h phi z ∩ Icc (-R) R)}.Finite := by
  let period := harperShiftedLatticePeriod delta h
  let theta := harperUnitPhaseRepresentative phi
  let lower : Real := (-R - delta) / period - theta
  let upper : Real := R / period - theta
  refine (Set.finite_Icc (Int.ceil lower) (Int.floor upper)).subset ?_
  intro z hz
  obtain ⟨x, hxCell, hxBox⟩ := hz
  have hxCell' :
      ((z : Real) + theta) * period < x ∧
        x ≤ ((z : Real) + theta) * period + delta := by
    simpa only [harperShiftedCoreCell, period, theta, Set.mem_Ioc]
      using hxCell
  have hLowerReal : lower ≤ (z : Real) := by
    dsimp only [lower]
    rw [sub_le_iff_le_add, div_le_iff₀ hperiod]
    nlinarith [hxBox.1, hxCell'.2]
  have hUpperReal : (z : Real) ≤ upper := by
    dsimp only [upper]
    rw [le_sub_iff_add_le, le_div_iff₀ hperiod]
    nlinarith [hxCell'.1, hxBox.2]
  constructor
  · exact Int.ceil_le.mpr hLowerReal
  · exact Int.le_floor.mpr hUpperReal

/-- Membership in the scaled core lattice is the unit-circle capture event
with normalized width `delta / (delta + 2*h)`. -/
theorem mem_harperShiftedCoreUnion_iff
    {delta h x : Real} {phi : UnitAddCircle}
    (hperiod : 0 < harperShiftedLatticePeriod delta h)
    (hfraction : delta / harperShiftedLatticePeriod delta h ≤ 1) :
    x ∈ harperShiftedCoreUnion delta h phi ↔
      phi ∈ harperUnitCorePhaseSet
        (delta / harperShiftedLatticePeriod delta h)
        ((x / harperShiftedLatticePeriod delta h : Real) : UnitAddCircle) := by
  rw [← mem_harperNormalizedCoreUnion_iff hfraction]
  rw [harperShiftedCoreUnion, mem_iUnion,
    harperNormalizedCoreUnion, mem_iUnion]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    change
      (z : Real) + harperUnitPhaseRepresentative phi <
          x / harperShiftedLatticePeriod delta h ∧
        x / harperShiftedLatticePeriod delta h ≤
          (z : Real) + harperUnitPhaseRepresentative phi +
            delta / harperShiftedLatticePeriod delta h
    change
      ((z : Real) + harperUnitPhaseRepresentative phi) *
            harperShiftedLatticePeriod delta h < x ∧
        x ≤ ((z : Real) + harperUnitPhaseRepresentative phi) *
            harperShiftedLatticePeriod delta h + delta at hz
    constructor
    · exact (lt_div_iff₀ hperiod).2 hz.1
    · rw [div_le_iff₀ hperiod]
      calc
        x ≤ ((z : Real) + harperUnitPhaseRepresentative phi) *
              harperShiftedLatticePeriod delta h + delta := hz.2
        _ = ((z : Real) + harperUnitPhaseRepresentative phi +
              delta / harperShiftedLatticePeriod delta h) *
                harperShiftedLatticePeriod delta h := by
          field_simp [hperiod.ne']
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    change
      ((z : Real) + harperUnitPhaseRepresentative phi) *
            harperShiftedLatticePeriod delta h < x ∧
        x ≤ ((z : Real) + harperUnitPhaseRepresentative phi) *
            harperShiftedLatticePeriod delta h + delta
    change
      (z : Real) + harperUnitPhaseRepresentative phi <
          x / harperShiftedLatticePeriod delta h ∧
        x / harperShiftedLatticePeriod delta h ≤
          (z : Real) + harperUnitPhaseRepresentative phi +
            delta / harperShiftedLatticePeriod delta h at hz
    constructor
    · exact (lt_div_iff₀ hperiod).1 hz.1
    · have hscaled := (div_le_iff₀ hperiod).1 hz.2
      calc
        x ≤ ((z : Real) + harperUnitPhaseRepresentative phi +
              delta / harperShiftedLatticePeriod delta h) *
                harperShiftedLatticePeriod delta h := hscaled
        _ = ((z : Real) + harperUnitPhaseRepresentative phi) *
              harperShiftedLatticePeriod delta h + delta := by
          field_simp [hperiod.ne']

/-- The full shifted cells are genuinely disjoint; the Fejer enlargement is
absorbed by the gap between neighboring cores. -/
theorem pairwiseDisjoint_harperShiftedFullCell
    {delta h : Real} (phi : UnitAddCircle)
    (hperiod : 0 < harperShiftedLatticePeriod delta h) :
    Pairwise (fun z w : Int ↦
      Disjoint (harperShiftedFullCell delta h phi z)
        (harperShiftedFullCell delta h phi w)) := by
  intro z w hzw
  rcases lt_or_gt_of_ne hzw with hlt | hgt
  · apply Set.Ioc_disjoint_Ioc_of_le
    have hzwSucc : z + 1 ≤ w := by omega
    have hcast : ((z + 1 : Int) : Real) ≤ (w : Real) := by
      exact_mod_cast hzwSucc
    have hmul := mul_le_mul_of_nonneg_right
      (add_le_add_right hcast (harperUnitPhaseRepresentative phi)) hperiod.le
    change
      ((z : Real) + harperUnitPhaseRepresentative phi) *
            harperShiftedLatticePeriod delta h + delta + h ≤
        ((w : Real) + harperUnitPhaseRepresentative phi) *
            harperShiftedLatticePeriod delta h - h
    calc
      ((z : Real) + harperUnitPhaseRepresentative phi) *
              harperShiftedLatticePeriod delta h + delta + h =
          (((z + 1 : Int) : Real) + harperUnitPhaseRepresentative phi) *
              harperShiftedLatticePeriod delta h - h := by
        simp only [Int.cast_add, Int.cast_one,
          harperShiftedLatticePeriod]
        ring
      _ ≤ ((w : Real) + harperUnitPhaseRepresentative phi) *
            harperShiftedLatticePeriod delta h - h := by linarith
  · apply Disjoint.symm
    apply Set.Ioc_disjoint_Ioc_of_le
    have hwzSucc : w + 1 ≤ z := by omega
    have hcast : ((w + 1 : Int) : Real) ≤ (z : Real) := by
      exact_mod_cast hwzSucc
    have hmul := mul_le_mul_of_nonneg_right
      (add_le_add_right hcast (harperUnitPhaseRepresentative phi)) hperiod.le
    change
      ((w : Real) + harperUnitPhaseRepresentative phi) *
            harperShiftedLatticePeriod delta h + delta + h ≤
        ((z : Real) + harperUnitPhaseRepresentative phi) *
            harperShiftedLatticePeriod delta h - h
    calc
      ((w : Real) + harperUnitPhaseRepresentative phi) *
              harperShiftedLatticePeriod delta h + delta + h =
          (((w + 1 : Int) : Real) + harperUnitPhaseRepresentative phi) *
              harperShiftedLatticePeriod delta h - h := by
        simp only [Int.cast_add, Int.cast_one,
          harperShiftedLatticePeriod]
        ring
      _ ≤ ((z : Real) + harperUnitPhaseRepresentative phi) *
            harperShiftedLatticePeriod delta h - h := by linarith

/-- A bivariate core cell, with an independently shifted lattice in each
coordinate. -/
def harperShiftedPairCoreCell (delta h : Real)
    (phi : UnitAddCircle × UnitAddCircle) (z : Int × Int) :
    Set (Real × Real) :=
  harperShiftedCoreCell delta h phi.1 z.1 ×ˢ
    harperShiftedCoreCell delta h phi.2 z.2

/-- The corresponding bivariate full cell. -/
def harperShiftedPairFullCell (delta h : Real)
    (phi : UnitAddCircle × UnitAddCircle) (z : Int × Int) :
    Set (Real × Real) :=
  harperShiftedFullCell delta h phi.1 z.1 ×ˢ
    harperShiftedFullCell delta h phi.2 z.2

theorem measurableSet_harperShiftedPairCoreCell
    (delta h : Real) (phi : UnitAddCircle × UnitAddCircle) (z : Int × Int) :
    MeasurableSet (harperShiftedPairCoreCell delta h phi z) :=
  measurableSet_Ioc.prod measurableSet_Ioc

theorem measurableSet_harperShiftedPairFullCell
    (delta h : Real) (phi : UnitAddCircle × UnitAddCircle) (z : Int × Int) :
    MeasurableSet (harperShiftedPairFullCell delta h phi z) :=
  measurableSet_Ioc.prod measurableSet_Ioc

/-- A full path cell is the coordinatewise product of bivariate full cells. -/
def harperShiftedPairPathCoreCell {n : Nat}
    (delta h : Fin n → Real)
    (phi : Fin n → UnitAddCircle × UnitAddCircle)
    (z : Fin n → Int × Int) : Set (Fin n → Real × Real) :=
  Set.pi Set.univ (fun i ↦
    harperShiftedPairCoreCell (delta i) (h i) (phi i) (z i))

def harperShiftedPairPathFullCell {n : Nat}
    (delta h : Fin n → Real)
    (phi : Fin n → UnitAddCircle × UnitAddCircle)
    (z : Fin n → Int × Int) : Set (Fin n → Real × Real) :=
  Set.pi Set.univ (fun i ↦
    harperShiftedPairFullCell (delta i) (h i) (phi i) (z i))

theorem measurableSet_harperShiftedPairPathCoreCell {n : Nat}
    (delta h : Fin n → Real)
    (phi : Fin n → UnitAddCircle × UnitAddCircle)
    (z : Fin n → Int × Int) :
    MeasurableSet (harperShiftedPairPathCoreCell delta h phi z) := by
  exact MeasurableSet.univ_pi fun i ↦
    measurableSet_harperShiftedPairCoreCell _ _ _ _

theorem measurableSet_harperShiftedPairPathFullCell {n : Nat}
    (delta h : Fin n → Real)
    (phi : Fin n → UnitAddCircle × UnitAddCircle)
    (z : Fin n → Int × Int) :
    MeasurableSet (harperShiftedPairPathFullCell delta h phi z) := by
  exact MeasurableSet.univ_pi fun i ↦
    measurableSet_harperShiftedPairFullCell _ _ _ _

/-- Paths whose two coordinates lie in the selected core lattice at every
block. -/
def harperShiftedPairPathCoreSet {n : Nat}
    (delta h : Fin n → Real)
    (phi : Fin n → UnitAddCircle × UnitAddCircle) :
    Set (Fin n → Real × Real) :=
  Set.pi Set.univ (fun i ↦
    harperShiftedCoreUnion (delta i) (h i) (phi i).1 ×ˢ
      harperShiftedCoreUnion (delta i) (h i) (phi i).2)

/-- The simultaneous core lattice is the union of its integer-indexed path
cells. -/
theorem harperShiftedPairPathCoreSet_eq_iUnion {n : Nat}
    (delta h : Fin n → Real)
    (phi : Fin n → UnitAddCircle × UnitAddCircle) :
    harperShiftedPairPathCoreSet delta h phi =
      ⋃ z : Fin n → Int × Int,
        harperShiftedPairPathCoreCell delta h phi z := by
  classical
  ext omega
  constructor
  · intro homega
    have hall : ∀ i : Fin n,
        (∃ z : Int,
          (omega i).1 ∈ harperShiftedCoreCell
            (delta i) (h i) (phi i).1 z) ∧
        (∃ z : Int,
          (omega i).2 ∈ harperShiftedCoreCell
            (delta i) (h i) (phi i).2 z) := by
      simpa only [harperShiftedPairPathCoreSet, Set.mem_pi,
        Set.mem_univ, forall_const, Set.mem_prod,
        harperShiftedCoreUnion, Set.mem_iUnion] using homega
    choose z₁ hz₁ using fun i ↦ (hall i).1
    choose z₂ hz₂ using fun i ↦ (hall i).2
    let z : Fin n → Int × Int := fun i ↦ (z₁ i, z₂ i)
    refine Set.mem_iUnion.mpr ⟨z, ?_⟩
    simp only [harperShiftedPairPathCoreCell, Set.mem_pi,
      Set.mem_univ, forall_const, harperShiftedPairCoreCell,
      Set.mem_prod, z]
    exact fun i ↦ ⟨hz₁ i, hz₂ i⟩
  · intro homega
    obtain ⟨z, hz⟩ := Set.mem_iUnion.mp homega
    simp only [harperShiftedPairPathCoreCell, Set.mem_pi,
      Set.mem_univ, forall_const, harperShiftedPairCoreCell,
      Set.mem_prod] at hz
    simp only [harperShiftedPairPathCoreSet, Set.mem_pi,
      Set.mem_univ, forall_const, Set.mem_prod,
      harperShiftedCoreUnion, Set.mem_iUnion]
    exact fun i ↦ ⟨⟨(z i).1, (hz i).1⟩, ⟨(z i).2, (hz i).2⟩⟩

/-- A coordinatewise bounded event meets only finitely many shifted path
cells.  The returned family contains exactly all cells meeting `A`, hence it
both covers the selected core portion and supplies a witness in `A` for every
active cell. -/
theorem exists_finite_shiftedPairPathCoreCell_cover_of_bounded {n : Nat}
    (A : Set (Fin n → Real × Real))
    (delta h R : Fin n → Real)
    (phi : Fin n → UnitAddCircle × UnitAddCircle)
    (hperiod : ∀ i, 0 < harperShiftedLatticePeriod (delta i) (h i))
    (hbounded : ∀ omega ∈ A, ∀ i,
      (omega i).1 ∈ Icc (-(R i)) (R i) ∧
        (omega i).2 ∈ Icc (-(R i)) (R i)) :
    ∃ active : Finset (Fin n → Int × Int),
      A ∩ harperShiftedPairPathCoreSet delta h phi ⊆
          ⋃ z ∈ active, harperShiftedPairPathCoreCell delta h phi z ∧
        ∀ z ∈ active,
          Set.Nonempty
            (A ∩ harperShiftedPairPathCoreCell delta h phi z) := by
  classical
  let activeSet : Set (Fin n → Int × Int) :=
    {z | Set.Nonempty
      (A ∩ harperShiftedPairPathCoreCell delta h phi z)}
  have hactiveFinite : activeSet.Finite := by
    let indexSet : Fin n → Set (Int × Int) := fun i ↦
      {z : Int | Set.Nonempty
          (harperShiftedCoreCell (delta i) (h i) (phi i).1 z ∩
            Icc (-(R i)) (R i))} ×ˢ
      {z : Int | Set.Nonempty
          (harperShiftedCoreCell (delta i) (h i) (phi i).2 z ∩
            Icc (-(R i)) (R i))}
    have hindexFinite (i : Fin n) : (indexSet i).Finite := by
      apply Set.Finite.prod
      · exact finite_shiftedCoreCell_indices_meeting_Icc
          (phi i).1 (hperiod i)
      · exact finite_shiftedCoreCell_indices_meeting_Icc
          (phi i).2 (hperiod i)
    refine (Set.Finite.pi hindexFinite).subset ?_
    intro z hz
    rw [Set.mem_pi]
    intro i _hi
    obtain ⟨omega, homegaA, homegaCell⟩ := hz
    have hcell :
        (omega i).1 ∈ harperShiftedCoreCell
            (delta i) (h i) (phi i).1 (z i).1 ∧
          (omega i).2 ∈ harperShiftedCoreCell
            (delta i) (h i) (phi i).2 (z i).2 := by
      simpa only [harperShiftedPairPathCoreCell, Set.mem_pi,
        Set.mem_univ, forall_const, harperShiftedPairCoreCell,
        Set.mem_prod] using homegaCell i
    have hbox := hbounded omega homegaA i
    exact ⟨⟨(omega i).1, hcell.1, hbox.1⟩,
      ⟨(omega i).2, hcell.2, hbox.2⟩⟩
  let active : Finset (Fin n → Int × Int) := hactiveFinite.toFinset
  refine ⟨active, ?_, ?_⟩
  · intro omega homega
    rw [harperShiftedPairPathCoreSet_eq_iUnion] at homega
    obtain ⟨z, hzCell⟩ := Set.mem_iUnion.mp homega.2
    have hzActive : z ∈ active := by
      change z ∈ hactiveFinite.toFinset
      rw [Set.Finite.mem_toFinset]
      exact ⟨omega, homega.1, hzCell⟩
    exact Set.mem_iUnion₂.mpr ⟨z, hzActive, hzCell⟩
  · intro z hz
    change z ∈ hactiveFinite.toFinset at hz
    rw [Set.Finite.mem_toFinset] at hz
    exact hz

/-- A point of a full cell is at most one lattice period from every point of
the corresponding core cell. -/
theorem abs_sub_le_period_of_mem_shiftedCoreCell_shiftedFullCell
    {delta h : Real} {phi : UnitAddCircle} {z : Int} {x y : Real}
    (hdelta : 0 ≤ delta) (hh : 0 ≤ h)
    (hx : x ∈ harperShiftedCoreCell delta h phi z)
    (hy : y ∈ harperShiftedFullCell delta h phi z) :
    |y - x| ≤ harperShiftedLatticePeriod delta h := by
  have hx' := hx
  have hy' := hy
  simp only [harperShiftedCoreCell, Set.mem_Ioc] at hx'
  simp only [harperShiftedFullCell, Set.mem_Ioc] at hy'
  rw [abs_le]
  unfold harperShiftedLatticePeriod
  constructor <;> linarith

theorem abs_shiftedCoreCell_lower_le_abs_add_delta
    {delta h : Real} {phi : UnitAddCircle} {z : Int} {x : Real}
    (hdelta : 0 ≤ delta)
    (hx : x ∈ harperShiftedCoreCell delta h phi z) :
    |((z : Real) + harperUnitPhaseRepresentative phi) *
        harperShiftedLatticePeriod delta h| ≤ |x| + delta := by
  let a := ((z : Real) + harperUnitPhaseRepresentative phi) *
    harperShiftedLatticePeriod delta h
  have hx' : a < x ∧ x ≤ a + delta := by
    simpa only [a, harperShiftedCoreCell, Set.mem_Ioc] using hx
  have hdiff : |x - a| ≤ delta := by
    rw [abs_of_nonneg (by linarith [hx'.1])]
    linarith [hx'.2]
  have htriangle : |a| ≤ |x| + |x - a| := by
    calc
      |a| = |x - (x - a)| := by congr 1 <;> ring
      _ ≤ |x| + |x - a| := abs_sub _ _
  dsimp only [a] at htriangle ⊢
  linarith

/-- Coordinatewise `epsilon`-neighborhood of a bivariate increment-path
event. -/
def harperPairPathCoordinateNeighborhood {n : Nat}
    (A : Set (Fin n → Real × Real)) (epsilon : Fin n → Real) :
    Set (Fin n → Real × Real) :=
  {y | ∃ x ∈ A, ∀ i,
    |(y i).1 - (x i).1| ≤ epsilon i ∧
      |(y i).2 - (x i).2| ≤ epsilon i}

/-- Full cells indexed by cells meeting `A` lie in the coordinatewise
period-neighborhood of `A`. -/
theorem iUnion_fullCells_subset_coordinateNeighborhood_of_meets
    {n : Nat} (A : Set (Fin n → Real × Real))
    (delta h : Fin n → Real)
    (phi : Fin n → UnitAddCircle × UnitAddCircle)
    (active : Finset (Fin n → Int × Int))
    (hdelta : ∀ i, 0 ≤ delta i) (hh : ∀ i, 0 ≤ h i)
    (hmeets : ∀ z ∈ active,
      Set.Nonempty (A ∩ harperShiftedPairPathCoreCell delta h phi z)) :
    (⋃ z ∈ active, harperShiftedPairPathFullCell delta h phi z) ⊆
      harperPairPathCoordinateNeighborhood A
        (fun i ↦ harperShiftedLatticePeriod (delta i) (h i)) := by
  intro y hy
  obtain ⟨z, hzActive, hyCell⟩ := Set.mem_iUnion₂.mp hy
  obtain ⟨x, hxA, hxCell⟩ := hmeets z hzActive
  refine ⟨x, hxA, ?_⟩
  have hxAll : ∀ i,
      (x i).1 ∈ harperShiftedCoreCell
          (delta i) (h i) (phi i).1 (z i).1 ∧
        (x i).2 ∈ harperShiftedCoreCell
          (delta i) (h i) (phi i).2 (z i).2 := by
    simpa only [harperShiftedPairPathCoreCell, Set.mem_pi,
      Set.mem_univ, forall_const, harperShiftedPairCoreCell,
      Set.mem_prod] using hxCell
  have hyAll : ∀ i,
      (y i).1 ∈ harperShiftedFullCell
          (delta i) (h i) (phi i).1 (z i).1 ∧
        (y i).2 ∈ harperShiftedFullCell
          (delta i) (h i) (phi i).2 (z i).2 := by
    simpa only [harperShiftedPairPathFullCell, Set.mem_pi,
      Set.mem_univ, forall_const, harperShiftedPairFullCell,
      Set.mem_prod] using hyCell
  intro i
  exact ⟨
    abs_sub_le_period_of_mem_shiftedCoreCell_shiftedFullCell
      (hdelta i) (hh i) (hxAll i).1 (hyAll i).1,
    abs_sub_le_period_of_mem_shiftedCoreCell_shiftedFullCell
      (hdelta i) (hh i) (hxAll i).2 (hyAll i).2⟩

theorem abs_harperPathPartialSum_sub_le_total_of_coordinatewise
    {n : Nat} {x y epsilon : Fin n → Real}
    (hepsilon : ∀ i, 0 ≤ epsilon i)
    (hcoordinate : ∀ i, |y i - x i| ≤ epsilon i)
    (k : Fin n) :
    |Problem520.harperPathPartialSum y k -
        Problem520.harperPathPartialSum x k| ≤ ∑ i, epsilon i := by
  calc
    |Problem520.harperPathPartialSum y k -
        Problem520.harperPathPartialSum x k| =
        |∑ i ∈ Finset.Iic k, (y i - x i)| := by
      simp only [Problem520.harperPathPartialSum, Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ Finset.Iic k, |y i - x i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.Iic k, epsilon i :=
      Finset.sum_le_sum fun i _hi ↦ hcoordinate i
    _ ≤ ∑ i, epsilon i := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _hi _hnot ↦ hepsilon i)

/-- A one-unit enlargement of the coarse linear guard. -/
def harperRelaxedLinearGuardPathEvent (n : Nat) : Set (Fin n → Real) :=
  Problem520.harperPartialSumBarrierSet
    (fun k ↦ -65 * (((k.val + 1 : Nat) : Real)))
    (fun _ ↦ 2)

theorem measurableSet_harperRelaxedLinearGuardPathEvent (n : Nat) :
    MeasurableSet (harperRelaxedLinearGuardPathEvent n) :=
  Problem520.measurableSet_harperPartialSumBarrierSet _ _

def harperPairedRelaxedLinearGuardPathEvent (n : Nat) :
    Set (Fin n → Real × Real) :=
  harperPairPathUnzipCLM n ⁻¹'
    (harperRelaxedLinearGuardPathEvent n ×ˢ
      harperRelaxedLinearGuardPathEvent n)

theorem measurableSet_harperPairedRelaxedLinearGuardPathEvent (n : Nat) :
    MeasurableSet (harperPairedRelaxedLinearGuardPathEvent n) := by
  exact ((measurableSet_harperRelaxedLinearGuardPathEvent n).prod
    (measurableSet_harperRelaxedLinearGuardPathEvent n)).preimage
      (harperPairPathUnzipCLM n).measurable

/-- A coordinatewise perturbation with total budget at most one sends the
coarse guard into its fixed relaxation. -/
theorem coordinateNeighborhood_linearGuard_subset_relaxed
    {n : Nat} (epsilon : Fin n → Real)
    (hepsilon : ∀ i, 0 ≤ epsilon i)
    (hsum : (∑ i, epsilon i) ≤ 1) :
    harperPairPathCoordinateNeighborhood
        (harperPairedLinearGuardPathEvent n) epsilon ⊆
      harperPairedRelaxedLinearGuardPathEvent n := by
  intro y hy
  obtain ⟨x, hxGuard, hcoordinate⟩ := hy
  have hxPair :
      (fun i ↦ (x i).1) ∈ harperLinearGuardPathEvent n ∧
        (fun i ↦ (x i).2) ∈ harperLinearGuardPathEvent n := by
    simpa only [harperPairedLinearGuardPathEvent,
      Set.mem_preimage, Set.mem_prod, harperPairPathUnzipCLM_apply]
      using hxGuard
  have hrelaxed (b : Bool) :
      (fun i ↦ if b then (y i).2 else (y i).1) ∈
        harperRelaxedLinearGuardPathEvent n := by
    let xp : Fin n → Real := fun i ↦ if b then (x i).2 else (x i).1
    let yp : Fin n → Real := fun i ↦ if b then (y i).2 else (y i).1
    have hxp : xp ∈ harperLinearGuardPathEvent n := by
      cases b with
      | false => simpa only [xp, if_false] using hxPair.1
      | true => simpa only [xp, if_true] using hxPair.2
    have hcoord : ∀ i, |yp i - xp i| ≤ epsilon i := by
      intro i
      cases b with
      | false => simpa only [yp, xp, if_false] using (hcoordinate i).1
      | true => simpa only [yp, xp, if_true] using (hcoordinate i).2
    intro k
    have hdiff := abs_harperPathPartialSum_sub_le_total_of_coordinatewise
      hepsilon hcoord k
    have hdiff' :
        |Problem520.harperPathPartialSum yp k -
          Problem520.harperPathPartialSum xp k| ≤ 1 := hdiff.trans hsum
    have hxbounds :=
      Problem520.mem_harperPartialSumBarrierSet.mp hxp k
    have hdiffBounds := abs_le.mp hdiff'
    have hkone : (1 : Real) ≤ k.val + 1 := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : k.val + 1 ≠ 0))
    change
      -65 * (((k.val + 1 : Nat) : Real)) ≤
          Problem520.harperPathPartialSum yp k ∧
        Problem520.harperPathPartialSum yp k ≤ 2
    push_cast at hxbounds ⊢
    constructor <;> nlinarith
  change
    (fun i ↦ (y i).1) ∈ harperRelaxedLinearGuardPathEvent n ∧
      (fun i ↦ (y i).2) ∈ harperRelaxedLinearGuardPathEvent n
  exact ⟨by simpa using hrelaxed false, by simpa using hrelaxed true⟩

/-- The coarse linear guard with one unit of room on both sides. -/
def harperInteriorLinearGuardPathEvent (n : Nat) : Set (Fin n → Real) :=
  Problem520.harperPartialSumBarrierSet
    (fun k ↦ -64 * (((k.val + 1 : Nat) : Real)) + 1)
    (fun _ ↦ 0)

def harperPairedInteriorLinearGuardPathEvent (n : Nat) :
    Set (Fin n → Real × Real) :=
  harperPairPathUnzipCLM n ⁻¹'
    (harperInteriorLinearGuardPathEvent n ×ˢ
      harperInteriorLinearGuardPathEvent n)

theorem measurableSet_harperPairedInteriorLinearGuardPathEvent (n : Nat) :
    MeasurableSet (harperPairedInteriorLinearGuardPathEvent n) := by
  exact ((Problem520.measurableSet_harperPartialSumBarrierSet _ _).prod
    (Problem520.measurableSet_harperPartialSumBarrierSet _ _)).preimage
      (harperPairPathUnzipCLM n).measurable

theorem harperPairedInteriorLinearGuardPathEvent_subset_linearGuard
    (n : Nat) :
    harperPairedInteriorLinearGuardPathEvent n ⊆
      harperPairedLinearGuardPathEvent n := by
  intro x hx
  change
    (fun i ↦ (x i).1) ∈ harperLinearGuardPathEvent n ∧
      (fun i ↦ (x i).2) ∈ harperLinearGuardPathEvent n
  have hx' :
      (fun i ↦ (x i).1) ∈ harperInteriorLinearGuardPathEvent n ∧
        (fun i ↦ (x i).2) ∈ harperInteriorLinearGuardPathEvent n := by
    simpa only [harperPairedInteriorLinearGuardPathEvent,
      Set.mem_preimage, Set.mem_prod, harperPairPathUnzipCLM_apply]
      using hx
  constructor <;> intro k
  · have hk := Problem520.mem_harperPartialSumBarrierSet.mp hx'.1 k
    constructor <;> dsimp only at hk ⊢ <;> linarith
  · have hk := Problem520.mem_harperPartialSumBarrierSet.mp hx'.2 k
    constructor <;> dsimp only at hk ⊢ <;> linarith

/-- The unit total lattice enlargement exactly consumes the reserved slack
and lands in the original Gaussian guard. -/
theorem coordinateNeighborhood_interiorGuard_subset_linearGuard
    {n : Nat} (epsilon : Fin n → Real)
    (hepsilon : ∀ i, 0 ≤ epsilon i)
    (hsum : (∑ i, epsilon i) ≤ 1) :
    harperPairPathCoordinateNeighborhood
        (harperPairedInteriorLinearGuardPathEvent n) epsilon ⊆
      harperPairedLinearGuardPathEvent n := by
  intro y hy
  obtain ⟨x, hxGuard, hcoordinate⟩ := hy
  have hxPair :
      (fun i ↦ (x i).1) ∈ harperInteriorLinearGuardPathEvent n ∧
        (fun i ↦ (x i).2) ∈ harperInteriorLinearGuardPathEvent n := by
    simpa only [harperPairedInteriorLinearGuardPathEvent,
      Set.mem_preimage, Set.mem_prod, harperPairPathUnzipCLM_apply]
      using hxGuard
  have hinside (b : Bool) :
      (fun i ↦ if b then (y i).2 else (y i).1) ∈
        harperLinearGuardPathEvent n := by
    let xp : Fin n → Real := fun i ↦ if b then (x i).2 else (x i).1
    let yp : Fin n → Real := fun i ↦ if b then (y i).2 else (y i).1
    have hxp : xp ∈ harperInteriorLinearGuardPathEvent n := by
      cases b with
      | false => simpa only [xp, if_false] using hxPair.1
      | true => simpa only [xp, if_true] using hxPair.2
    have hcoord : ∀ i, |yp i - xp i| ≤ epsilon i := by
      intro i
      cases b with
      | false => simpa only [yp, xp, if_false] using (hcoordinate i).1
      | true => simpa only [yp, xp, if_true] using (hcoordinate i).2
    intro k
    have hdiff := abs_harperPathPartialSum_sub_le_total_of_coordinatewise
      hepsilon hcoord k
    have hdiff' :
        |Problem520.harperPathPartialSum yp k -
          Problem520.harperPathPartialSum xp k| ≤ 1 := hdiff.trans hsum
    have hxbounds :=
      Problem520.mem_harperPartialSumBarrierSet.mp hxp k
    have hdiffBounds := abs_le.mp hdiff'
    change
      -64 * (((k.val + 1 : Nat) : Real)) ≤
          Problem520.harperPathPartialSum yp k ∧
        Problem520.harperPathPartialSum yp k ≤ 1
    constructor <;> nlinarith
  change
    (fun i ↦ (y i).1) ∈ harperLinearGuardPathEvent n ∧
      (fun i ↦ (y i).2) ∈ harperLinearGuardPathEvent n
  exact ⟨by simpa using hinside false, by simpa using hinside true⟩

/-- The abstract Haar averaging theorem specialized to real bivariate paths.
It chooses one phase for each block and each of the two coordinates. -/
theorem exists_pairPhase_measure_shiftedPathCoreSet_ge
    {n : Nat} (mu : Measure (Fin n → Real × Real))
    [IsProbabilityMeasure mu]
    {A : Set (Fin n → Real × Real)} (hA : MeasurableSet A)
    (delta h : Fin n → Real)
    (hdelta : ∀ i, 0 ≤ delta i) (hh : ∀ i, 0 ≤ h i) (hperiod : ∀ i,
      0 < harperShiftedLatticePeriod (delta i) (h i)) :
    ∃ phi : Fin n → UnitAddCircle × UnitAddCircle,
      (∏ p : Fin n × Bool,
          ENNReal.ofReal
            (delta p.1 / harperShiftedLatticePeriod (delta p.1) (h p.1))) *
          mu A ≤
        mu (A ∩ harperShiftedPairPathCoreSet delta h phi) := by
  let c : Fin n × Bool → Real := fun p ↦
    delta p.1 / harperShiftedLatticePeriod (delta p.1) (h p.1)
  let q : (Fin n → Real × Real) → Fin n × Bool → UnitAddCircle :=
    fun omega p ↦
      if p.2 then
        (((omega p.1).2 / harperShiftedLatticePeriod (delta p.1) (h p.1) :
          Real) : UnitAddCircle)
      else
        (((omega p.1).1 / harperShiftedLatticePeriod (delta p.1) (h p.1) :
          Real) : UnitAddCircle)
  have hc0 (p : Fin n × Bool) : 0 ≤ c p := by
    dsimp only [c]
    exact div_nonneg (hdelta p.1) (le_of_lt (hperiod p.1))
  have hc1 (p : Fin n × Bool) : c p ≤ 1 := by
    dsimp only [c]
    rw [div_le_one (hperiod p.1)]
    dsimp only [harperShiftedLatticePeriod]
    linarith [hh p.1]
  have hq : Measurable q := by
    apply measurable_pi_lambda
    intro p
    by_cases hp : p.2
    · simp only [q, hp, if_true]
      apply AddCircle.measurable_mk'.comp
      exact (measurable_snd.comp (measurable_pi_apply p.1)).div_const _
    · simp only [q, hp, if_false]
      apply AddCircle.measurable_mk'.comp
      exact (measurable_fst.comp (measurable_pi_apply p.1)).div_const _
  obtain ⟨flatPhi, hflatPhi⟩ :=
    exists_phase_measure_capture_ge_product mu hA c hc0 hc1 hq
  let phi : Fin n → UnitAddCircle × UnitAddCircle := fun i ↦
    (flatPhi (i, false), flatPhi (i, true))
  refine ⟨phi, ?_⟩
  have hfiber :
      Prod.mk flatPhi ⁻¹' harperPhaseCaptureRelation A c q =
        A ∩ harperShiftedPairPathCoreSet delta h phi := by
    ext omega
    simp only [Set.mem_preimage, harperPhaseCaptureRelation,
      Set.mem_inter_iff, Set.mem_iInter, harperShiftedPairPathCoreSet,
      Set.mem_pi, Set.mem_univ, forall_const, Set.mem_prod]
    change
      (omega ∈ A ∧ ∀ p : Fin n × Bool,
        q omega p - flatPhi p ∈ harperUnitIocArc (c p)) ↔
      (omega ∈ A ∧ ∀ i : Fin n,
        (omega i).1 ∈ harperShiftedCoreUnion (delta i) (h i) (phi i).1 ∧
        (omega i).2 ∈ harperShiftedCoreUnion (delta i) (h i) (phi i).2)
    apply and_congr Iff.rfl
    constructor
    · intro hall i
      constructor
      · rw [mem_harperShiftedCoreUnion_iff (hperiod i) (hc1 (i, false))]
        exact hall (i, false)
      · rw [mem_harperShiftedCoreUnion_iff (hperiod i) (hc1 (i, true))]
        exact hall (i, true)
    · rintro hall ⟨i, b⟩
      cases b with
      | false =>
          have hcore := (hall i).1
          rw [mem_harperShiftedCoreUnion_iff
            (hperiod i) (hc1 (i, false))] at hcore
          simpa only [harperUnitCorePhaseSet, Set.mem_preimage,
            q, c, phi, if_false] using hcore
      | true =>
          have hcore := (hall i).2
          rw [mem_harperShiftedCoreUnion_iff
            (hperiod i) (hc1 (i, true))] at hcore
          simpa only [harperUnitCorePhaseSet, Set.mem_preimage,
            q, c, phi, if_true] using hcore
  simpa only [c, hfiber] using hflatPhi

/-- Real-valued form of simultaneous phase averaging.  This is convenient
for composing with the local relative estimates, which are stated using
`Measure.real`. -/
theorem exists_pairPhase_measureReal_shiftedPathCoreSet_ge
    {n : Nat} (mu : Measure (Fin n → Real × Real))
    [IsProbabilityMeasure mu]
    {A : Set (Fin n → Real × Real)} (hA : MeasurableSet A)
    (delta h : Fin n → Real)
    (hdelta : ∀ i, 0 ≤ delta i) (hh : ∀ i, 0 ≤ h i) (hperiod : ∀ i,
      0 < harperShiftedLatticePeriod (delta i) (h i)) :
    ∃ phi : Fin n → UnitAddCircle × UnitAddCircle,
      (∏ p : Fin n × Bool,
          delta p.1 / harperShiftedLatticePeriod (delta p.1) (h p.1)) *
          mu.real A ≤
        mu.real (A ∩ harperShiftedPairPathCoreSet delta h phi) := by
  obtain ⟨phi, hphi⟩ :=
    exists_pairPhase_measure_shiftedPathCoreSet_ge mu hA delta h
      hdelta hh hperiod
  refine ⟨phi, ?_⟩
  have hleftFinite :
      (∏ p : Fin n × Bool,
          ENNReal.ofReal
            (delta p.1 / harperShiftedLatticePeriod
              (delta p.1) (h p.1))) * mu A ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.prod_ne_top fun _ _ ↦ ENNReal.ofReal_ne_top
    · exact measure_ne_top mu A
  have hrightFinite :
      mu (A ∩ harperShiftedPairPathCoreSet delta h phi) ≠ ∞ :=
    measure_ne_top _ _
  have hreal :=
    ENNReal.toReal_le_toReal hleftFinite hrightFinite |>.mpr hphi
  rw [ENNReal.toReal_mul, ENNReal.toReal_prod] at hreal
  simp only [ENNReal.toReal_ofReal
    (div_nonneg (hdelta _) (le_of_lt (hperiod _))), Measure.real] at hreal
  exact hreal

/-- Distinct integer index vectors give disjoint full path cells. -/
theorem pairwiseDisjoint_harperShiftedPairPathFullCell {n : Nat}
    {delta h : Fin n → Real}
    (phi : Fin n → UnitAddCircle × UnitAddCircle)
    (hperiod : ∀ i, 0 < harperShiftedLatticePeriod (delta i) (h i)) :
    Pairwise (fun z w : Fin n → Int × Int ↦
      Disjoint (harperShiftedPairPathFullCell delta h phi z)
        (harperShiftedPairPathFullCell delta h phi w)) := by
  intro z w hzw
  rw [harperShiftedPairPathFullCell, harperShiftedPairPathFullCell,
    disjoint_univ_pi]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hzw
  have hor : (z i).1 ≠ (w i).1 ∨ (z i).2 ≠ (w i).2 := by
    contrapose! hi
    exact Prod.ext hi.1 hi.2
  refine ⟨i, ?_⟩
  rcases hor with hfirst | hsecond
  · exact (pairwiseDisjoint_harperShiftedFullCell (phi i).1 (hperiod i)
      hfirst).set_prod_left
        (harperShiftedFullCell (delta i) (h i) (phi i).2 (z i).2)
        (harperShiftedFullCell (delta i) (h i) (phi i).2 (w i).2)
  · exact (pairwiseDisjoint_harperShiftedFullCell (phi i).2 (hperiod i)
      hsecond).set_prod_right
        (harperShiftedFullCell (delta i) (h i) (phi i).1 (z i).1)
        (harperShiftedFullCell (delta i) (h i) (phi i).1 (w i).1)

/-- Product-law mass of a shifted bivariate path cell is the product of its
one-block masses. -/
theorem measureReal_pi_harperShiftedPairPathCoreCell {n : Nat}
    (rho : Fin n → Measure (Real × Real))
    [∀ i, SigmaFinite (rho i)]
    (delta h : Fin n → Real)
    (phi : Fin n → UnitAddCircle × UnitAddCircle)
    (z : Fin n → Int × Int) :
    (Measure.pi rho).real (harperShiftedPairPathCoreCell delta h phi z) =
      ∏ i, (rho i).real
        (harperShiftedPairCoreCell (delta i) (h i) (phi i) (z i)) := by
  rw [Measure.real, harperShiftedPairPathCoreCell, Measure.pi_pi,
    ENNReal.toReal_prod]
  rfl

theorem measureReal_pi_harperShiftedPairPathFullCell {n : Nat}
    (nu : Fin n → Measure (Real × Real))
    [∀ i, SigmaFinite (nu i)]
    (delta h : Fin n → Real)
    (phi : Fin n → UnitAddCircle × UnitAddCircle)
    (z : Fin n → Int × Int) :
    (Measure.pi nu).real (harperShiftedPairPathFullCell delta h phi z) =
      ∏ i, (nu i).real
        (harperShiftedPairFullCell (delta i) (h i) (phi i) (z i)) := by
  rw [Measure.real, harperShiftedPairPathFullCell, Measure.pi_pi,
    ENNReal.toReal_prod]
  rfl

/-- Coordinatewise bivariate comparisons multiply without any cell-count
loss. -/
theorem measureReal_pi_shiftedPairPathCoreCell_le_prod_mul_fullCell
    {n : Nat}
    (rho nu : Fin n → Measure (Real × Real))
    [∀ i, SigmaFinite (rho i)] [∀ i, SigmaFinite (nu i)]
    (A B delta h : Fin n → Real)
    (phi : Fin n → UnitAddCircle × UnitAddCircle)
    (z : Fin n → Int × Int)
    (hA : ∀ i, 0 ≤ A i)
    (hcell : ∀ i,
      A i * (rho i).real
          (harperShiftedPairCoreCell (delta i) (h i) (phi i) (z i)) ≤
        B i * (nu i).real
          (harperShiftedPairFullCell (delta i) (h i) (phi i) (z i))) :
    (∏ i, A i) *
        (Measure.pi rho).real
          (harperShiftedPairPathCoreCell delta h phi z) ≤
      (∏ i, B i) *
        (Measure.pi nu).real
          (harperShiftedPairPathFullCell delta h phi z) := by
  rw [measureReal_pi_harperShiftedPairPathCoreCell,
    measureReal_pi_harperShiftedPairPathFullCell,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod
    (fun i _hi ↦ mul_nonneg (hA i) measureReal_nonneg)
    (fun i _hi ↦ hcell i)

/-- A finite family of core cells may be union-bounded on the actual side;
the disjoint full lattice sums exactly on the Gaussian side. -/
theorem measureReal_biUnion_shiftedPairPathCoreCell_le_prod_mul_fullCell
    {n : Nat}
    (rho nu : Fin n → Measure (Real × Real))
    [∀ i, IsFiniteMeasure (rho i)] [∀ i, IsFiniteMeasure (nu i)]
    (A B delta h : Fin n → Real)
    (phi : Fin n → UnitAddCircle × UnitAddCircle)
    (s : Finset (Fin n → Int × Int))
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (hperiod : ∀ i, 0 < harperShiftedLatticePeriod (delta i) (h i))
    (hcell : ∀ z ∈ s, ∀ i,
      A i * (rho i).real
          (harperShiftedPairCoreCell (delta i) (h i) (phi i) (z i)) ≤
        B i * (nu i).real
          (harperShiftedPairFullCell (delta i) (h i) (phi i) (z i))) :
    (∏ i, A i) * (Measure.pi rho).real
        (⋃ z ∈ s, harperShiftedPairPathCoreCell delta h phi z) ≤
      (∏ i, B i) * (Measure.pi nu).real
        (⋃ z ∈ s, harperShiftedPairPathFullCell delta h phi z) := by
  let AP : Real := ∏ i, A i
  let BP : Real := ∏ i, B i
  have hAP : 0 ≤ AP := Finset.prod_nonneg fun i _hi ↦ hA i
  have hBP : 0 ≤ BP := Finset.prod_nonneg fun i _hi ↦ hB i
  calc
    AP * (Measure.pi rho).real
          (⋃ z ∈ s, harperShiftedPairPathCoreCell delta h phi z) ≤
        AP * ∑ z ∈ s, (Measure.pi rho).real
          (harperShiftedPairPathCoreCell delta h phi z) := by
      gcongr
      exact measureReal_biUnion_finset_le s _
    _ = ∑ z ∈ s, AP * (Measure.pi rho).real
          (harperShiftedPairPathCoreCell delta h phi z) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ z ∈ s, BP * (Measure.pi nu).real
          (harperShiftedPairPathFullCell delta h phi z) := by
      apply Finset.sum_le_sum
      intro z hz
      exact measureReal_pi_shiftedPairPathCoreCell_le_prod_mul_fullCell
        rho nu A B delta h phi z hA (hcell z hz)
    _ = BP * ∑ z ∈ s, (Measure.pi nu).real
          (harperShiftedPairPathFullCell delta h phi z) := by
      rw [Finset.mul_sum]
    _ = BP * (Measure.pi nu).real
          (⋃ z ∈ s, harperShiftedPairPathFullCell delta h phi z) := by
      congr 1
      rw [measureReal_biUnion_finset]
      · exact (pairwiseDisjoint_harperShiftedPairPathFullCell phi hperiod).set_pairwise s
      · exact fun z _hz ↦
          measurableSet_harperShiftedPairPathFullCell delta h phi z

/-! ## Scheduled specialization -/

/-- The radius by which the local bivariate Fejer comparison enlarges each
real coordinate. -/
def harperScheduledBivariateExpansionRadius (j : Nat) : Real :=
  2 * (Real.sqrt (Problem520.harperScheduledStrongComparisonFrequency j) /
    (Problem520.harperScheduledStrongComparisonFrequency j / 2))

theorem harperScheduledBivariateExpansionRadius_pos (j : Nat) :
    0 < harperScheduledBivariateExpansionRadius j := by
  unfold harperScheduledBivariateExpansionRadius
  have hF := Problem520.harperScheduledStrongComparisonFrequency_pos j
  positivity

theorem harperScheduledBivariateExpansionRadius_eq_four_div_sqrt
    (j : Nat) :
    harperScheduledBivariateExpansionRadius j =
      4 / Real.sqrt
        (Problem520.harperScheduledStrongComparisonFrequency j) := by
  let F := Problem520.harperScheduledStrongComparisonFrequency j
  have hF : 0 < F :=
    Problem520.harperScheduledStrongComparisonFrequency_pos j
  have hsqrt : 0 < Real.sqrt F := Real.sqrt_pos.2 hF
  have hsq : (Real.sqrt F) ^ (2 : Nat) = F := Real.sq_sqrt hF.le
  unfold harperScheduledBivariateExpansionRadius
  change 2 * (Real.sqrt F / (F / 2)) = 4 / Real.sqrt F
  field_simp
  nlinarith

/-- The square root of the doubly exponential frequency has a literal power
of two form one schedule step later. -/
theorem sqrt_harperScheduledStrongComparisonFrequency_succ (j : Nat) :
    Real.sqrt
        (Problem520.harperScheduledStrongComparisonFrequency (j + 1)) =
      (2 : Real) ^ (2 ^ j) := by
  unfold Problem520.harperScheduledStrongComparisonFrequency
  have hexponent : 2 ^ (j + 1) = 2 ^ j * 2 := by omega
  rw [hexponent, pow_mul, Real.sqrt_sq_eq_abs]
  exact abs_of_pos (by positivity)

private theorem two_mul_nat_le_two_pow_pred {j : Nat} (hj : 6 ≤ j) :
    2 * j ≤ 2 ^ (j - 1) := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
      rw [show j + 1 - 1 = (j - 1) + 1 by omega, pow_succ]
      omega

private theorem succ_sq_nat_le_two_pow {j : Nat} (hj : 6 ≤ j) :
    (j + 1) ^ 2 ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
      have hsquare : (j + 1 + 1) ^ 2 ≤ 2 * (j + 1) ^ 2 := by
        nlinarith
      have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by
        rw [pow_succ]
        omega
      rw [hpow]
      exact hsquare.trans (Nat.mul_le_mul_left 2 ih)

theorem four_pow_le_sqrt_harperScheduledStrongComparisonFrequency
    {j : Nat} (hj : 6 ≤ j) :
    (4 : Real) ^ j ≤
      Real.sqrt (Problem520.harperScheduledStrongComparisonFrequency j) := by
  have hjpos : 0 < j := by omega
  have hsqrt := sqrt_harperScheduledStrongComparisonFrequency_succ (j - 1)
  rw [show j - 1 + 1 = j by omega] at hsqrt
  rw [hsqrt]
  have hexponent := two_mul_nat_le_two_pow_pred hj
  calc
    (4 : Real) ^ j = (2 : Real) ^ (2 * j) := by
      rw [show (4 : Real) = 2 ^ 2 by norm_num, pow_mul]
    _ ≤ (2 : Real) ^ (2 ^ (j - 1)) :=
      pow_le_pow_right₀ (by norm_num) (by exact_mod_cast hexponent)

theorem harperScheduledBivariateExpansionRadius_le_four_mul_quarter_pow
    {j : Nat} (hj : 6 ≤ j) :
    harperScheduledBivariateExpansionRadius j ≤
      4 * (1 / 4 : Real) ^ j := by
  rw [harperScheduledBivariateExpansionRadius_eq_four_div_sqrt]
  have hsqrtPos := Real.sqrt_pos.2
    (Problem520.harperScheduledStrongComparisonFrequency_pos j)
  have hfourPos : 0 < (4 : Real) ^ j := by positivity
  have hden := four_pow_le_sqrt_harperScheduledStrongComparisonFrequency hj
  calc
    4 / Real.sqrt
        (Problem520.harperScheduledStrongComparisonFrequency j) ≤
        4 / (4 : Real) ^ j := by
      exact div_le_div_of_nonneg_left (by norm_num) hfourPos hden
    _ = 4 * (1 / 4 : Real) ^ j := by
      rw [one_div_pow]
      ring

private theorem sum_range_half_pow_le_two (n : Nat) :
    (∑ i ∈ Finset.range n, (1 / 2 : Real) ^ i) ≤ 2 := by
  have hgeom := geom_sum_mul_neg (1 / 2 : Real) n
  have hpow : 0 ≤ (1 / 2 : Real) ^ n := by positivity
  norm_num at hgeom ⊢
  nlinarith

theorem sum_fin_half_pow_shift_le (start n : Nat) :
    (∑ i : Fin n, (1 / 2 : Real) ^ (start + i.val)) ≤
      2 * (1 / 2 : Real) ^ start := by
  calc
    (∑ i : Fin n, (1 / 2 : Real) ^ (start + i.val)) =
        ∑ i ∈ Finset.range n, (1 / 2 : Real) ^ (start + i) :=
      by
        simpa only using
          (Fin.sum_univ_eq_sum_range
            (fun i : Nat ↦ (1 / 2 : Real) ^ (start + i)) n)
    _ = (1 / 2 : Real) ^ start *
        ∑ i ∈ Finset.range n, (1 / 2 : Real) ^ i := by
      simp_rw [pow_add]
      rw [Finset.mul_sum]
    _ ≤ (1 / 2 : Real) ^ start * 2 :=
      mul_le_mul_of_nonneg_left (sum_range_half_pow_le_two n) (by positivity)
    _ = 2 * (1 / 2 : Real) ^ start := by ring

private theorem scheduled_moderate_linear_nat_bound (i : Nat) :
    (4096 * (i + 1) + 80) ^ 2 ≤ 2 ^ (30 + i) := by
  by_cases hi : i < 2
  · interval_cases i <;> norm_num
  · have hi2 : 2 ≤ i := by omega
    induction i, hi2 using Nat.le_induction with
    | base => norm_num
    | succ i hi ih =>
        have hgrowth :
            (4096 * (i + 1 + 1) + 80) ^ 2 ≤
              2 * (4096 * (i + 1) + 80) ^ 2 := by
          nlinarith
        calc
          (4096 * (i + 1 + 1) + 80) ^ 2 ≤
              2 * (4096 * (i + 1) + 80) ^ 2 := hgrowth
          _ ≤ 2 * 2 ^ (30 + i) :=
            Nat.mul_le_mul_left 2 (ih (by omega))
          _ = 2 ^ (30 + (i + 1)) := by
            rw [show 30 + (i + 1) = (30 + i) + 1 by omega, pow_succ]
            omega

/-- From schedule block 30 onward, the local Gaussian moderate window
uniformly contains the linear path-coordinate envelope. -/
theorem harperScheduled_linearEnvelope_le_moderateWindow
    {start : Nat} (hstart : 30 ≤ start) (i : Nat) :
    256 * (((i + 1 : Nat) : Real)) + 5 ≤
      (1 / 16 : Real) *
        Real.sqrt (((2 ^ (start + i) : Nat) : Real)) := by
  have hnatBase := scheduled_moderate_linear_nat_bound i
  have hexponent : 30 + i ≤ start + i := by omega
  have hnatPow : 2 ^ (30 + i) ≤ 2 ^ (start + i) :=
    Nat.pow_le_pow_right (by norm_num) hexponent
  have hnat : (4096 * (i + 1) + 80) ^ 2 ≤ 2 ^ (start + i) :=
    hnatBase.trans hnatPow
  have hreal :
      ((4096 * (i + 1) + 80 : Nat) : Real) ^ 2 ≤
        ((2 ^ (start + i) : Nat) : Real) := by exact_mod_cast hnat
  have hsqrt :
      (16 : Real) * (256 * (((i + 1 : Nat) : Real)) + 5) ≤
        Real.sqrt (((2 ^ (start + i) : Nat) : Real)) := by
    apply Real.le_sqrt_of_sq_le
    convert hreal using 1 <;> push_cast <;> ring
  nlinarith

/-- Every scheduled cell meeting the interior guard is automatically inside
the local relative-comparison moderate window. -/
theorem harperScheduled_activeInteriorCells_moderate
    {start n : Nat} (hstart : 30 ≤ start)
    (phi : Fin n → UnitAddCircle × UnitAddCircle)
    (active : Finset (Fin n → Int × Int))
    (hmeets : ∀ z ∈ active,
      Set.Nonempty
        (harperPairedInteriorLinearGuardPathEvent n ∩
          harperShiftedPairPathCoreCell
            (fun i ↦
              Problem520.harperScheduledRelativeIntervalWidth
                (start + i.val))
            (fun i ↦ harperScheduledBivariateExpansionRadius
              (start + i.val)) phi z)) :
    ∀ z ∈ active, ∀ i,
      let j := start + i.val
      let delta := Problem520.harperScheduledRelativeIntervalWidth j
      let h := harperScheduledBivariateExpansionRadius j
      let a := ((z i).1 : Real) +
        harperUnitPhaseRepresentative (phi i).1
      let b := ((z i).2 : Real) +
        harperUnitPhaseRepresentative (phi i).2
      |a * harperShiftedLatticePeriod delta h| +
          |b * harperShiftedLatticePeriod delta h| + 3 ≤
        (1 / 16 : Real) *
          Real.sqrt (((2 ^ j : Nat) : Real)) := by
  intro z hz i
  dsimp only
  obtain ⟨x, hxInterior, hxCell⟩ := hmeets z hz
  have hxLinear :=
    harperPairedInteriorLinearGuardPathEvent_subset_linearGuard n hxInterior
  have hxPair :
      (fun i ↦ (x i).1) ∈ harperLinearGuardPathEvent n ∧
        (fun i ↦ (x i).2) ∈ harperLinearGuardPathEvent n := by
    simpa only [harperPairedLinearGuardPathEvent,
      Set.mem_preimage, Set.mem_prod, harperPairPathUnzipCLM_apply]
      using hxLinear
  have hxAll : ∀ i,
      (x i).1 ∈ harperShiftedCoreCell
          (Problem520.harperScheduledRelativeIntervalWidth
            (start + i.val))
          (harperScheduledBivariateExpansionRadius (start + i.val))
          (phi i).1 (z i).1 ∧
        (x i).2 ∈ harperShiftedCoreCell
          (Problem520.harperScheduledRelativeIntervalWidth
            (start + i.val))
          (harperScheduledBivariateExpansionRadius (start + i.val))
          (phi i).2 (z i).2 := by
    simpa only [harperShiftedPairPathCoreCell, Set.mem_pi,
      Set.mem_univ, forall_const, harperShiftedPairCoreCell,
      Set.mem_prod] using hxCell
  have hxFirst := abs_coordinate_le_of_linear_partialSum_guard
    (fun i ↦ (x i).1)
    (fun k ↦ (Problem520.mem_harperPartialSumBarrierSet.mp hxPair.1 k).1)
    (fun k ↦ (Problem520.mem_harperPartialSumBarrierSet.mp hxPair.1 k).2) i
  have hxSecond := abs_coordinate_le_of_linear_partialSum_guard
    (fun i ↦ (x i).2)
    (fun k ↦ (Problem520.mem_harperPartialSumBarrierSet.mp hxPair.2 k).1)
    (fun k ↦ (Problem520.mem_harperPartialSumBarrierSet.mp hxPair.2 k).2) i
  let delta := Problem520.harperScheduledRelativeIntervalWidth
    (start + i.val)
  let h := harperScheduledBivariateExpansionRadius (start + i.val)
  have hdelta : 0 ≤ delta :=
    (Problem520.harperScheduledRelativeIntervalWidth_pos _).le
  have hdeltaOne : delta ≤ 1 :=
    Problem520.harperScheduledRelativeIntervalWidth_le_one _
  have ha := abs_shiftedCoreCell_lower_le_abs_add_delta hdelta (hxAll i).1
  have hb := abs_shiftedCoreCell_lower_le_abs_add_delta hdelta (hxAll i).2
  have henvelope := harperScheduled_linearEnvelope_le_moderateWindow
    hstart i.val
  dsimp only [delta, h] at ha hb ⊢
  calc
    |(((z i).1 : Real) + harperUnitPhaseRepresentative (phi i).1) *
          harperShiftedLatticePeriod
            (Problem520.harperScheduledRelativeIntervalWidth
              (start + i.val))
            (harperScheduledBivariateExpansionRadius (start + i.val))| +
        |(((z i).2 : Real) + harperUnitPhaseRepresentative (phi i).2) *
          harperShiftedLatticePeriod
            (Problem520.harperScheduledRelativeIntervalWidth
              (start + i.val))
            (harperScheduledBivariateExpansionRadius (start + i.val))| + 3 ≤
        256 * (((i.val + 1 : Nat) : Real)) + 5 := by
      nlinarith
    _ ≤ (1 / 16 : Real) *
        Real.sqrt (((2 ^ (start + i.val) : Nat) : Real)) := henvelope

theorem harperScheduled_coreFraction_defect_le_halfPow
    {j : Nat} (hj : 6 ≤ j) :
    1 - Problem520.harperScheduledRelativeIntervalWidth j /
          harperShiftedLatticePeriod
            (Problem520.harperScheduledRelativeIntervalWidth j)
            (harperScheduledBivariateExpansionRadius j) ≤
      8 * (1 / 2 : Real) ^ j := by
  let delta := Problem520.harperScheduledRelativeIntervalWidth j
  let h := harperScheduledBivariateExpansionRadius j
  have hdelta : 0 < delta :=
    Problem520.harperScheduledRelativeIntervalWidth_pos j
  have hh : 0 < h := harperScheduledBivariateExpansionRadius_pos j
  have hperiod : 0 < harperShiftedLatticePeriod delta h := by
    unfold harperShiftedLatticePeriod
    positivity
  have hexpansion : h ≤ 4 * (1 / 4 : Real) ^ j :=
    harperScheduledBivariateExpansionRadius_le_four_mul_quarter_pow hj
  have hsquareNat := succ_sq_nat_le_two_pow hj
  have hsquareReal : ((((j + 1 : Nat) : Real)) ^ 2) ≤
      (2 : Real) ^ j := by exact_mod_cast hsquareNat
  have hratio : 2 * h / delta ≤ 8 * (1 / 2 : Real) ^ j := by
    dsimp only [delta]
    unfold Problem520.harperScheduledRelativeIntervalWidth
    rw [div_inv_eq_mul]
    calc
      2 * h * (((j + 1 : Nat) : Real) ^ 2) ≤
          2 * (4 * (1 / 4 : Real) ^ j) *
            (((j + 1 : Nat) : Real) ^ 2) := by
        gcongr
      _ ≤ 2 * (4 * (1 / 4 : Real) ^ j) * (2 : Real) ^ j := by
        gcongr
      _ = 8 * (1 / 2 : Real) ^ j := by
        calc
          2 * (4 * (1 / 4 : Real) ^ j) * (2 : Real) ^ j =
              8 * ((1 / 4 : Real) ^ j * (2 : Real) ^ j) := by ring
          _ = 8 * ((1 / 4 : Real) * 2) ^ j := by rw [mul_pow]
          _ = 8 * (1 / 2 : Real) ^ j := by norm_num
  have hidentity :
      1 - delta / harperShiftedLatticePeriod delta h =
        2 * h / harperShiftedLatticePeriod delta h := by
    unfold harperShiftedLatticePeriod
    field_simp
    ring
  change 1 - delta / harperShiftedLatticePeriod delta h ≤ _
  rw [hidentity]
  exact (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hh.le)
    hdelta (by
      unfold harperShiftedLatticePeriod
      linarith)).trans hratio

/-- Uniform Haar retention: from block six onward, all two-coordinate core
fractions together retain at least one half of the event, independently of
the path length. -/
theorem one_half_le_prod_harperScheduled_coreFractions
    {start n : Nat} (hstart : 6 ≤ start) :
    (1 / 2 : Real) ≤
      ∏ p : Fin n × Bool,
        Problem520.harperScheduledRelativeIntervalWidth (start + p.1.val) /
          harperShiftedLatticePeriod
            (Problem520.harperScheduledRelativeIntervalWidth
              (start + p.1.val))
            (harperScheduledBivariateExpansionRadius
              (start + p.1.val)) := by
  let x : Fin n × Bool → Real := fun p ↦
    8 * (1 / 2 : Real) ^ (start + p.1.val)
  let fraction : Fin n × Bool → Real := fun p ↦
    Problem520.harperScheduledRelativeIntervalWidth (start + p.1.val) /
      harperShiftedLatticePeriod
        (Problem520.harperScheduledRelativeIntervalWidth
          (start + p.1.val))
        (harperScheduledBivariateExpansionRadius (start + p.1.val))
  have hx0 (p : Fin n × Bool) : 0 ≤ x p := by
    dsimp only [x]
    positivity
  have hx1 (p : Fin n × Bool) : x p ≤ 1 := by
    dsimp only [x]
    have hp : (1 / 2 : Real) ^ (start + p.1.val) ≤
        (1 / 2 : Real) ^ 6 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    norm_num at hp ⊢
    linarith
  have hfraction0 (p : Fin n × Bool) : 0 ≤ fraction p := by
    dsimp only [fraction]
    exact div_nonneg
      (Problem520.harperScheduledRelativeIntervalWidth_pos _).le
      (by
        unfold harperShiftedLatticePeriod
        exact add_nonneg
          (Problem520.harperScheduledRelativeIntervalWidth_pos _).le
          (mul_nonneg (by norm_num)
            (harperScheduledBivariateExpansionRadius_pos _).le))
  have hterm (p : Fin n × Bool) : 1 - x p ≤ fraction p := by
    have hdefect := harperScheduled_coreFraction_defect_le_halfPow
      (j := start + p.1.val) (by omega)
    dsimp only [x, fraction]
    linarith
  have hsum : (∑ p : Fin n × Bool, x p) ≤ 1 / 2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_bool]
    simp only [x]
    have hhalf := sum_fin_half_pow_shift_le start n
    calc
      (∑ i : Fin n,
          (8 * (1 / 2 : Real) ^ (start + i.val) +
            8 * (1 / 2 : Real) ^ (start + i.val))) =
          16 * ∑ i : Fin n, (1 / 2 : Real) ^ (start + i.val) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ ≤ 16 * (2 * (1 / 2 : Real) ^ start) := by
        gcongr
      _ ≤ 1 / 2 := by
        have hp : (1 / 2 : Real) ^ start ≤ (1 / 2 : Real) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hstart
        norm_num at hp ⊢
        linarith
  have honeSub := one_sub_sum_le_prod_one_sub
    (Finset.univ : Finset (Fin n × Bool)) x
    (fun p _hp ↦ hx0 p) (fun p _hp ↦ hx1 p)
  have hprodCompare :
      (∏ p : Fin n × Bool, (1 - x p)) ≤ ∏ p, fraction p := by
    apply Finset.prod_le_prod
    · intro p _hp
      exact sub_nonneg.mpr (hx1 p)
    · intro p _hp
      exact hterm p
  change (1 / 2 : Real) ≤ ∏ p, fraction p
  calc
    (1 / 2 : Real) ≤ 1 - ∑ p : Fin n × Bool, x p := by linarith
    _ ≤ ∏ p : Fin n × Bool, (1 - x p) := honeSub
    _ ≤ ∏ p, fraction p := hprodCompare

theorem harperScheduled_retention_defect_le_halfPow
    {j : Nat} (hj : 6 ≤ j) :
    1 - (1 - 2 / Real.sqrt
          (Problem520.harperScheduledStrongComparisonFrequency j)) ^
            (2 : Nat) ≤
      4 * (1 / 2 : Real) ^ j := by
  let root := Real.sqrt
    (Problem520.harperScheduledStrongComparisonFrequency j)
  let a := 2 / root
  have hroot : 0 < root := Real.sqrt_pos.2
    (Problem520.harperScheduledStrongComparisonFrequency_pos j)
  have hfour : (4 : Real) ^ j ≤ root := by
    exact four_pow_le_sqrt_harperScheduledStrongComparisonFrequency hj
  have hfourPos : 0 < (4 : Real) ^ j := by positivity
  have ha0 : 0 ≤ a := div_nonneg (by norm_num) hroot.le
  have ha1 : a ≤ 1 := by
    have hrootTwo : 2 ≤ root := by
      calc
        (2 : Real) ≤ 4 ^ j := by
          have : (1 : Nat) ≤ j := by omega
          have hpow : (4 : Real) ^ 1 ≤ 4 ^ j :=
            pow_le_pow_right₀ (by norm_num) this
          norm_num at hpow
          exact (show (2 : Real) ≤ 4 from by norm_num).trans hpow
        _ ≤ root := hfour
    exact (div_le_one hroot).2 hrootTwo
  have hdiv : 4 / root ≤ 4 * (1 / 2 : Real) ^ j := by
    calc
      4 / root ≤ 4 / (4 : Real) ^ j :=
        div_le_div_of_nonneg_left (by norm_num) hfourPos hfour
      _ = 4 * (1 / 4 : Real) ^ j := by
        rw [one_div_pow]
        ring
      _ ≤ 4 * (1 / 2 : Real) ^ j := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀
            (by norm_num : 0 ≤ (1 / 4 : Real))
            (by norm_num : (1 / 4 : Real) ≤ 1 / 2) j)
          (by norm_num)
  change 1 - (1 - a) ^ (2 : Nat) ≤ _
  calc
    1 - (1 - a) ^ (2 : Nat) ≤ 2 * a := by
      nlinarith [sq_nonneg a]
    _ = 4 / root := by
      dsimp only [a]
      ring
    _ ≤ 4 * (1 / 2 : Real) ^ j := hdiv

/-- The multiplicative Fejer retention factors also have a uniform positive
tail product. -/
theorem one_half_le_prod_harperScheduled_retentions
    {start n : Nat} (hstart : 6 ≤ start) :
    (1 / 2 : Real) ≤
      ∏ i : Fin n,
        (1 - 2 / Real.sqrt
          (Problem520.harperScheduledStrongComparisonFrequency
            (start + i.val))) ^ (2 : Nat) := by
  let x : Fin n → Real := fun i ↦
    4 * (1 / 2 : Real) ^ (start + i.val)
  let retention : Fin n → Real := fun i ↦
    (1 - 2 / Real.sqrt
      (Problem520.harperScheduledStrongComparisonFrequency
        (start + i.val))) ^ (2 : Nat)
  have hx0 (i : Fin n) : 0 ≤ x i := by
    dsimp only [x]
    positivity
  have hx1 (i : Fin n) : x i ≤ 1 := by
    dsimp only [x]
    have hp : (1 / 2 : Real) ^ (start + i.val) ≤
        (1 / 2 : Real) ^ 6 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    norm_num at hp ⊢
    linarith
  have hterm (i : Fin n) : 1 - x i ≤ retention i := by
    have hdefect := harperScheduled_retention_defect_le_halfPow
      (j := start + i.val) (by omega)
    dsimp only [x, retention]
    linarith
  have hsum : (∑ i : Fin n, x i) ≤ 1 / 2 := by
    have hhalf := sum_fin_half_pow_shift_le start n
    dsimp only [x]
    rw [← Finset.mul_sum]
    calc
      4 * ∑ i : Fin n, (1 / 2 : Real) ^ (start + i.val) ≤
          4 * (2 * (1 / 2 : Real) ^ start) := by gcongr
      _ ≤ 1 / 2 := by
        have hp : (1 / 2 : Real) ^ start ≤ (1 / 2 : Real) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hstart
        norm_num at hp ⊢
        linarith
  have honeSub := one_sub_sum_le_prod_one_sub
    (Finset.univ : Finset (Fin n)) x
    (fun i _hi ↦ hx0 i) (fun i _hi ↦ hx1 i)
  have hprodCompare :
      (∏ i : Fin n, (1 - x i)) ≤ ∏ i, retention i := by
    apply Finset.prod_le_prod
    · intro i _hi
      exact sub_nonneg.mpr (hx1 i)
    · intro i _hi
      exact hterm i
  change (1 / 2 : Real) ≤ ∏ i, retention i
  calc
    (1 / 2 : Real) ≤ 1 - ∑ i : Fin n, x i := by linarith
    _ ≤ ∏ i : Fin n, (1 - x i) := honeSub
    _ ≤ ∏ i, retention i := hprodCompare

/-- The local relative losses multiply to one absolute constant. -/
theorem prod_harperScheduled_twoHeightLoss_le_exp_four
    (start n : Nat) :
    (∏ i : Fin n,
      (1 + 2 * Problem520.harperScheduledRelativeIntervalWidth
        (start + i.val))) ≤ Real.exp 4 := by
  calc
    (∏ i : Fin n,
        (1 + 2 * Problem520.harperScheduledRelativeIntervalWidth
          (start + i.val))) ≤
        ∏ i : Fin n,
          Real.exp (2 * Problem520.harperScheduledRelativeIntervalWidth
            (start + i.val)) := by
      apply Finset.prod_le_prod
      · intro i _hi
        have hd := Problem520.harperScheduledRelativeIntervalWidth_pos
          (start + i.val)
        linarith
      · intro i _hi
        simpa only [add_comm] using Real.add_one_le_exp
          (2 * Problem520.harperScheduledRelativeIntervalWidth
            (start + i.val))
    _ = Real.exp (∑ i : Fin n,
        2 * Problem520.harperScheduledRelativeIntervalWidth
          (start + i.val)) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp 4 := by
      apply Real.exp_le_exp.mpr
      rw [← Finset.mul_sum]
      have hsum :=
        Problem520.sum_fin_harperScheduledRelativeIntervalWidth_le_two
          start n
      linarith

/-- Numerical discharge of all three path-composition products. -/
theorem le_four_mul_exp_four_of_harperScheduled_products
    {start n : Nat} (hstart : 6 ≤ start) {P Q : Real}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hcompare :
      ((∏ i : Fin n,
          (1 - 2 / Real.sqrt
            (Problem520.harperScheduledStrongComparisonFrequency
              (start + i.val))) ^ (2 : Nat)) *
        (∏ p : Fin n × Bool,
          Problem520.harperScheduledRelativeIntervalWidth
              (start + p.1.val) /
            harperShiftedLatticePeriod
              (Problem520.harperScheduledRelativeIntervalWidth
                (start + p.1.val))
              (harperScheduledBivariateExpansionRadius
                (start + p.1.val)))) * P ≤
        (∏ i : Fin n,
          (1 + 2 * Problem520.harperScheduledRelativeIntervalWidth
            (start + i.val))) * Q) :
    P ≤ 4 * Real.exp 4 * Q := by
  let retention : Real := ∏ i : Fin n,
    (1 - 2 / Real.sqrt
      (Problem520.harperScheduledStrongComparisonFrequency
        (start + i.val))) ^ (2 : Nat)
  let core : Real := ∏ p : Fin n × Bool,
    Problem520.harperScheduledRelativeIntervalWidth (start + p.1.val) /
      harperShiftedLatticePeriod
        (Problem520.harperScheduledRelativeIntervalWidth
          (start + p.1.val))
        (harperScheduledBivariateExpansionRadius (start + p.1.val))
  let loss : Real := ∏ i : Fin n,
    (1 + 2 * Problem520.harperScheduledRelativeIntervalWidth
      (start + i.val))
  have hretention : (1 / 2 : Real) ≤ retention :=
    one_half_le_prod_harperScheduled_retentions hstart
  have hcore : (1 / 2 : Real) ≤ core :=
    one_half_le_prod_harperScheduled_coreFractions hstart
  have hloss : loss ≤ Real.exp 4 :=
    prod_harperScheduled_twoHeightLoss_le_exp_four start n
  have hquarter : (1 / 4 : Real) ≤ retention * core := by
    have hr0 : 0 ≤ retention := (by norm_num : (0 : Real) ≤ 1 / 2).trans hretention
    have hc0 : 0 ≤ core := (by norm_num : (0 : Real) ≤ 1 / 2).trans hcore
    nlinarith [mul_nonneg hr0 hc0]
  have hleft : (1 / 4 : Real) * P ≤ (retention * core) * P :=
    mul_le_mul_of_nonneg_right hquarter hP
  have hright : loss * Q ≤ Real.exp 4 * Q :=
    mul_le_mul_of_nonneg_right hloss hQ
  have hchain : (1 / 4 : Real) * P ≤ Real.exp 4 * Q := by
    exact hleft.trans (hcompare.trans hright)
  nlinarith

/-- The total coordinate enlargement along every late scheduled path is less
than one. -/
theorem sum_harperScheduled_shiftedLatticePeriod_le_one
    {start n : Nat} (hstart : 6 ≤ start) :
    (∑ i : Fin n,
      harperShiftedLatticePeriod
        (Problem520.harperScheduledRelativeIntervalWidth
          (start + i.val))
        (harperScheduledBivariateExpansionRadius
          (start + i.val))) ≤ 1 := by
  have hdelta := sum_fin_harperScheduledRelativeIntervalWidth_le_inv
    start n (by omega)
  have hdeltaSix :
      (∑ i : Fin n,
        Problem520.harperScheduledRelativeIntervalWidth
          (start + i.val)) ≤ (1 / 6 : Real) := by
    calc
      (∑ i : Fin n,
          Problem520.harperScheduledRelativeIntervalWidth
            (start + i.val)) ≤ 1 / (start : Real) := hdelta
      _ ≤ 1 / 6 := by
        exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hstart)
  have hexpansionTerm (i : Fin n) :
      harperScheduledBivariateExpansionRadius (start + i.val) ≤
        4 * (1 / 2 : Real) ^ (start + i.val) := by
    calc
      harperScheduledBivariateExpansionRadius (start + i.val) ≤
          4 * (1 / 4 : Real) ^ (start + i.val) :=
        harperScheduledBivariateExpansionRadius_le_four_mul_quarter_pow
          (by omega)
      _ ≤ 4 * (1 / 2 : Real) ^ (start + i.val) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀
            (by norm_num : 0 ≤ (1 / 4 : Real))
            (by norm_num : (1 / 4 : Real) ≤ 1 / 2) _)
          (by norm_num)
  have hexpansion :
      (∑ i : Fin n,
        harperScheduledBivariateExpansionRadius (start + i.val)) ≤
          (1 / 8 : Real) := by
    calc
      (∑ i : Fin n,
          harperScheduledBivariateExpansionRadius (start + i.val)) ≤
          ∑ i : Fin n, 4 * (1 / 2 : Real) ^ (start + i.val) :=
        Finset.sum_le_sum fun i _hi ↦ hexpansionTerm i
      _ = 4 * ∑ i : Fin n, (1 / 2 : Real) ^ (start + i.val) := by
        rw [Finset.mul_sum]
      _ ≤ 4 * (2 * (1 / 2 : Real) ^ start) := by
        gcongr
        exact sum_fin_half_pow_shift_le start n
      _ ≤ 1 / 8 := by
        have hp : (1 / 2 : Real) ^ start ≤ (1 / 2 : Real) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hstart
        norm_num at hp ⊢
        linarith
  simp_rw [harperShiftedLatticePeriod, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  linarith

/-- The shifted pair-cell form of the compiled local relative comparison. -/
theorem exists_harperScheduledTwoHeightRelativeShiftedPairCell_le :
    ∃ J : Nat, ∀ shell j y : Nat, J + (shell + 1) ≤ j →
      Problem520.harperBlockEndpoint (j + 1) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (shell + 1) < |t - s| →
              ∀ phi : UnitAddCircle × UnitAddCircle, ∀ z : Int × Int,
                let delta := Problem520.harperScheduledRelativeIntervalWidth j
                let h := harperScheduledBivariateExpansionRadius j
                let a := ((z.1 : Real) +
                    harperUnitPhaseRepresentative phi.1) *
                  harperShiftedLatticePeriod delta h
                let b := ((z.2 : Real) +
                    harperUnitPhaseRepresentative phi.2) *
                  harperShiftedLatticePeriod delta h
                |a| + |b| + 3 ≤
                    (1 / 16 : Real) *
                      Real.sqrt (((2 ^ j : Nat) : Real)) →
                  (1 - 2 / Real.sqrt
                      (Problem520.harperScheduledStrongComparisonFrequency j)) ^
                        (2 : Nat) *
                      (harperTwoHeightPrimeBlockVectorLaw y
                        (Problem520.harperScheduledPrimeBlock y j) t s).real
                          (harperShiftedPairCoreCell delta h phi z) ≤
                    (1 + 2 * delta) *
                      (harperTwoHeightGaussianLaw y
                        (Problem520.harperScheduledPrimeBlock y j) t s).real
                          (harperShiftedPairFullCell delta h phi z) := by
  obtain ⟨J, hJ⟩ :=
    exists_harperScheduledTwoHeightRelativeRectangleProbability_le
  refine ⟨J, ?_⟩
  intro shell j y hj hy t ht s hs hsep phi z
  dsimp only
  intro hmoderate
  let delta := Problem520.harperScheduledRelativeIntervalWidth j
  let h := harperScheduledBivariateExpansionRadius j
  let a := ((z.1 : Real) + harperUnitPhaseRepresentative phi.1) *
    harperShiftedLatticePeriod delta h
  let b := ((z.2 : Real) + harperUnitPhaseRepresentative phi.2) *
    harperShiftedLatticePeriod delta h
  have hlocal := hJ shell j y hj hy t ht s hs hsep a b hmoderate
  simpa only [delta, h, a, b, harperShiftedPairCoreCell,
    harperShiftedPairFullCell, harperShiftedCoreCell,
    harperShiftedFullCell, harperScheduledBivariateExpansionRadius]
    using hlocal

/-- The local comparisons multiply and sum over any finite active family of
shifted path cells.  This is the path-composition theorem before the purely
geometric choice of the active family. -/
theorem exists_harperScheduledTwoHeightRelativeShiftedFiniteUnion_le :
    ∃ J : Nat, ∀ shell start n y : Nat,
      J + (shell + 1) ≤ start →
      Problem520.harperBlockEndpoint (start + n) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (shell + 1) < |t - s| →
              ∀ phi : Fin n → UnitAddCircle × UnitAddCircle,
                ∀ active : Finset (Fin n → Int × Int),
                  (∀ z ∈ active, ∀ i,
                    let j := start + i.val
                    let delta :=
                      Problem520.harperScheduledRelativeIntervalWidth j
                    let h := harperScheduledBivariateExpansionRadius j
                    let a := ((z i).1 : Real) +
                        harperUnitPhaseRepresentative (phi i).1
                    let b := ((z i).2 : Real) +
                        harperUnitPhaseRepresentative (phi i).2
                    |a * harperShiftedLatticePeriod delta h| +
                        |b * harperShiftedLatticePeriod delta h| + 3 ≤
                      (1 / 16 : Real) *
                        Real.sqrt (((2 ^ j : Nat) : Real))) →
                  let delta : Fin n → Real := fun i ↦
                    Problem520.harperScheduledRelativeIntervalWidth
                      (start + i.val)
                  let h : Fin n → Real := fun i ↦
                    harperScheduledBivariateExpansionRadius (start + i.val)
                  let retention : Fin n → Real := fun i ↦
                    (1 - 2 / Real.sqrt
                      (Problem520.harperScheduledStrongComparisonFrequency
                        (start + i.val))) ^ (2 : Nat)
                  let loss : Fin n → Real := fun i ↦
                    1 + 2 * Problem520.harperScheduledRelativeIntervalWidth
                      (start + i.val)
                  (∏ i, retention i) *
                    (Measure.pi (fun i : Fin n ↦
                      harperTwoHeightPrimeBlockVectorLaw y
                        (Problem520.harperScheduledPrimeBlock y
                          (start + i.val)) t s)).real
                      (⋃ z ∈ active,
                        harperShiftedPairPathCoreCell delta h phi z) ≤
                  (∏ i, loss i) *
                    (Measure.pi (fun i : Fin n ↦
                      harperTwoHeightGaussianLaw y
                        (Problem520.harperScheduledPrimeBlock y
                          (start + i.val)) t s)).real
                      (⋃ z ∈ active,
                        harperShiftedPairPathFullCell delta h phi z) := by
  obtain ⟨Jlocal, hlocal⟩ :=
    exists_harperScheduledTwoHeightRelativeShiftedPairCell_le
  let J := max 4 Jlocal
  refine ⟨J, ?_⟩
  intro shell start n y hstart hy t ht s hs hsep phi active hmoderate
  dsimp only
  let delta : Fin n → Real := fun i ↦
    Problem520.harperScheduledRelativeIntervalWidth (start + i.val)
  let h : Fin n → Real := fun i ↦
    harperScheduledBivariateExpansionRadius (start + i.val)
  let retention : Fin n → Real := fun i ↦
    (1 - 2 / Real.sqrt
      (Problem520.harperScheduledStrongComparisonFrequency
        (start + i.val))) ^ (2 : Nat)
  let loss : Fin n → Real := fun i ↦
    1 + 2 * Problem520.harperScheduledRelativeIntervalWidth
      (start + i.val)
  have hjFour (i : Fin n) : 4 ≤ start + i.val := by
    dsimp only [J] at hstart
    omega
  have hretention (i : Fin n) : 0 ≤ retention i := by
    dsimp only [retention]
    positivity
  have hloss (i : Fin n) : 0 ≤ loss i := by
    dsimp only [loss]
    have hd := Problem520.harperScheduledRelativeIntervalWidth_pos
      (start + i.val)
    linarith
  have hperiod (i : Fin n) :
      0 < harperShiftedLatticePeriod (delta i) (h i) := by
    dsimp only [delta, h, harperShiftedLatticePeriod]
    have hd := Problem520.harperScheduledRelativeIntervalWidth_pos
      (start + i.val)
    have hh := harperScheduledBivariateExpansionRadius_pos (start + i.val)
    positivity
  apply measureReal_biUnion_shiftedPairPathCoreCell_le_prod_mul_fullCell
    (rho := fun i : Fin n ↦
      harperTwoHeightPrimeBlockVectorLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)
    (nu := fun i : Fin n ↦
      harperTwoHeightGaussianLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)
    retention loss delta h phi active hretention hloss hperiod
  intro z hz i
  have hj : Jlocal + (shell + 1) ≤ start + i.val := by
    dsimp only [J] at hstart
    omega
  have hyi :
      Problem520.harperBlockEndpoint (start + i.val + 1) ≤ y := by
    exact (Problem520.strictMono_harperBlockEndpoint.monotone (by omega)).trans hy
  have hm := hmoderate z hz i
  simpa only [delta, h, retention, loss, mul_assoc] using
    hlocal shell (start + i.val) y hj hyi t ht s hs hsep (phi i) (z i) hm

/-- Haar phase selection plus the finite disjoint-cell comparison.  The only
remaining input is geometric: for every phase, exhibit a finite moderate
family whose core cells cover the selected part of `A` and whose full cells
lie in the Gaussian guard `G`. -/
theorem exists_harperScheduledTwoHeightRelativeShiftedPath_le :
    ∃ J : Nat, ∀ shell start n y : Nat,
      J + (shell + 1) ≤ start →
      Problem520.harperBlockEndpoint (start + n) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (shell + 1) < |t - s| →
              ∀ A G : Set (Fin n → Real × Real), MeasurableSet A →
                (∀ phi : Fin n → UnitAddCircle × UnitAddCircle,
                  ∃ active : Finset (Fin n → Int × Int),
                    A ∩ harperShiftedPairPathCoreSet
                      (fun i ↦
                        Problem520.harperScheduledRelativeIntervalWidth
                          (start + i.val))
                      (fun i ↦ harperScheduledBivariateExpansionRadius
                        (start + i.val)) phi ⊆
                      ⋃ z ∈ active, harperShiftedPairPathCoreCell
                        (fun i ↦
                          Problem520.harperScheduledRelativeIntervalWidth
                            (start + i.val))
                        (fun i ↦ harperScheduledBivariateExpansionRadius
                          (start + i.val)) phi z ∧
                    (∀ z ∈ active, ∀ i,
                      let j := start + i.val
                      let delta :=
                        Problem520.harperScheduledRelativeIntervalWidth j
                      let h := harperScheduledBivariateExpansionRadius j
                      let a := ((z i).1 : Real) +
                        harperUnitPhaseRepresentative (phi i).1
                      let b := ((z i).2 : Real) +
                        harperUnitPhaseRepresentative (phi i).2
                      |a * harperShiftedLatticePeriod delta h| +
                          |b * harperShiftedLatticePeriod delta h| + 3 ≤
                        (1 / 16 : Real) *
                          Real.sqrt (((2 ^ j : Nat) : Real))) ∧
                    (⋃ z ∈ active, harperShiftedPairPathFullCell
                      (fun i ↦
                        Problem520.harperScheduledRelativeIntervalWidth
                          (start + i.val))
                      (fun i ↦ harperScheduledBivariateExpansionRadius
                        (start + i.val)) phi z) ⊆ G) →
                let delta : Fin n → Real := fun i ↦
                  Problem520.harperScheduledRelativeIntervalWidth
                    (start + i.val)
                let h : Fin n → Real := fun i ↦
                  harperScheduledBivariateExpansionRadius (start + i.val)
                let coreFraction : Fin n × Bool → Real := fun p ↦
                  delta p.1 /
                    harperShiftedLatticePeriod (delta p.1) (h p.1)
                let retention : Fin n → Real := fun i ↦
                  (1 - 2 / Real.sqrt
                    (Problem520.harperScheduledStrongComparisonFrequency
                      (start + i.val))) ^ (2 : Nat)
                let loss : Fin n → Real := fun i ↦
                  1 + 2 * Problem520.harperScheduledRelativeIntervalWidth
                    (start + i.val)
                ((∏ i, retention i) * (∏ p, coreFraction p)) *
                    (Measure.pi (fun i : Fin n ↦
                      harperTwoHeightPrimeBlockVectorLaw y
                        (Problem520.harperScheduledPrimeBlock y
                          (start + i.val)) t s)).real A ≤
                  (∏ i, loss i) *
                    (Measure.pi (fun i : Fin n ↦
                      harperTwoHeightGaussianLaw y
                        (Problem520.harperScheduledPrimeBlock y
                          (start + i.val)) t s)).real G := by
  obtain ⟨J, hfinite⟩ :=
    exists_harperScheduledTwoHeightRelativeShiftedFiniteUnion_le
  refine ⟨J, ?_⟩
  intro shell start n y hstart hy t ht s hs hsep A G hA hgeometry
  dsimp only
  let delta : Fin n → Real := fun i ↦
    Problem520.harperScheduledRelativeIntervalWidth (start + i.val)
  let h : Fin n → Real := fun i ↦
    harperScheduledBivariateExpansionRadius (start + i.val)
  let coreFraction : Fin n × Bool → Real := fun p ↦
    delta p.1 / harperShiftedLatticePeriod (delta p.1) (h p.1)
  let retention : Fin n → Real := fun i ↦
    (1 - 2 / Real.sqrt
      (Problem520.harperScheduledStrongComparisonFrequency
        (start + i.val))) ^ (2 : Nat)
  let loss : Fin n → Real := fun i ↦
    1 + 2 * Problem520.harperScheduledRelativeIntervalWidth
      (start + i.val)
  let rho : Fin n → Measure (Real × Real) := fun i ↦
    harperTwoHeightPrimeBlockVectorLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  let nu : Fin n → Measure (Real × Real) := fun i ↦
    harperTwoHeightGaussianLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  have hdelta (i : Fin n) : 0 ≤ delta i := by
    exact (Problem520.harperScheduledRelativeIntervalWidth_pos _).le
  have hh (i : Fin n) : 0 ≤ h i := by
    exact (harperScheduledBivariateExpansionRadius_pos _).le
  have hperiod (i : Fin n) :
      0 < harperShiftedLatticePeriod (delta i) (h i) := by
    dsimp only [delta, h, harperShiftedLatticePeriod]
    exact add_pos_of_pos_of_nonneg
      (Problem520.harperScheduledRelativeIntervalWidth_pos _)
      (mul_nonneg (by norm_num)
        (harperScheduledBivariateExpansionRadius_pos _).le)
  have hretention (i : Fin n) : 0 ≤ retention i := by
    dsimp only [retention]
    positivity
  have hretentionProd : 0 ≤ ∏ i, retention i :=
    Finset.prod_nonneg fun i _hi ↦ hretention i
  have hloss (i : Fin n) : 0 ≤ loss i := by
    dsimp only [loss]
    have hd := Problem520.harperScheduledRelativeIntervalWidth_pos
      (start + i.val)
    linarith
  have hlossProd : 0 ≤ ∏ i, loss i :=
    Finset.prod_nonneg fun i _hi ↦ hloss i
  obtain ⟨phi, hphase⟩ :=
    exists_pairPhase_measureReal_shiftedPathCoreSet_ge
      (Measure.pi rho) hA delta h hdelta hh hperiod
  obtain ⟨active, hcover, hmoderate, hfull⟩ := hgeometry phi
  have hselected :
      (Measure.pi rho).real
          (A ∩ harperShiftedPairPathCoreSet delta h phi) ≤
        (Measure.pi rho).real
          (⋃ z ∈ active,
            harperShiftedPairPathCoreCell delta h phi z) :=
    measureReal_mono hcover (measure_ne_top _ _)
  have hcompare :=
    hfinite shell start n y hstart hy t ht s hs hsep phi active hmoderate
  change
    ((∏ i, retention i) * (∏ p, coreFraction p)) *
        (Measure.pi rho).real A ≤
      (∏ i, loss i) * (Measure.pi nu).real G
  calc
    ((∏ i, retention i) * (∏ p, coreFraction p)) *
          (Measure.pi rho).real A =
        (∏ i, retention i) *
          ((∏ p, coreFraction p) * (Measure.pi rho).real A) := by ring
    _ ≤ (∏ i, retention i) *
          (Measure.pi rho).real
            (A ∩ harperShiftedPairPathCoreSet delta h phi) := by
      exact mul_le_mul_of_nonneg_left hphase hretentionProd
    _ ≤ (∏ i, retention i) *
          (Measure.pi rho).real
            (⋃ z ∈ active,
              harperShiftedPairPathCoreCell delta h phi z) := by
      exact mul_le_mul_of_nonneg_left hselected hretentionProd
    _ ≤ (∏ i, loss i) *
          (Measure.pi nu).real
            (⋃ z ∈ active,
              harperShiftedPairPathFullCell delta h phi z) := by
      simpa only [rho, nu, delta, h, retention, loss] using hcompare
    _ ≤ (∏ i, loss i) * (Measure.pi nu).real G := by
      exact mul_le_mul_of_nonneg_left
        (measureReal_mono hfull (measure_ne_top _ _)) hlossProd

/-- Unconditional separated-height comparison for the interior linear
guard.  All shifted-lattice products and geometric side conditions have been
discharged into the absolute factor `4 * exp 4`. -/
theorem exists_harperScheduledTwoHeightInteriorGuard_le_gaussianLinearGuard :
    ∃ J : Nat, ∀ shell start n y : Nat,
      J + (shell + 1) ≤ start →
      Problem520.harperBlockEndpoint (start + n) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (shell + 1) < |t - s| →
              (Measure.pi (fun i : Fin n ↦
                harperTwoHeightPrimeBlockVectorLaw y
                  (Problem520.harperScheduledPrimeBlock y
                    (start + i.val)) t s)).real
                  (harperPairedInteriorLinearGuardPathEvent n) ≤
                4 * Real.exp 4 *
                  (Measure.pi (fun i : Fin n ↦
                    harperTwoHeightGaussianLaw y
                      (Problem520.harperScheduledPrimeBlock y
                        (start + i.val)) t s)).real
                    (harperPairedLinearGuardPathEvent n) := by
  obtain ⟨Jpath, hpath⟩ :=
    exists_harperScheduledTwoHeightRelativeShiftedPath_le
  let J := max 30 Jpath
  refine ⟨J, ?_⟩
  intro shell start n y hstart hy t ht s hs hsep
  have hstartThirty : 30 ≤ start := by
    dsimp only [J] at hstart
    omega
  have hstartPath : Jpath + (shell + 1) ≤ start := by
    dsimp only [J] at hstart
    omega
  let delta : Fin n → Real := fun i ↦
    Problem520.harperScheduledRelativeIntervalWidth (start + i.val)
  let h : Fin n → Real := fun i ↦
    harperScheduledBivariateExpansionRadius (start + i.val)
  let period : Fin n → Real := fun i ↦
    harperShiftedLatticePeriod (delta i) (h i)
  let R : Fin n → Real := fun i ↦
    128 * (((i.val + 1 : Nat) : Real))
  have hdelta (i : Fin n) : 0 ≤ delta i :=
    (Problem520.harperScheduledRelativeIntervalWidth_pos _).le
  have hh (i : Fin n) : 0 ≤ h i :=
    (harperScheduledBivariateExpansionRadius_pos _).le
  have hperiodPos (i : Fin n) : 0 < period i := by
    dsimp only [period, delta, h, harperShiftedLatticePeriod]
    exact add_pos_of_pos_of_nonneg
      (Problem520.harperScheduledRelativeIntervalWidth_pos _)
      (mul_nonneg (by norm_num)
        (harperScheduledBivariateExpansionRadius_pos _).le)
  have hbounded :
      ∀ x ∈ harperPairedInteriorLinearGuardPathEvent n, ∀ i,
        (x i).1 ∈ Icc (-(R i)) (R i) ∧
          (x i).2 ∈ Icc (-(R i)) (R i) := by
    intro x hx i
    have hxLinear :=
      harperPairedInteriorLinearGuardPathEvent_subset_linearGuard n hx
    have hxPair :
        (fun i ↦ (x i).1) ∈ harperLinearGuardPathEvent n ∧
          (fun i ↦ (x i).2) ∈ harperLinearGuardPathEvent n := by
      simpa only [harperPairedLinearGuardPathEvent,
        Set.mem_preimage, Set.mem_prod, harperPairPathUnzipCLM_apply]
        using hxLinear
    have hfirst := abs_coordinate_le_of_linear_partialSum_guard
      (fun i ↦ (x i).1)
      (fun k ↦ (Problem520.mem_harperPartialSumBarrierSet.mp hxPair.1 k).1)
      (fun k ↦ (Problem520.mem_harperPartialSumBarrierSet.mp hxPair.1 k).2) i
    have hsecond := abs_coordinate_le_of_linear_partialSum_guard
      (fun i ↦ (x i).2)
      (fun k ↦ (Problem520.mem_harperPartialSumBarrierSet.mp hxPair.2 k).1)
      (fun k ↦ (Problem520.mem_harperPartialSumBarrierSet.mp hxPair.2 k).2) i
    exact ⟨abs_le.mp hfirst, abs_le.mp hsecond⟩
  have hgeometry :
      ∀ phi : Fin n → UnitAddCircle × UnitAddCircle,
        ∃ active : Finset (Fin n → Int × Int),
          harperPairedInteriorLinearGuardPathEvent n ∩
              harperShiftedPairPathCoreSet delta h phi ⊆
            ⋃ z ∈ active,
              harperShiftedPairPathCoreCell delta h phi z ∧
          (∀ z ∈ active, ∀ i,
            let j := start + i.val
            let delta :=
              Problem520.harperScheduledRelativeIntervalWidth j
            let h := harperScheduledBivariateExpansionRadius j
            let a := ((z i).1 : Real) +
              harperUnitPhaseRepresentative (phi i).1
            let b := ((z i).2 : Real) +
              harperUnitPhaseRepresentative (phi i).2
            |a * harperShiftedLatticePeriod delta h| +
                |b * harperShiftedLatticePeriod delta h| + 3 ≤
              (1 / 16 : Real) *
                Real.sqrt (((2 ^ j : Nat) : Real))) ∧
          (⋃ z ∈ active,
              harperShiftedPairPathFullCell delta h phi z) ⊆
            harperPairedLinearGuardPathEvent n := by
    intro phi
    obtain ⟨active, hcover, hmeets⟩ :=
      exists_finite_shiftedPairPathCoreCell_cover_of_bounded
        (harperPairedInteriorLinearGuardPathEvent n) delta h R phi
        (fun i ↦ by simpa only [period] using hperiodPos i) hbounded
    refine ⟨active, hcover, ?_, ?_⟩
    · simpa only [delta, h] using
        harperScheduled_activeInteriorCells_moderate
          hstartThirty phi active (by simpa only [delta, h] using hmeets)
    · apply (iUnion_fullCells_subset_coordinateNeighborhood_of_meets
        (harperPairedInteriorLinearGuardPathEvent n) delta h phi active
        hdelta hh hmeets).trans
      apply coordinateNeighborhood_interiorGuard_subset_linearGuard period
      · intro i
        dsimp only [period]
        exact (hperiodPos i).le
      · dsimp only [period, delta, h]
        exact sum_harperScheduled_shiftedLatticePeriod_le_one
          (by omega : 6 ≤ start)
  have hraw := hpath shell start n y hstartPath hy t ht s hs hsep
    (harperPairedInteriorLinearGuardPathEvent n)
    (harperPairedLinearGuardPathEvent n)
    (measurableSet_harperPairedInteriorLinearGuardPathEvent n)
    (by simpa only [delta, h] using hgeometry)
  apply le_four_mul_exp_four_of_harperScheduled_products
    (start := start) (n := n) (by omega : 6 ≤ start)
    measureReal_nonneg measureReal_nonneg
  simpa only using hraw

/-- The completed separated-height `C/n` theorem for the actual scheduled
two-height Rademacher path, on the one-unit interior guard. -/
theorem exists_harperScheduledTwoHeightInteriorGuard_probability_le :
    ∃ C > 0, ∃ J : Nat, ∀ shell n y : Nat, 0 < n →
      Problem520.harperBlockEndpoint (J + (shell + 1) + n) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (shell + 1) < |t - s| →
              (Measure.pi (fun i : Fin n ↦
                harperTwoHeightPrimeBlockVectorLaw y
                  (Problem520.harperScheduledPrimeBlock y
                    (J + (shell + 1) + i.val)) t s)).real
                  (harperPairedInteriorLinearGuardPathEvent n) ≤
                C * (n : Real)⁻¹ := by
  obtain ⟨Jactual, hactual⟩ :=
    exists_harperScheduledTwoHeightInteriorGuard_le_gaussianLinearGuard
  obtain ⟨L, hL, Jgaussian, hgaussian⟩ :=
    exists_harperScheduledCorrelatedGaussian_linearGuard_probability_le
  let J := max Jactual Jgaussian
  let C := 4 * Real.exp 4 * (12288 * (512 * L + 3))
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, J, ?_⟩
  intro shell n y hn hy t ht s hs hsep
  let start := J + (shell + 1)
  have hactualStart : Jactual + (shell + 1) ≤ start := by
    dsimp only [start, J]
    omega
  have hactualBound := hactual shell start n y hactualStart hy
    t ht s hs hsep
  let r := shell + (J - Jgaussian)
  have hJgaussian : Jgaussian ≤ J := by
    dsimp only [J]
    exact le_max_right _ _
  have hstartEq : Jgaussian + (r + 1) = start := by
    dsimp only [r, start]
    omega
  have hshellLe : shell + 1 ≤ r + 1 := by
    dsimp only [r]
    omega
  have hsepGaussian :
      (1 / 2 : Real) ^ (r + 1) < |t - s| := by
    exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hshellLe).trans_lt
      hsep
  have hgaussianBound := hgaussian r n y hn (by
    simpa only [hstartEq] using hy) t ht s hs hsepGaussian
  rw [hstartEq] at hgaussianBound
  change
    (Measure.pi (fun i : Fin n ↦
      harperTwoHeightPrimeBlockVectorLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
        (harperPairedInteriorLinearGuardPathEvent n) ≤ C * (n : Real)⁻¹
  calc
    (Measure.pi (fun i : Fin n ↦
        harperTwoHeightPrimeBlockVectorLaw y
          (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
          (harperPairedInteriorLinearGuardPathEvent n) ≤
        4 * Real.exp 4 *
          (Measure.pi (fun i : Fin n ↦
            harperTwoHeightGaussianLaw y
              (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
            (harperPairedLinearGuardPathEvent n) := hactualBound
    _ ≤ 4 * Real.exp 4 *
        ((12288 * (512 * L + 3)) * (n : Real)⁻¹) := by
      gcongr
    _ = C * (n : Real)⁻¹ := by
      dsimp only [C]
      ring

end

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.volume_harperUnitIocArc
#print axioms Erdos.Problem1144.volume_harperUnitCorePhaseSet
#print axioms Erdos.Problem1144.measureReal_pi_harperUnitCorePhaseSet
#print axioms Erdos.Problem1144.exists_phase_measure_capture_ge_product
#print axioms Erdos.Problem1144.mem_harperNormalizedCoreUnion_iff
#print axioms Erdos.Problem1144.mem_harperShiftedCoreUnion_iff
#print axioms Erdos.Problem1144.exists_finite_shiftedPairPathCoreCell_cover_of_bounded
#print axioms Erdos.Problem1144.pairwiseDisjoint_harperShiftedFullCell
#print axioms Erdos.Problem1144.pairwiseDisjoint_harperShiftedPairPathFullCell
#print axioms Erdos.Problem1144.exists_pairPhase_measure_shiftedPathCoreSet_ge
#print axioms Erdos.Problem1144.exists_pairPhase_measureReal_shiftedPathCoreSet_ge
#print axioms Erdos.Problem1144.measureReal_biUnion_shiftedPairPathCoreCell_le_prod_mul_fullCell
#print axioms Erdos.Problem1144.one_half_le_prod_harperScheduled_coreFractions
#print axioms Erdos.Problem1144.one_half_le_prod_harperScheduled_retentions
#print axioms Erdos.Problem1144.prod_harperScheduled_twoHeightLoss_le_exp_four
#print axioms Erdos.Problem1144.exists_harperScheduledTwoHeightRelativeShiftedPairCell_le
#print axioms Erdos.Problem1144.exists_harperScheduledTwoHeightRelativeShiftedFiniteUnion_le
#print axioms Erdos.Problem1144.exists_harperScheduledTwoHeightRelativeShiftedPath_le
#print axioms Erdos.Problem1144.exists_harperScheduledTwoHeightInteriorGuard_le_gaussianLinearGuard
#print axioms Erdos.Problem1144.exists_harperScheduledTwoHeightInteriorGuard_probability_le
