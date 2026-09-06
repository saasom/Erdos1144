import Erdos.Problem1144.HarperTwoHeightDriftControl

open Finset MeasureTheory ProbabilityTheory Set

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Finite coordinate replacement for two-height ballot paths

The one-block comparison is useful only after it is lifted through the other
independent blocks.  This file begins that lift with the exact Fubini lemma:
a pointwise comparison of all coordinate sections integrates to the same
comparison under an arbitrary outer probability law, with the additive error
paid once.
-/

/-- Updating one increment changes exactly the partial sums at and after that
coordinate. -/
theorem harperPathPartialSum_update
    {n : Nat} (v : Fin n → Real) (i k : Fin n) (x : Real) :
    Problem520.harperPathPartialSum (Function.update v i x) k =
      if i ≤ k then
        Problem520.harperPathPartialSum v k - v i + x
      else Problem520.harperPathPartialSum v k := by
  unfold Problem520.harperPathPartialSum
  split_ifs with hik
  · rw [Finset.sum_update_of_mem (Finset.mem_Iic.mpr hik)]
    have hsum := (Finset.Iic k).sum_erase_add v
      (Finset.mem_Iic.mpr hik)
    rw [Finset.sdiff_singleton_eq_erase]
    linarith
  · rw [Finset.sum_update_of_notMem]
    simpa only [Finset.mem_Iic] using hik

/-- The scalar section of a partial-sum barrier obtained by varying one
increment and freezing all the others. -/
def harperBarrierCoordinateSection
    {n : Nat} (lower upper v : Fin n → Real) (i : Fin n) : Set Real :=
  {x | Function.update v i x ∈
    Problem520.harperPartialSumBarrierSet lower upper}

/-- A one-coordinate section of a finite two-sided partial-sum barrier is
either empty or a closed interval.  Its width is controlled by the corridor
width at the coordinate being replaced. -/
theorem harperBarrierCoordinateSection_eq_empty_or_Icc
    {n : Nat} (lower upper v : Fin n → Real) (i : Fin n) :
    harperBarrierCoordinateSection lower upper v i = ∅ ∨
      ∃ a b : Real,
        a ≤ b ∧ b - a ≤ upper i - lower i ∧
          harperBarrierCoordinateSection lower upper v i = Icc a b := by
  classical
  let K : Finset (Fin n) := Finset.Ici i
  have hK : K.Nonempty := by
    refine ⟨i, ?_⟩
    simp [K]
  let L : Finset Real := K.image fun k ↦
    lower k - (Problem520.harperPathPartialSum v k - v i)
  let U : Finset Real := K.image fun k ↦
    upper k - (Problem520.harperPathPartialSum v k - v i)
  have hL : L.Nonempty := hK.image _
  have hU : U.Nonempty := hK.image _
  let a : Real := L.max' hL
  let b : Real := U.min' hU
  by_cases hsection :
      (harperBarrierCoordinateSection lower upper v i).Nonempty
  · right
    rcases hsection with ⟨x0, hx0⟩
    have hmem (x : Real) :
        x ∈ harperBarrierCoordinateSection lower upper v i ↔
          a ≤ x ∧ x ≤ b := by
      constructor
      · intro hx
        have hall :=
          Problem520.mem_harperPartialSumBarrierSet.mp hx
        constructor
        · dsimp only [a]
          apply Finset.max'_le
          intro q hq
          rcases Finset.mem_image.mp hq with ⟨k, hk, rfl⟩
          have hik : i ≤ k := by
            simpa only [K, Finset.mem_Ici] using hk
          have hlow := (hall k).1
          rw [harperPathPartialSum_update v i k x, if_pos hik] at hlow
          linarith
        · dsimp only [b]
          apply Finset.le_min'
          intro q hq
          rcases Finset.mem_image.mp hq with ⟨k, hk, rfl⟩
          have hik : i ≤ k := by
            simpa only [K, Finset.mem_Ici] using hk
          have hupp := (hall k).2
          rw [harperPathPartialSum_update v i k x, if_pos hik] at hupp
          linarith
      · rintro ⟨hax, hxb⟩
        apply Problem520.mem_harperPartialSumBarrierSet.mpr
        intro k
        by_cases hik : i ≤ k
        · have hqL :
              lower k - (Problem520.harperPathPartialSum v k - v i) ∈ L := by
            apply Finset.mem_image.mpr
            exact ⟨k, by simpa only [K, Finset.mem_Ici], rfl⟩
          have hqU :
              upper k - (Problem520.harperPathPartialSum v k - v i) ∈ U := by
            apply Finset.mem_image.mpr
            exact ⟨k, by simpa only [K, Finset.mem_Ici], rfl⟩
          have hlowMax :
              lower k - (Problem520.harperPathPartialSum v k - v i) ≤ a := by
            exact Finset.le_max' L _ hqL
          have huppMin :
              b ≤ upper k - (Problem520.harperPathPartialSum v k - v i) := by
            exact Finset.min'_le U _ hqU
          rw [harperPathPartialSum_update v i k x, if_pos hik]
          constructor <;> linarith
        · have hall0 :=
            Problem520.mem_harperPartialSumBarrierSet.mp hx0 k
          rw [harperPathPartialSum_update v i k x, if_neg hik]
          rw [harperPathPartialSum_update v i k x0, if_neg hik] at hall0
          exact hall0
    have hx0Bounds := (hmem x0).mp hx0
    have hai :
        lower i - (Problem520.harperPathPartialSum v i - v i) ≤ a := by
      exact Finset.le_max' L _ (by
        apply Finset.mem_image.mpr
        exact ⟨i, by simp [K], rfl⟩)
    have hbi :
        b ≤ upper i - (Problem520.harperPathPartialSum v i - v i) := by
      exact Finset.min'_le U _ (by
        apply Finset.mem_image.mpr
        exact ⟨i, by simp [K], rfl⟩)
    refine ⟨a, b, hx0Bounds.1.trans hx0Bounds.2,
      ?_, ?_⟩
    · linarith
    · ext x
      simpa only [Set.mem_Icc] using hmem x
  · left
    exact not_nonempty_iff_eq_empty.mp hsection

/-- First scalar path carried by a path of increment pairs. -/
def harperPairFirstPath {n : Nat} (v : Fin n → Real × Real) :
    Fin n → Real := fun k ↦ (v k).1

/-- Second scalar path carried by a path of increment pairs. -/
def harperPairSecondPath {n : Nat} (v : Fin n → Real × Real) :
    Fin n → Real := fun k ↦ (v k).2

/-- The event that both coordinates of a paired-increment path stay in the
same two-sided partial-sum corridor. -/
def harperPairedPartialSumBarrierSet
    {n : Nat} (lower upper : Fin n → Real) :
    Set (Fin n → Real × Real) :=
  harperPairFirstPath ⁻¹'
      Problem520.harperPartialSumBarrierSet lower upper ∩
    harperPairSecondPath ⁻¹'
      Problem520.harperPartialSumBarrierSet lower upper

theorem measurable_harperPairFirstPath {n : Nat} :
    Measurable (harperPairFirstPath (n := n)) := by
  unfold harperPairFirstPath
  fun_prop

theorem measurable_harperPairSecondPath {n : Nat} :
    Measurable (harperPairSecondPath (n := n)) := by
  unfold harperPairSecondPath
  fun_prop

theorem measurableSet_harperPairedPartialSumBarrierSet
    {n : Nat} (lower upper : Fin n → Real) :
    MeasurableSet (harperPairedPartialSumBarrierSet lower upper) := by
  exact
    ((Problem520.measurableSet_harperPartialSumBarrierSet lower upper).preimage
      measurable_harperPairFirstPath).inter
    ((Problem520.measurableSet_harperPartialSumBarrierSet lower upper).preimage
      measurable_harperPairSecondPath)

/-- The section of the paired path event obtained by varying a single pair of
increments. -/
def harperPairedBarrierCoordinateSection
    {n : Nat} (lower upper : Fin n → Real)
    (v : Fin n → Real × Real) (i : Fin n) : Set (Real × Real) :=
  {z | Function.update v i z ∈
    harperPairedPartialSumBarrierSet lower upper}

/-- Measurable splitting of a finite paired path into all coordinates except
`i`, followed by coordinate `i`. -/
def harperPiCoordinateEquiv {n : Nat} (i : Fin (n + 1)) :
    (Fin (n + 1) → Real × Real) ≃ᵐ
      (Fin n → Real × Real) × (Real × Real) :=
  (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) ↦ Real × Real) i).trans
    (MeasurableEquiv.prodComm :
      ((Real × Real) × (Fin n → Real × Real)) ≃ᵐ
        ((Fin n → Real × Real) × (Real × Real)))

theorem harperPiCoordinateEquiv_symm_apply
    {n : Nat} (i : Fin (n + 1))
    (w : Fin n → Real × Real) (z : Real × Real) :
    (harperPiCoordinateEquiv i).symm (w, z) =
      @Fin.insertNth n (fun _ ↦ Real × Real) i z w := by
  rfl

/-- Inserting a placeholder and then updating its coordinate is exactly
insertion of the new coordinate. -/
theorem update_insertNth
    {n : Nat} (i : Fin (n + 1))
    (w : Fin n → Real × Real) (z0 z : Real × Real) :
    Function.update (@Fin.insertNth n (fun _ ↦ Real × Real) i z0 w) i z =
      @Fin.insertNth n (fun _ ↦ Real × Real) i z w := by
  apply funext
  exact i.forall_iff_succAbove.mpr ⟨by simp, fun j ↦ by simp⟩

/-- Splitting a finite product measure at one coordinate, with the other
coordinates placed first, preserves the real mass of every measurable event. -/
theorem pi_real_eq_coordinate_prod_real_preimage_symm
    {n : Nat} (M : Fin (n + 1) → Measure (Real × Real))
    [∀ j, IsProbabilityMeasure (M j)]
    (i : Fin (n + 1)) (E : Set (Fin (n + 1) → Real × Real))
    (hE : MeasurableSet E) :
    (Measure.pi M).real E =
      ((Measure.pi fun j : Fin n ↦ M (i.succAbove j)).prod (M i)).real
        ((harperPiCoordinateEquiv i).symm ⁻¹' E) := by
  let e := harperPiCoordinateEquiv i
  have hsplit : MeasurePreserving e (Measure.pi M)
      ((Measure.pi fun j : Fin n ↦ M (i.succAbove j)).prod (M i)) := by
    exact (measurePreserving_piFinSuccAbove M i).trans
      Measure.measurePreserving_swap
  rw [← hsplit.map_eq,
    map_measureReal_apply e.measurable (hE.preimage e.symm.measurable)]
  congr 1
  ext v
  simp only [Set.mem_preimage]
  rw [e.symm_apply_apply]

theorem harperPairFirstPath_update
    {n : Nat} (v : Fin n → Real × Real) (i : Fin n) (z : Real × Real) :
    harperPairFirstPath (Function.update v i z) =
      Function.update (harperPairFirstPath v) i z.1 := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [harperPairFirstPath]
  · simp [harperPairFirstPath, hki]

theorem harperPairSecondPath_update
    {n : Nat} (v : Fin n → Real × Real) (i : Fin n) (z : Real × Real) :
    harperPairSecondPath (Function.update v i z) =
      Function.update (harperPairSecondPath v) i z.2 := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [harperPairSecondPath]
  · simp [harperPairSecondPath, hki]

/-- A coordinate section of the paired two-walk event is exactly the product
of its two scalar sections. -/
theorem harperPairedBarrierCoordinateSection_eq_prod
    {n : Nat} (lower upper : Fin n → Real)
    (v : Fin n → Real × Real) (i : Fin n) :
    harperPairedBarrierCoordinateSection lower upper v i =
      harperBarrierCoordinateSection lower upper
          (harperPairFirstPath v) i ×ˢ
        harperBarrierCoordinateSection lower upper
          (harperPairSecondPath v) i := by
  ext z
  simp only [harperPairedBarrierCoordinateSection,
    harperPairedPartialSumBarrierSet, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_prod]
  rw [harperPairFirstPath_update, harperPairSecondPath_update]
  rfl

/-- Consequently every paired coordinate section is either empty or one
closed rectangle, with both side lengths controlled by the corridor width at
the replaced time. -/
theorem harperPairedBarrierCoordinateSection_eq_empty_or_prod_Icc
    {n : Nat} (lower upper : Fin n → Real)
    (v : Fin n → Real × Real) (i : Fin n) :
    harperPairedBarrierCoordinateSection lower upper v i = ∅ ∨
      ∃ a b c d : Real,
        a ≤ b ∧ c ≤ d ∧
        b - a ≤ upper i - lower i ∧
        d - c ≤ upper i - lower i ∧
        harperPairedBarrierCoordinateSection lower upper v i =
          Icc a b ×ˢ Icc c d := by
  rw [harperPairedBarrierCoordinateSection_eq_prod]
  rcases harperBarrierCoordinateSection_eq_empty_or_Icc
    lower upper (harperPairFirstPath v) i with hfirst | hfirst
  · left
    rw [hfirst]
    exact Set.empty_prod
  rcases harperBarrierCoordinateSection_eq_empty_or_Icc
      lower upper (harperPairSecondPath v) i with hsecond | hsecond
  · left
    rw [hsecond]
    exact Set.prod_empty
  · right
    rcases hfirst with ⟨a, b, hab, habWidth, hfirst⟩
    rcases hsecond with ⟨c, d, hcd, hcdWidth, hsecond⟩
    exact ⟨a, b, c, d, hab, hcd, habWidth, hcdWidth, by rw [hfirst, hsecond]⟩

/-- Enlarging a nonempty coordinate interval by `e` is absorbed by relaxing
both path barriers uniformly by `e`.  The proof clamps the new increment to
the old interval and compares the two paths. -/
theorem expanded_Icc_subset_relaxed_harperBarrierCoordinateSection
    {n : Nat} (lower upper v : Fin n → Real) (i : Fin n)
    {a b e : Real} (hab : a ≤ b) (he : 0 ≤ e)
    (hsection : harperBarrierCoordinateSection lower upper v i = Icc a b) :
    Icc (a - e) (b + e) ⊆
      harperBarrierCoordinateSection
        (fun k ↦ lower k - e) (fun k ↦ upper k + e) v i := by
  intro x hx
  let x0 : Real := max a (min b x)
  have hx0lower : a ≤ x0 := by
    exact le_max_left _ _
  have hx0upper : x0 ≤ b := by
    exact max_le hab (min_le_left _ _)
  have hx0mem : x0 ∈ harperBarrierCoordinateSection lower upper v i := by
    rw [hsection]
    exact ⟨hx0lower, hx0upper⟩
  have hxLower : x0 - e ≤ x := by
    have ha : a ≤ x + e := by linarith [hx.1]
    have hmin : min b x ≤ x + e := by
      exact (min_le_right _ _).trans (by linarith)
    have hx0 : x0 ≤ x + e := max_le ha hmin
    linarith
  have hxUpper : x ≤ x0 + e := by
    by_cases hxb : x ≤ b
    · have hmin : min b x = x := min_eq_right hxb
      have hxx0 : x ≤ x0 := by
        dsimp only [x0]
        rw [hmin]
        exact le_max_right _ _
      linarith
    · have hbx : b ≤ x := le_of_not_ge hxb
      have hmin : min b x = b := min_eq_left hbx
      have hbx0 : b ≤ x0 := by
        dsimp only [x0]
        rw [hmin]
        exact le_max_right _ _
      linarith [hx.2]
  have hall0 := Problem520.mem_harperPartialSumBarrierSet.mp hx0mem
  apply Problem520.mem_harperPartialSumBarrierSet.mpr
  intro k
  by_cases hik : i ≤ k
  · have hk0 := hall0 k
    rw [harperPathPartialSum_update v i k x0, if_pos hik] at hk0
    rw [harperPathPartialSum_update v i k x, if_pos hik]
    constructor <;> linarith
  · have hk0 := hall0 k
    rw [harperPathPartialSum_update v i k x0, if_neg hik] at hk0
    rw [harperPathPartialSum_update v i k x, if_neg hik]
    constructor <;> linarith

/-- A direct stability form used for the paired path: moving one increment by
at most `e` is absorbed by an `e`-relaxation of both barriers. -/
theorem mem_relaxed_harperBarrierCoordinateSection_of_close
    {n : Nat} (lower upper v : Fin n → Real) (i : Fin n)
    {x0 x e : Real} (he : 0 ≤ e)
    (hx0 : x0 ∈ harperBarrierCoordinateSection lower upper v i)
    (hlower : x0 - e ≤ x) (hupper : x ≤ x0 + e) :
    x ∈ harperBarrierCoordinateSection
      (fun k ↦ lower k - e) (fun k ↦ upper k + e) v i := by
  have hall0 := Problem520.mem_harperPartialSumBarrierSet.mp hx0
  apply Problem520.mem_harperPartialSumBarrierSet.mpr
  intro k
  by_cases hik : i ≤ k
  · have hk0 := hall0 k
    rw [harperPathPartialSum_update v i k x0, if_pos hik] at hk0
    rw [harperPathPartialSum_update v i k x, if_pos hik]
    constructor <;> linarith
  · have hk0 := hall0 k
    rw [harperPathPartialSum_update v i k x0, if_neg hik] at hk0
    rw [harperPathPartialSum_update v i k x, if_neg hik]
    constructor <;> linarith

/-- Enlarging a nonempty paired section rectangle coordinatewise is absorbed
by the same uniform relaxation of the two path corridors. -/
theorem expanded_prod_Icc_subset_relaxed_harperPairedBarrierCoordinateSection
    {n : Nat} (lower upper : Fin n → Real)
    (v : Fin n → Real × Real) (i : Fin n)
    {a b c d e : Real} (hab : a ≤ b) (hcd : c ≤ d) (he : 0 ≤ e)
    (hsection : harperPairedBarrierCoordinateSection lower upper v i =
      Icc a b ×ˢ Icc c d) :
    Icc (a - e) (b + e) ×ˢ Icc (c - e) (d + e) ⊆
      harperPairedBarrierCoordinateSection
        (fun k ↦ lower k - e) (fun k ↦ upper k + e) v i := by
  intro z hz
  let x0 : Real := max a (min b z.1)
  let y0 : Real := max c (min d z.2)
  have hx0lower : a ≤ x0 := le_max_left _ _
  have hx0upper : x0 ≤ b := max_le hab (min_le_left _ _)
  have hy0lower : c ≤ y0 := le_max_left _ _
  have hy0upper : y0 ≤ d := max_le hcd (min_le_left _ _)
  have hxLower : x0 - e ≤ z.1 := by
    have ha : a ≤ z.1 + e := by linarith [hz.1.1]
    have hmin : min b z.1 ≤ z.1 + e :=
      (min_le_right _ _).trans (by linarith)
    have hx0 : x0 ≤ z.1 + e := max_le ha hmin
    linarith
  have hxUpper : z.1 ≤ x0 + e := by
    by_cases hzb : z.1 ≤ b
    · have hmin : min b z.1 = z.1 := min_eq_right hzb
      have hzx0 : z.1 ≤ x0 := by
        dsimp only [x0]
        rw [hmin]
        exact le_max_right _ _
      linarith
    · have hbz : b ≤ z.1 := le_of_not_ge hzb
      have hmin : min b z.1 = b := min_eq_left hbz
      have hbx0 : b ≤ x0 := by
        dsimp only [x0]
        rw [hmin]
        exact le_max_right _ _
      linarith [hz.1.2]
  have hyLower : y0 - e ≤ z.2 := by
    have hc : c ≤ z.2 + e := by linarith [hz.2.1]
    have hmin : min d z.2 ≤ z.2 + e :=
      (min_le_right _ _).trans (by linarith)
    have hy0 : y0 ≤ z.2 + e := max_le hc hmin
    linarith
  have hyUpper : z.2 ≤ y0 + e := by
    by_cases hzd : z.2 ≤ d
    · have hmin : min d z.2 = z.2 := min_eq_right hzd
      have hzy0 : z.2 ≤ y0 := by
        dsimp only [y0]
        rw [hmin]
        exact le_max_right _ _
      linarith
    · have hdz : d ≤ z.2 := le_of_not_ge hzd
      have hmin : min d z.2 = d := min_eq_left hdz
      have hdy0 : d ≤ y0 := by
        dsimp only [y0]
        rw [hmin]
        exact le_max_right _ _
      linarith [hz.2.2]
  have hz0 : (x0, y0) ∈
      harperPairedBarrierCoordinateSection lower upper v i := by
    rw [hsection]
    exact ⟨⟨hx0lower, hx0upper⟩, hy0lower, hy0upper⟩
  rw [harperPairedBarrierCoordinateSection_eq_prod] at hz0 ⊢
  exact ⟨
    mem_relaxed_harperBarrierCoordinateSection_of_close
      lower upper (harperPairFirstPath v) i he hz0.1 hxLower hxUpper,
    mem_relaxed_harperBarrierCoordinateSection_of_close
      lower upper (harperPairSecondPath v) i he hz0.2 hyLower hyUpper⟩

/-- A pointwise comparison of the fibers of two measurable events integrates
through an arbitrary outer probability law.  The additive error is paid once,
not once per cell or outer configuration. -/
theorem probability_prod_real_le_of_fiberwise
    {Omega X : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    (R : Measure Omega) (mu nu : Measure X)
    [IsProbabilityMeasure R] [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu]
    {A B : Set (Omega × X)}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (beta err : Real)
    (hfiber : ∀ omega,
      beta * mu.real (Prod.mk omega ⁻¹' A) ≤
        nu.real (Prod.mk omega ⁻¹' B) + err) :
    beta * (R.prod mu).real A ≤ (R.prod nu).real B + err := by
  have hAint : Integrable (A.indicator (1 : Omega × X → Real))
      (R.prod mu) :=
    (integrable_const (1 : Real)).indicator hA
  have hBint : Integrable (B.indicator (1 : Omega × X → Real))
      (R.prod nu) :=
    (integrable_const (1 : Real)).indicator hB
  have hArepr : (R.prod mu).real A =
      ∫ omega, (mu.real (Prod.mk omega ⁻¹' A)) ∂ R := by
    rw [← integral_indicator_one (μ := R.prod mu) hA,
      integral_prod _ hAint]
    apply integral_congr_ae
    exact ae_of_all R fun omega ↦ by
      change (∫ x, A.indicator (1 : Omega × X → Real) (omega, x) ∂mu) =
        mu.real (Prod.mk omega ⁻¹' A)
      rw [← integral_indicator_one (μ := mu) (measurable_prodMk_left hA)]
      rfl
  have hBrepr : (R.prod nu).real B =
      ∫ omega, (nu.real (Prod.mk omega ⁻¹' B)) ∂ R := by
    rw [← integral_indicator_one (μ := R.prod nu) hB,
      integral_prod _ hBint]
    apply integral_congr_ae
    exact ae_of_all R fun omega ↦ by
      change (∫ x, B.indicator (1 : Omega × X → Real) (omega, x) ∂nu) =
        nu.real (Prod.mk omega ⁻¹' B)
      rw [← integral_indicator_one (μ := nu) (measurable_prodMk_left hB)]
      rfl
  rw [hArepr, hBrepr, ← integral_const_mul]
  calc
    (∫ omega, beta * mu.real (Prod.mk omega ⁻¹' A) ∂ R) ≤
        ∫ omega, (nu.real (Prod.mk omega ⁻¹' B) + err) ∂ R := by
      apply integral_mono
      · exact (Measure.integrable_measure_prodMk_left hA
          (measure_ne_top (R.prod mu) A)).const_mul beta
      · exact (Measure.integrable_measure_prodMk_left hB
          (measure_ne_top (R.prod nu) B)).add (integrable_const err)
      · exact hfiber
    _ = (∫ omega, nu.real (Prod.mk omega ⁻¹' B) ∂ R) + err := by
      rw [integral_add
        (Measure.integrable_measure_prodMk_left hB
          (measure_ne_top (R.prod nu) B)) (integrable_const err),
        integral_const]
      simp

/-- Lifting a closed-rectangle one-block comparison through all frozen
coordinates.  A source fiber may be empty; otherwise it is one rectangle,
and the enlarged comparison rectangle is required to lie in the target
fiber.  This is the exact form used by a path-coordinate replacement. -/
theorem probability_prod_real_le_of_rectangle_sections
    {Omega : Type*} [MeasurableSpace Omega]
    (R : Measure Omega) (mu nu : Measure (Real × Real))
    [IsProbabilityMeasure R] [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu]
    {A B : Set (Omega × (Real × Real))}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (beta err expand width : Real)
    (herr : 0 ≤ err)
    (hrectangle : ∀ {a b c d : Real},
      a ≤ b → c ≤ d → b - a ≤ width → d - c ≤ width →
      beta * mu.real (Icc a b ×ˢ Icc c d) ≤
        nu.real
          (Icc (a - expand) (b + expand) ×ˢ
            Icc (c - expand) (d + expand)) + err)
    (hsection : ∀ omega,
      Prod.mk omega ⁻¹' A = ∅ ∨
        ∃ a b c d : Real,
          a ≤ b ∧ c ≤ d ∧ b - a ≤ width ∧ d - c ≤ width ∧
          Prod.mk omega ⁻¹' A = Icc a b ×ˢ Icc c d ∧
          Icc (a - expand) (b + expand) ×ˢ
              Icc (c - expand) (d + expand) ⊆
            Prod.mk omega ⁻¹' B) :
    beta * (R.prod mu).real A ≤ (R.prod nu).real B + err := by
  apply probability_prod_real_le_of_fiberwise R mu nu hA hB beta err
  intro omega
  rcases hsection omega with hempty | hrect
  · rw [hempty, measureReal_empty, mul_zero]
    exact add_nonneg (measureReal_nonneg) herr
  · rcases hrect with
      ⟨a, b, c, d, hab, hcd, habWidth, hcdWidth, hsource, htarget⟩
    rw [hsource]
    exact (hrectangle hab hcd habWidth hcdWidth).trans
      (add_le_add (measureReal_mono htarget (measure_ne_top nu _)) le_rfl)

/-- One complete path-coordinate replacement.  After conditioning on all
other increments, the paired ballot event is a single rectangle, so the
one-block comparison lifts with one copy of its additive error. -/
theorem probability_prod_harperPairedBarrier_coordinate_replacement
    {Omega : Type*} [MeasurableSpace Omega]
    {n : Nat} (R : Measure Omega)
    (mu nu : Measure (Real × Real))
    [IsProbabilityMeasure R] [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu]
    (lower upper : Fin n → Real)
    (v : Omega → Fin n → Real × Real) (i : Fin n)
    (beta err expand width : Real)
    (herr : 0 ≤ err) (hexpand : 0 ≤ expand)
    (hwidth : upper i - lower i ≤ width)
    (hsourceMeas : MeasurableSet
      {w : Omega × (Real × Real) |
        Function.update (v w.1) i w.2 ∈
          harperPairedPartialSumBarrierSet lower upper})
    (htargetMeas : MeasurableSet
      {w : Omega × (Real × Real) |
        Function.update (v w.1) i w.2 ∈
          harperPairedPartialSumBarrierSet
            (fun k ↦ lower k - expand) (fun k ↦ upper k + expand)})
    (hrectangle : ∀ {a b c d : Real},
      a ≤ b → c ≤ d → b - a ≤ width → d - c ≤ width →
      beta * mu.real (Icc a b ×ˢ Icc c d) ≤
        nu.real
          (Icc (a - expand) (b + expand) ×ˢ
            Icc (c - expand) (d + expand)) + err) :
    beta * (R.prod mu).real
        {w : Omega × (Real × Real) |
          Function.update (v w.1) i w.2 ∈
            harperPairedPartialSumBarrierSet lower upper} ≤
      (R.prod nu).real
          {w : Omega × (Real × Real) |
            Function.update (v w.1) i w.2 ∈
              harperPairedPartialSumBarrierSet
                (fun k ↦ lower k - expand) (fun k ↦ upper k + expand)} +
        err := by
  apply probability_prod_real_le_of_rectangle_sections
    R mu nu hsourceMeas htargetMeas beta err expand width herr hrectangle
  intro omega
  rcases harperPairedBarrierCoordinateSection_eq_empty_or_prod_Icc
      lower upper (v omega) i with hempty | hrect
  · left
    exact hempty
  · right
    rcases hrect with
      ⟨a, b, c, d, hab, hcd, habWidth, hcdWidth, hsection⟩
    refine ⟨a, b, c, d, hab, hcd, habWidth.trans hwidth,
      hcdWidth.trans hwidth, hsection, ?_⟩
    exact
      expanded_prod_Icc_subset_relaxed_harperPairedBarrierCoordinateSection
        lower upper (v omega) i hab hcd hexpand hsection

/-- The one-coordinate replacement theorem directly on a finite product law.
All marginals except `i` are frozen, the `i`-th marginal is changed from
`M i` to `nu`, and the paired corridor is relaxed by `expand`. -/
theorem pi_harperPairedBarrier_coordinate_replacement
    {n : Nat} (M : Fin (n + 1) → Measure (Real × Real))
    [∀ j, IsProbabilityMeasure (M j)]
    (nu : Measure (Real × Real)) [IsProbabilityMeasure nu]
    (lower upper : Fin (n + 1) → Real) (i : Fin (n + 1))
    (beta err expand width : Real)
    (herr : 0 ≤ err) (hexpand : 0 ≤ expand)
    (hwidth : upper i - lower i ≤ width)
    (hrectangle : ∀ {a b c d : Real},
      a ≤ b → c ≤ d → b - a ≤ width → d - c ≤ width →
      beta * (M i).real (Icc a b ×ˢ Icc c d) ≤
        nu.real
          (Icc (a - expand) (b + expand) ×ˢ
            Icc (c - expand) (d + expand)) + err) :
    beta * (Measure.pi M).real
        (harperPairedPartialSumBarrierSet lower upper) ≤
      (Measure.pi (Function.update M i nu)).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ lower k - expand) (fun k ↦ upper k + expand)) +
        err := by
  classical
  let M' : Fin (n + 1) → Measure (Real × Real) :=
    Function.update M i nu
  let R : Measure (Fin n → Real × Real) :=
    Measure.pi fun j : Fin n ↦ M (i.succAbove j)
  let v : (Fin n → Real × Real) → Fin (n + 1) → Real × Real :=
    fun w ↦ @Fin.insertNth n (fun _ ↦ Real × Real) i (0, 0) w
  let A : Set ((Fin n → Real × Real) × (Real × Real)) :=
    {w | Function.update (v w.1) i w.2 ∈
      harperPairedPartialSumBarrierSet lower upper}
  let B : Set ((Fin n → Real × Real) × (Real × Real)) :=
    {w | Function.update (v w.1) i w.2 ∈
      harperPairedPartialSumBarrierSet
        (fun k ↦ lower k - expand) (fun k ↦ upper k + expand)}
  haveI hM' : ∀ j, IsProbabilityMeasure (M' j) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [M', Function.update_self]
    · simpa [M', hji] using
        (inferInstance : IsProbabilityMeasure (M j))
  have houter :
      Measure.pi (fun j : Fin n ↦ M' (i.succAbove j)) = R := by
    congr 1
    funext j
    simp [M', i.succAbove_ne j]
  have hassemble (w : Fin n → Real × Real) (z : Real × Real) :
      Function.update (v w) i z = (harperPiCoordinateEquiv i).symm (w, z) := by
    rw [harperPiCoordinateEquiv_symm_apply]
    exact update_insertNth i w (0, 0) z
  have hAeq : A = (harperPiCoordinateEquiv i).symm ⁻¹'
      harperPairedPartialSumBarrierSet lower upper := by
    ext w
    simp only [A, Set.mem_setOf_eq, Set.mem_preimage]
    rw [hassemble]
  have hBeq : B = (harperPiCoordinateEquiv i).symm ⁻¹'
      harperPairedPartialSumBarrierSet
        (fun k ↦ lower k - expand) (fun k ↦ upper k + expand) := by
    ext w
    simp only [B, Set.mem_setOf_eq, Set.mem_preimage]
    rw [hassemble]
  have hAmeas : MeasurableSet A := by
    rw [hAeq]
    exact
      (measurableSet_harperPairedPartialSumBarrierSet lower upper).preimage
        (harperPiCoordinateEquiv i).symm.measurable
  have hBmeas : MeasurableSet B := by
    rw [hBeq]
    exact
      (measurableSet_harperPairedPartialSumBarrierSet
        (fun k ↦ lower k - expand)
        (fun k ↦ upper k + expand)).preimage
          (harperPiCoordinateEquiv i).symm.measurable
  have hsource := pi_real_eq_coordinate_prod_real_preimage_symm
    M i (harperPairedPartialSumBarrierSet lower upper)
      (measurableSet_harperPairedPartialSumBarrierSet lower upper)
  have htarget := pi_real_eq_coordinate_prod_real_preimage_symm
    M' i
      (harperPairedPartialSumBarrierSet
        (fun k ↦ lower k - expand) (fun k ↦ upper k + expand))
      (measurableSet_harperPairedPartialSumBarrierSet
        (fun k ↦ lower k - expand) (fun k ↦ upper k + expand))
  have hlift : beta * (R.prod (M i)).real A ≤
      (R.prod nu).real B + err := by
    apply probability_prod_harperPairedBarrier_coordinate_replacement
      R (M i) nu lower upper v i beta err expand width herr hexpand hwidth
    · exact hAmeas
    · exact hBmeas
    · exact hrectangle
  rw [hAeq, hBeq] at hlift
  rw [houter] at htarget
  simpa only [M', Function.update_self, R, hsource, htarget] using hlift

/-- Hybrid product marginals: the first `r` coordinates use `Q`, and all
remaining coordinates use `P`. -/
def harperHybridMarginal
    {n : Nat} (P Q : Fin n → Measure (Real × Real))
    (r : Nat) (j : Fin n) : Measure (Real × Real) :=
  if j.val < r then Q j else P j

instance harperHybridMarginal_isProbabilityMeasure
    {n : Nat} (P Q : Fin n → Measure (Real × Real))
    [∀ j, IsProbabilityMeasure (P j)]
    [∀ j, IsProbabilityMeasure (Q j)]
    (r : Nat) (j : Fin n) :
    IsProbabilityMeasure (harperHybridMarginal P Q r j) := by
  unfold harperHybridMarginal
  split_ifs
  · infer_instance
  · infer_instance

theorem harperHybridMarginal_zero
    {n : Nat} (P Q : Fin n → Measure (Real × Real)) :
    harperHybridMarginal P Q 0 = P := by
  funext j
  simp [harperHybridMarginal]

theorem harperHybridMarginal_eq_right
    {n : Nat} (P Q : Fin n → Measure (Real × Real)) :
    harperHybridMarginal P Q n = Q := by
  funext j
  simp [harperHybridMarginal, j.isLt]

/-- Advancing a hybrid by one step is literal `Function.update` at the next
coordinate. -/
theorem harperHybridMarginal_succ_eq_update
    {n : Nat} (P Q : Fin n → Measure (Real × Real))
    {r : Nat} (hr : r < n) :
    harperHybridMarginal P Q (r + 1) =
      Function.update (harperHybridMarginal P Q r)
        (⟨r, hr⟩ : Fin n) (Q ⟨r, hr⟩) := by
  classical
  funext j
  let i : Fin n := ⟨r, hr⟩
  by_cases hji : j = i
  · subst j
    simp [harperHybridMarginal, i]
  · have hjne : j.val ≠ r := by
      intro hval
      apply hji
      exact Fin.ext hval
    by_cases hjr : j.val < r
    · have hjr1 : j.val < r + 1 := by omega
      simp [harperHybridMarginal, i, hji, hjr, hjr1]
    · have hjr1 : ¬j.val < r + 1 := by omega
      simp [harperHybridMarginal, i, hji, hjr, hjr1]

/-- Iterating coordinate replacements costs only `n * err`.  The retention
factor accumulates multiplicatively, while `beta ≤ 1` prevents earlier error
terms from growing. -/
theorem pow_mul_le_of_step_mul_le_add
    (q : Nat → Real) (beta err : Real) (n : Nat)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1) (herr : 0 ≤ err)
    (hstep : ∀ r < n, beta * q r ≤ q (r + 1) + err) :
    beta ^ n * q 0 ≤ q n + (n : Real) * err := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hfirst : beta ^ n * q 0 ≤ q n + (n : Real) * err := by
        apply ih
        intro r hr
        exact hstep r (by omega)
      have hscale :
          beta * (beta ^ n * q 0) ≤
            beta * (q n + (n : Real) * err) :=
        mul_le_mul_of_nonneg_left hfirst hbeta0
      have herrScale :
          beta * ((n : Real) * err) ≤ (n : Real) * err := by
        apply mul_le_of_le_one_left
        · positivity
        · exact hbeta1
      calc
        beta ^ (n + 1) * q 0 = beta * (beta ^ n * q 0) := by ring
        _ ≤ beta * (q n + (n : Real) * err) := hscale
        _ = beta * q n + beta * ((n : Real) * err) := by ring
        _ ≤ (q (n + 1) + err) + (n : Real) * err :=
          add_le_add (hstep n (by omega)) herrScale
        _ = q (n + 1) + ((n + 1 : Nat) : Real) * err := by
          push_cast
          ring

/-- Full finite Lindeberg replacement for a paired partial-sum corridor.
Every coordinate is replaced once.  The corridor expands by `n * expand`,
the local retention becomes `beta ^ n`, and the total additive loss is only
`n * err`. -/
theorem pi_harperPairedBarrier_finite_replacement
    {n : Nat} (P Q : Fin n → Measure (Real × Real))
    [∀ j, IsProbabilityMeasure (P j)]
    [∀ j, IsProbabilityMeasure (Q j)]
    (lower upper : Fin n → Real)
    (beta err expand width : Real)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (herr : 0 ≤ err) (hexpand : 0 ≤ expand)
    (hwidth : ∀ (r : Nat) (hr : r < n),
      upper (⟨r, hr⟩ : Fin n) - lower ⟨r, hr⟩ +
          2 * (r : Real) * expand ≤ width)
    (hrectangle : ∀ (i : Fin n) {a b c d : Real},
      a ≤ b → c ≤ d → b - a ≤ width → d - c ≤ width →
      beta * (P i).real (Icc a b ×ˢ Icc c d) ≤
        (Q i).real
          (Icc (a - expand) (b + expand) ×ˢ
            Icc (c - expand) (d + expand)) + err) :
    beta ^ n * (Measure.pi P).real
        (harperPairedPartialSumBarrierSet lower upper) ≤
      (Measure.pi Q).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ lower k - (n : Real) * expand)
            (fun k ↦ upper k + (n : Real) * expand)) +
        (n : Real) * err := by
  cases n with
  | zero =>
      have hPQ : P = Q := by
        funext i
        exact Fin.elim0 i
      subst Q
      simp
  | succ m =>
      let q : Nat → Real := fun r ↦
        (Measure.pi (harperHybridMarginal P Q r)).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ lower k - (r : Real) * expand)
            (fun k ↦ upper k + (r : Real) * expand))
      have hstep : ∀ r < m + 1, beta * q r ≤ q (r + 1) + err := by
        intro r hr
        let i : Fin (m + 1) := ⟨r, hr⟩
        have hMi : harperHybridMarginal P Q r i = P i := by
          simp [harperHybridMarginal, i]
        have hwidthr :
            (upper i + (r : Real) * expand) -
                (lower i - (r : Real) * expand) ≤ width := by
          have hw := hwidth r hr
          change upper i - lower i + 2 * (r : Real) * expand ≤ width at hw
          linarith
        have hlocal :=
          pi_harperPairedBarrier_coordinate_replacement
            (harperHybridMarginal P Q r) (Q i)
            (fun k ↦ lower k - (r : Real) * expand)
            (fun k ↦ upper k + (r : Real) * expand)
            i beta err expand width herr hexpand hwidthr
            (by
              intro a b c d hab hcd habWidth hcdWidth
              rw [hMi]
              exact hrectangle i hab hcd habWidth hcdWidth)
        have hMstep := harperHybridMarginal_succ_eq_update P Q hr
        have hlower :
            (fun k : Fin (m + 1) ↦
              (lower k - (r : Real) * expand) - expand) =
              fun k ↦ lower k - ((r + 1 : Nat) : Real) * expand := by
          funext k
          push_cast
          ring
        have hupper :
            (fun k : Fin (m + 1) ↦
              (upper k + (r : Real) * expand) + expand) =
              fun k ↦ upper k + ((r + 1 : Nat) : Real) * expand := by
          funext k
          push_cast
          ring
        rw [← hMstep, hlower, hupper] at hlocal
        simpa only [q] using hlocal
      have hiter := pow_mul_le_of_step_mul_le_add
        q beta err (m + 1) hbeta0 hbeta1 herr hstep
      simpa [q, harperHybridMarginal_zero,
        harperHybridMarginal_eq_right] using hiter

/-- Scheduled finite replacement for an arbitrary paired partial-sum
corridor.  The only geometric input is the coarse `64n+1` width bound; this
is what allows the theorem to be applied to a suffix after conditioning on
an arbitrary admissible prefix. -/
theorem harperScheduledTwoHeightArbitraryBarrier_finiteReplacement
    (y start n : Nat) (t s : Real)
    (lower upper : Fin n → Real)
    (hn : 4 ≤ n)
    (hcorridor : ∀ i, upper i - lower i ≤ 64 * (n : Real) + 1)
    (hfrequency : ∀ i : Fin n,
      4 * (n : Real) ^ (6 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hendpoint : ∀ i : Fin n,
      1048576 * (n : Real) ^ (48 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hcovariance : ∀ i : Fin n,
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t s| ≤ 1 / (n : Real) ^ (40 : Nat)) :
    let beta : Real :=
      ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
    let expand : Real := 4 * (1 / (n : Real) ^ (2 : Nat))
    let err : Real := 6 / (n : Real) ^ (4 : Nat)
    let P : Fin n → Measure (Real × Real) := fun i ↦
      harperTwoHeightBallotBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
    let Q : Fin n → Measure (Real × Real) := fun i ↦
      harperTwoHeightDriftedIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
    beta ^ n * (Measure.pi P).real
        (harperPairedPartialSumBarrierSet lower upper) ≤
      (Measure.pi Q).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ lower k - (n : Real) * expand)
            (fun k ↦ upper k + (n : Real) * expand)) +
        (n : Real) * err := by
  dsimp only
  let beta : Real :=
    ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
  let expand : Real := 4 * (1 / (n : Real) ^ (2 : Nat))
  let err : Real := 6 / (n : Real) ^ (4 : Nat)
  let P : Fin n → Measure (Real × Real) := fun i ↦
    harperTwoHeightBallotBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  let Q : Fin n → Measure (Real × Real) := fun i ↦
    harperTwoHeightDriftedIndependentGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  have hfracNonneg : 0 ≤ 2 / (n : Real) ^ (4 : Nat) := by positivity
  have hnPow : (2 : Real) ≤ (n : Real) ^ (4 : Nat) := by
    have hnR : (4 : Real) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : Real) ^ (2 : Nat) - 1)]
  have hfracOne : 2 / (n : Real) ^ (4 : Nat) ≤ 1 := by
    exact (div_le_one (by positivity)).mpr hnPow
  have huLower : -1 ≤ 1 - 2 / (n : Real) ^ (4 : Nat) := by
    linarith
  have huUpper : 1 - 2 / (n : Real) ^ (4 : Nat) ≤ 1 := by
    linarith
  have huSq :
      (1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat) ≤ 1 := by
    nlinarith [sq_nonneg
      (1 - 2 / (n : Real) ^ (4 : Nat) - 1),
      sq_nonneg
      (1 - 2 / (n : Real) ^ (4 : Nat) + 1)]
  have hbeta0 : 0 ≤ beta := by
    dsimp only [beta]
    positivity
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    nlinarith [sq_nonneg
      ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat))]
  have herr : 0 ≤ err := by
    dsimp only [err]
    positivity
  have hexpand : 0 ≤ expand := by
    dsimp only [expand]
    positivity
  apply pi_harperPairedBarrier_finite_replacement
    P Q lower upper beta err expand (65 * (n : Real) - 1)
    hbeta0 hbeta1 herr hexpand
  · intro r hr
    let i : Fin n := ⟨r, hr⟩
    have hbase := hcorridor i
    have hrn : (r : Real) ≤ n := by
      exact_mod_cast (show r ≤ n by omega)
    have hsmall : 2 * (r : Real) * expand ≤ 2 := by
      dsimp only [expand]
      have hden : 0 < (n : Real) ^ (2 : Nat) := by positivity
      rw [show 2 * (r : Real) * (4 * (1 / (n : Real) ^ (2 : Nat))) =
        (8 * (r : Real)) / (n : Real) ^ (2 : Nat) by
          field_simp
          ring]
      apply (div_le_iff₀ hden).mpr
      have hnR : (4 : Real) ≤ n := by exact_mod_cast hn
      nlinarith
    have hnR : (4 : Real) ≤ n := by exact_mod_cast hn
    change upper i - lower i + 2 * (r : Real) * expand ≤
      65 * (n : Real) - 1
    nlinarith
  · intro i a b c d hab hcd habWidth hcdWidth
    dsimp only [P, Q, beta, expand, err]
    exact
      harperScheduledTwoHeightBallotClosedRectangleMass_le_driftedGaussian_cutoff
        y (start + i.val) n t s hn hab hcd habWidth hcdWidth
          (hfrequency i) (hendpoint i) (hcovariance i)

/-- Concrete finite replacement for the scheduled two-height ballot block
laws.  It packages the Fourier cutoff comparison at every block into one path
comparison with total expansion `4/n` and raw total error `6n/n^4`. -/
theorem harperScheduledTwoHeightBallotPath_finiteReplacement
    (y start n : Nat) (t s : Real)
    (hn : 4 ≤ n)
    (hfrequency : ∀ i : Fin n,
      4 * (n : Real) ^ (6 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hendpoint : ∀ i : Fin n,
      1048576 * (n : Real) ^ (48 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hcovariance : ∀ i : Fin n,
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t s| ≤ 1 / (n : Real) ^ (40 : Nat)) :
    let beta : Real :=
      ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
    let expand : Real := 4 * (1 / (n : Real) ^ (2 : Nat))
    let err : Real := 6 / (n : Real) ^ (4 : Nat)
    let P : Fin n → Measure (Real × Real) := fun i ↦
      harperTwoHeightBallotBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
    let Q : Fin n → Measure (Real × Real) := fun i ↦
      harperTwoHeightDriftedIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
    beta ^ n * (Measure.pi P).real
        (harperPairedPartialSumBarrierSet
          (harper1144LogBallotLowerBarrier start n)
          (harper1144LogBallotUpperBarrier n)) ≤
      (Measure.pi Q).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ harper1144LogBallotLowerBarrier start n k -
              (n : Real) * expand)
            (fun k ↦ harper1144LogBallotUpperBarrier n k +
              (n : Real) * expand)) +
        (n : Real) * err := by
  dsimp only
  let beta : Real :=
    ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
  let expand : Real := 4 * (1 / (n : Real) ^ (2 : Nat))
  let err : Real := 6 / (n : Real) ^ (4 : Nat)
  let P : Fin n → Measure (Real × Real) := fun i ↦
    harperTwoHeightBallotBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  let Q : Fin n → Measure (Real × Real) := fun i ↦
    harperTwoHeightDriftedIndependentGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  have hnPos : (0 : Real) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hfracNonneg : 0 ≤ 2 / (n : Real) ^ (4 : Nat) := by positivity
  have hnPow : (2 : Real) ≤ (n : Real) ^ (4 : Nat) := by
    have hnR : (4 : Real) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : Real) ^ (2 : Nat) - 1)]
  have hfracOne : 2 / (n : Real) ^ (4 : Nat) ≤ 1 := by
    exact (div_le_one (by positivity)).mpr hnPow
  have huLower :
      -1 ≤ 1 - 2 / (n : Real) ^ (4 : Nat) := by linarith
  have huUpper :
      1 - 2 / (n : Real) ^ (4 : Nat) ≤ 1 := by linarith
  have huSq :
      (1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat) ≤ 1 := by
    nlinarith [sq_nonneg
      (1 - 2 / (n : Real) ^ (4 : Nat) - 1),
      sq_nonneg
      (1 - 2 / (n : Real) ^ (4 : Nat) + 1)]
  have hbeta0 : 0 ≤ beta := by
    dsimp only [beta]
    positivity
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    nlinarith [sq_nonneg
      ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat))]
  have herr : 0 ≤ err := by
    dsimp only [err]
    positivity
  have hexpand : 0 ≤ expand := by
    dsimp only [expand]
    positivity
  apply pi_harperPairedBarrier_finite_replacement
    P Q
    (harper1144LogBallotLowerBarrier start n)
    (harper1144LogBallotUpperBarrier n)
    beta err expand (65 * (n : Real) - 1)
    hbeta0 hbeta1 herr hexpand
  · intro r hr
    let i : Fin n := ⟨r, hr⟩
    have hcorridor :=
      harper1144LogBallot_corridorWidth_le_add_one start n i
    have hrn : (r : Real) ≤ n := by
      exact_mod_cast (show r ≤ n by omega)
    have hsmall : 2 * (r : Real) * expand ≤ 2 := by
      dsimp only [expand]
      have hden : 0 < (n : Real) ^ (2 : Nat) := by positivity
      rw [show 2 * (r : Real) * (4 * (1 / (n : Real) ^ (2 : Nat))) =
        (8 * (r : Real)) / (n : Real) ^ (2 : Nat) by
          field_simp
          ring]
      apply (div_le_iff₀ hden).mpr
      have hnR : (4 : Real) ≤ n := by exact_mod_cast hn
      nlinarith
    have hnR : (4 : Real) ≤ n := by exact_mod_cast hn
    change
      harper1144LogBallotUpperBarrier n i -
          harper1144LogBallotLowerBarrier start n i +
        2 * (r : Real) * expand ≤ 65 * (n : Real) - 1
    nlinarith
  · intro i a b c d hab hcd habWidth hcdWidth
    dsimp only [P, Q, beta, expand, err]
    exact
      harperScheduledTwoHeightBallotClosedRectangleMass_le_driftedGaussian_cutoff
        y (start + i.val) n t s hn hab hcd habWidth hcdWidth
          (hfrequency i) (hendpoint i) (hcovariance i)

/-- The literal one-height-centered pairs of ballot increments remain
independent across scheduled prime blocks under the two-height tilt. -/
theorem iIndepFun_harperTwoHeightScheduledBallotBlockVectors
    (y start n : Nat) (t s : Real) :
    iIndepFun
      (fun j : Fin n ↦ fun eta : Problem520.HarperPrimeCube y ↦
        harperTwoHeightBallotBlockVector y
          (Problem520.harperScheduledPrimeBlock y (start + j.val)) t s eta)
      (harperTwoHeightCubeLaw y t s) := by
  let F : (j : Fin n) → Problem520.HarperPrimeCube y → Real × Real :=
    fun j eta ↦ harperTwoHeightPrimeBlockVector y
      (Problem520.harperScheduledPrimeBlock y (start + j.val)) t s eta
  let g : (j : Fin n) → Real × Real → Real × Real := fun j ↦
    harperPairTranslate
      (harperTwoHeightBallotBlockDrift y
        (Problem520.harperScheduledPrimeBlock y (start + j.val)) t s)
  have hjoint : iIndepFun F (harperTwoHeightCubeLaw y t s) := by
    exact iIndepFun_harperTwoHeightScheduledBlockVectors y start n t s
  have htranslated := hjoint.comp g fun j ↦
    measurable_harperPairTranslate _
  apply htranslated.congr
  intro j
  exact ae_of_all (harperTwoHeightCubeLaw y t s) fun eta ↦ by
    exact (harperTwoHeightBallotBlockVector_eq_translate y
      (Problem520.harperScheduledPrimeBlock y (start + j.val)) t s eta).symm

/-- Hence the full literal ballot-increment vector has exactly the product of
the individual literal ballot block laws. -/
theorem map_harperTwoHeightScheduledBallotBlockVectors_eq_pi
    (y start n : Nat) (t s : Real) :
    Measure.map
        (fun eta : Problem520.HarperPrimeCube y ↦ fun j : Fin n ↦
          harperTwoHeightBallotBlockVector y
            (Problem520.harperScheduledPrimeBlock y (start + j.val)) t s eta)
        (harperTwoHeightCubeLaw y t s) =
      Measure.pi (fun j : Fin n ↦
        harperTwoHeightBallotBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + j.val)) t s) := by
  have hmeas : ∀ j : Fin n, Measurable
      (fun eta : Problem520.HarperPrimeCube y ↦
        harperTwoHeightBallotBlockVector y
          (Problem520.harperScheduledPrimeBlock y (start + j.val)) t s eta) :=
    fun _j ↦ measurable_of_finite _
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (fun j ↦ (hmeas j).aemeasurable)).mp
      (iIndepFun_harperTwoHeightScheduledBallotBlockVectors y start n t s)
  simpa only [harperTwoHeightBallotBlockLaw] using h

/-- Measurable paired path events may therefore be evaluated exactly either
on the two-height tilted sign cube or under the product of literal ballot
block laws. -/
theorem harperTwoHeightCubeLaw_real_preimage_scheduledBallotBlockVectors_eq_pi
    (y start n : Nat) (t s : Real)
    (A : Set (Fin n → Real × Real)) (hA : MeasurableSet A) :
    (harperTwoHeightCubeLaw y t s).real
        ((fun eta : Problem520.HarperPrimeCube y ↦ fun j : Fin n ↦
          harperTwoHeightBallotBlockVector y
            (Problem520.harperScheduledPrimeBlock y (start + j.val))
              t s eta) ⁻¹' A) =
      (Measure.pi (fun j : Fin n ↦
        harperTwoHeightBallotBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + j.val)) t s)).real
        A := by
  let F : Problem520.HarperPrimeCube y → Fin n → Real × Real :=
    fun eta j ↦ harperTwoHeightBallotBlockVector y
      (Problem520.harperScheduledPrimeBlock y (start + j.val)) t s eta
  have hF : Measurable F :=
    measurable_pi_iff.mpr fun _j ↦ measurable_of_finite _
  have hmap := map_measureReal_apply
    (μ := harperTwoHeightCubeLaw y t s) hF hA
  rw [map_harperTwoHeightScheduledBallotBlockVectors_eq_pi] at hmap
  simpa only [F] using hmap.symm

/-- Coordinatewise deterministic translation of a paired increment path. -/
def harperPairPathTranslate
    {n : Nat} (d z : Fin n → Real × Real) : Fin n → Real × Real :=
  fun i ↦ harperPairTranslate (d i) (z i)

theorem measurable_harperPairPathTranslate
    {n : Nat} (d : Fin n → Real × Real) :
    Measurable (harperPairPathTranslate d) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_harperPairTranslate (d i)).comp
    (measurable_pi_apply i)

/-- A finite product of translated block laws is the pushforward of the
untranslated product by coordinatewise path translation. -/
theorem map_pi_harperPairPathTranslate
    {n : Nat} (G : Fin n → Measure (Real × Real))
    [∀ i, IsProbabilityMeasure (G i)]
    (d : Fin n → Real × Real) :
    Measure.map (harperPairPathTranslate d) (Measure.pi G) =
      Measure.pi (fun i ↦ Measure.map (harperPairTranslate (d i)) (G i)) := by
  simpa only [harperPairPathTranslate] using
    (Measure.pi_map_pi
      (μ := G)
      (f := fun i ↦ harperPairTranslate (d i))
      (fun i ↦ (measurable_harperPairTranslate (d i)).aemeasurable))

theorem harperPathPartialSum_pairPathTranslate_first
    {n : Nat} (d z : Fin n → Real × Real) (k : Fin n) :
    Problem520.harperPathPartialSum
        (harperPairFirstPath (harperPairPathTranslate d z)) k =
      Problem520.harperPathPartialSum (harperPairFirstPath z) k +
        ∑ i ∈ Finset.Iic k, (d i).1 := by
  unfold Problem520.harperPathPartialSum harperPairFirstPath
    harperPairPathTranslate harperPairTranslate
  rw [← Finset.sum_add_distrib]

theorem harperPathPartialSum_pairPathTranslate_second
    {n : Nat} (d z : Fin n → Real × Real) (k : Fin n) :
    Problem520.harperPathPartialSum
        (harperPairSecondPath (harperPairPathTranslate d z)) k =
      Problem520.harperPathPartialSum (harperPairSecondPath z) k +
        ∑ i ∈ Finset.Iic k, (d i).2 := by
  unfold Problem520.harperPathPartialSum harperPairSecondPath
    harperPairPathTranslate harperPairTranslate
  rw [← Finset.sum_add_distrib]

/-- If both cumulative deterministic drifts are bounded by `D`, removing the
drift enlarges each side of the paired path corridor by at most `D`. -/
theorem preimage_harperPairPathTranslate_pairedBarrier_subset_relaxed
    {n : Nat} (lower upper : Fin n → Real)
    (d : Fin n → Real × Real) (D : Real)
    (hfirst : ∀ k : Fin n, |∑ i ∈ Finset.Iic k, (d i).1| ≤ D)
    (hsecond : ∀ k : Fin n, |∑ i ∈ Finset.Iic k, (d i).2| ≤ D) :
    harperPairPathTranslate d ⁻¹'
        harperPairedPartialSumBarrierSet lower upper ⊆
      harperPairedPartialSumBarrierSet
        (fun k ↦ lower k - D) (fun k ↦ upper k + D) := by
  intro z hz
  rcases hz with ⟨hzfirst, hzsecond⟩
  constructor
  · apply Problem520.mem_harperPartialSumBarrierSet.mpr
    intro k
    have hk := Problem520.mem_harperPartialSumBarrierSet.mp hzfirst k
    rw [harperPathPartialSum_pairPathTranslate_first] at hk
    have habs := abs_le.mp (hfirst k)
    constructor <;> linarith
  · apply Problem520.mem_harperPartialSumBarrierSet.mpr
    intro k
    have hk := Problem520.mem_harperPartialSumBarrierSet.mp hzsecond k
    rw [harperPathPartialSum_pairPathTranslate_second] at hk
    have habs := abs_le.mp (hsecond k)
    constructor <;> linarith

/-- Mass form of deterministic drift removal for a product of translated
block laws. -/
theorem pi_translated_pairedBarrier_real_le_relaxed
    {n : Nat} (G : Fin n → Measure (Real × Real))
    [∀ i, IsProbabilityMeasure (G i)]
    (d : Fin n → Real × Real)
    (lower upper : Fin n → Real) (D : Real)
    (hfirst : ∀ k : Fin n, |∑ i ∈ Finset.Iic k, (d i).1| ≤ D)
    (hsecond : ∀ k : Fin n, |∑ i ∈ Finset.Iic k, (d i).2| ≤ D) :
    (Measure.pi (fun i ↦
        Measure.map (harperPairTranslate (d i)) (G i))).real
        (harperPairedPartialSumBarrierSet lower upper) ≤
      (Measure.pi G).real
        (harperPairedPartialSumBarrierSet
          (fun k ↦ lower k - D) (fun k ↦ upper k + D)) := by
  have hE := measurableSet_harperPairedPartialSumBarrierSet lower upper
  have hmap := map_measureReal_apply
    (μ := Measure.pi G) (measurable_harperPairPathTranslate d) hE
  rw [map_pi_harperPairPathTranslate] at hmap
  rw [hmap]
  exact measureReal_mono
    (preimage_harperPairPathTranslate_pairedBarrier_subset_relaxed
      lower upper d D hfirst hsecond)
    (measure_ne_top (Measure.pi G) _)

/-- Scheduled drift removal.  If every deterministic ballot-centering drift
is at most `n^-2`, then all cumulative prefix drifts are at most `n^-1`, so
the product of drifted independent Gaussian block laws is dominated by the
centered independent Gaussian path with an additional `n^-1` corridor
relaxation. -/
theorem harperScheduledDriftedGaussianPath_real_le_independent_relaxed
    (y start n : Nat) (t s : Real) (hn : 1 ≤ n)
    (lower upper : Fin n → Real)
    (hdriftFirst : ∀ i : Fin n,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t t| ≤ 1 / (n : Real) ^ (2 : Nat))
    (hdriftSecond : ∀ i : Fin n,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s s s| ≤ 1 / (n : Real) ^ (2 : Nat)) :
    (Measure.pi (fun i : Fin n ↦
      harperTwoHeightDriftedIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
        (harperPairedPartialSumBarrierSet lower upper) ≤
      (Measure.pi (fun i : Fin n ↦
        harperTwoHeightIndependentGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
        (harperPairedPartialSumBarrierSet
          (fun k ↦ lower k - 1 / (n : Real))
          (fun k ↦ upper k + 1 / (n : Real))) := by
  let G : Fin n → Measure (Real × Real) := fun i ↦
    harperTwoHeightIndependentGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  let d : Fin n → Real × Real := fun i ↦
    harperTwoHeightBallotBlockDrift y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  have hnPos : (0 : Real) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hprefix
      (coord : (Real × Real) → Real)
      (hcoord : ∀ i : Fin n, |coord (d i)| ≤
        1 / (n : Real) ^ (2 : Nat))
      (k : Fin n) :
      |∑ i ∈ Finset.Iic k, coord (d i)| ≤ 1 / (n : Real) := by
    calc
      |∑ i ∈ Finset.Iic k, coord (d i)| ≤
          ∑ i ∈ Finset.Iic k, |coord (d i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.Iic k,
          1 / (n : Real) ^ (2 : Nat) := by
        exact Finset.sum_le_sum fun i _hi ↦ hcoord i
      _ = ((k.val + 1 : Nat) : Real) *
          (1 / (n : Real) ^ (2 : Nat)) := by
        rw [Finset.sum_const, Fin.card_Iic, nsmul_eq_mul]
      _ ≤ (n : Real) * (1 / (n : Real) ^ (2 : Nat)) := by
        gcongr
        exact_mod_cast (show k.val + 1 ≤ n by omega)
      _ = 1 / (n : Real) := by field_simp
  have hfirst : ∀ k : Fin n,
      |∑ i ∈ Finset.Iic k, (d i).1| ≤ 1 / (n : Real) := by
    apply hprefix Prod.fst
    intro i
    exact hdriftFirst i
  have hsecond : ∀ k : Fin n,
      |∑ i ∈ Finset.Iic k, (d i).2| ≤ 1 / (n : Real) := by
    apply hprefix Prod.snd
    intro i
    exact hdriftSecond i
  have hmass := pi_translated_pairedBarrier_real_le_relaxed
    G d lower upper (1 / (n : Real)) hfirst hsecond
  simpa only [G, d, harperTwoHeightBallotBlockDrift,
    harperTwoHeightDriftedIndependentGaussianBlockLaw] using hmass

/-- End-to-end finite replacement for an arbitrary admissible corridor,
including deterministic drift removal.  This is the conditional-suffix form:
the barrier may already have been translated by an exposed prefix. -/
theorem harperScheduledTwoHeightArbitraryBarrierPath_le_independentGaussian
    (y start n : Nat) (t s : Real)
    (lower upper : Fin n → Real)
    (hn : 4 ≤ n)
    (hcorridor : ∀ i, upper i - lower i ≤ 64 * (n : Real) + 1)
    (hfrequency : ∀ i : Fin n,
      4 * (n : Real) ^ (6 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hendpoint : ∀ i : Fin n,
      1048576 * (n : Real) ^ (48 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hcovariance : ∀ i : Fin n,
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t s| ≤ 1 / (n : Real) ^ (40 : Nat))
    (hdriftFirst : ∀ i : Fin n,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t t| ≤ 1 / (n : Real) ^ (2 : Nat))
    (hdriftSecond : ∀ i : Fin n,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s s s| ≤ 1 / (n : Real) ^ (2 : Nat)) :
    let beta : Real :=
      ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
    let P : Fin n → Measure (Real × Real) := fun i ↦
      harperTwoHeightBallotBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
    let G : Fin n → Measure (Real × Real) := fun i ↦
      harperTwoHeightIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
    beta ^ n * (Measure.pi P).real
        (harperPairedPartialSumBarrierSet lower upper) ≤
      (Measure.pi G).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ lower k - 5 / (n : Real))
            (fun k ↦ upper k + 5 / (n : Real))) +
        6 / (n : Real) ^ (3 : Nat) := by
  dsimp only
  let beta : Real :=
    ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
  let expand : Real := 4 * (1 / (n : Real) ^ (2 : Nat))
  let err : Real := 6 / (n : Real) ^ (4 : Nat)
  let P : Fin n → Measure (Real × Real) := fun i ↦
    harperTwoHeightBallotBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  let Q : Fin n → Measure (Real × Real) := fun i ↦
    harperTwoHeightDriftedIndependentGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  let G : Fin n → Measure (Real × Real) := fun i ↦
    harperTwoHeightIndependentGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  have hreplace :=
    harperScheduledTwoHeightArbitraryBarrier_finiteReplacement
      y start n t s lower upper hn hcorridor hfrequency hendpoint hcovariance
  dsimp only at hreplace
  have hremove :=
    harperScheduledDriftedGaussianPath_real_le_independent_relaxed
      y start n t s (by omega)
      (fun k ↦ lower k - (n : Real) * expand)
      (fun k ↦ upper k + (n : Real) * expand)
      hdriftFirst hdriftSecond
  have htotalExpand : (n : Real) * expand + 1 / (n : Real) =
      5 / (n : Real) := by
    dsimp only [expand]
    field_simp
    ring
  have htotalErr : (n : Real) * err =
      6 / (n : Real) ^ (3 : Nat) := by
    dsimp only [err]
    field_simp
  have hlowerEq :
      (fun k : Fin n ↦
        (lower k - (n : Real) * expand) - 1 / (n : Real)) =
        fun k ↦ lower k - 5 / (n : Real) := by
    funext k
    rw [← htotalExpand]
    ring
  have hupperEq :
      (fun k : Fin n ↦
        (upper k + (n : Real) * expand) + 1 / (n : Real)) =
        fun k ↦ upper k + 5 / (n : Real) := by
    funext k
    rw [← htotalExpand]
    ring
  have hremove' :
      (Measure.pi Q).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ lower k - (n : Real) * expand)
            (fun k ↦ upper k + (n : Real) * expand)) ≤
        (Measure.pi G).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ lower k - 5 / (n : Real))
            (fun k ↦ upper k + 5 / (n : Real))) := by
    rw [hlowerEq, hupperEq] at hremove
    simpa only [Q, G] using hremove
  dsimp only [P, Q, G, beta, expand, err] at hreplace hremove' ⊢
  rw [htotalErr] at hreplace
  exact hreplace.trans (add_le_add hremove' le_rfl)

/-- End-to-end finite replacement through deterministic drift removal.  The
literal two-height ballot path is bounded by the centered coordinatewise
independent Gaussian path with total corridor enlargement `5/n` and additive
loss `6/n^3`. -/
theorem harperScheduledTwoHeightBallotPath_le_independentGaussian
    (y start n : Nat) (t s : Real)
    (hn : 4 ≤ n)
    (hfrequency : ∀ i : Fin n,
      4 * (n : Real) ^ (6 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hendpoint : ∀ i : Fin n,
      1048576 * (n : Real) ^ (48 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hcovariance : ∀ i : Fin n,
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t s| ≤ 1 / (n : Real) ^ (40 : Nat))
    (hdriftFirst : ∀ i : Fin n,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t t| ≤ 1 / (n : Real) ^ (2 : Nat))
    (hdriftSecond : ∀ i : Fin n,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s s s| ≤ 1 / (n : Real) ^ (2 : Nat)) :
    let beta : Real :=
      ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
    let P : Fin n → Measure (Real × Real) := fun i ↦
      harperTwoHeightBallotBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
    let G : Fin n → Measure (Real × Real) := fun i ↦
      harperTwoHeightIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
    beta ^ n * (Measure.pi P).real
        (harperPairedPartialSumBarrierSet
          (harper1144LogBallotLowerBarrier start n)
          (harper1144LogBallotUpperBarrier n)) ≤
      (Measure.pi G).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ harper1144LogBallotLowerBarrier start n k -
              5 / (n : Real))
            (fun k ↦ harper1144LogBallotUpperBarrier n k +
              5 / (n : Real))) +
        6 / (n : Real) ^ (3 : Nat) := by
  dsimp only
  let beta : Real :=
    ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
  let expand : Real := 4 * (1 / (n : Real) ^ (2 : Nat))
  let err : Real := 6 / (n : Real) ^ (4 : Nat)
  let P : Fin n → Measure (Real × Real) := fun i ↦
    harperTwoHeightBallotBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  let Q : Fin n → Measure (Real × Real) := fun i ↦
    harperTwoHeightDriftedIndependentGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  let G : Fin n → Measure (Real × Real) := fun i ↦
    harperTwoHeightIndependentGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  have hnPos : (0 : Real) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hreplace := harperScheduledTwoHeightBallotPath_finiteReplacement
    y start n t s hn hfrequency hendpoint hcovariance
  dsimp only at hreplace
  have hremove :=
    harperScheduledDriftedGaussianPath_real_le_independent_relaxed
      y start n t s (by omega)
      (fun k ↦ harper1144LogBallotLowerBarrier start n k -
        (n : Real) * expand)
      (fun k ↦ harper1144LogBallotUpperBarrier n k +
        (n : Real) * expand)
      hdriftFirst hdriftSecond
  have htotalExpand : (n : Real) * expand + 1 / (n : Real) =
      5 / (n : Real) := by
    dsimp only [expand]
    field_simp
    ring
  have htotalErr : (n : Real) * err =
      6 / (n : Real) ^ (3 : Nat) := by
    dsimp only [err]
    field_simp
  have hlowerEq :
      (fun k : Fin n ↦
        (harper1144LogBallotLowerBarrier start n k -
          (n : Real) * expand) - 1 / (n : Real)) =
        fun k ↦ harper1144LogBallotLowerBarrier start n k -
          5 / (n : Real) := by
    funext k
    rw [← htotalExpand]
    ring
  have hupperEq :
      (fun k : Fin n ↦
        (harper1144LogBallotUpperBarrier n k +
          (n : Real) * expand) + 1 / (n : Real)) =
        fun k ↦ harper1144LogBallotUpperBarrier n k +
          5 / (n : Real) := by
    funext k
    rw [← htotalExpand]
    ring
  have hremove' :
      (Measure.pi Q).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ harper1144LogBallotLowerBarrier start n k -
              (n : Real) * expand)
            (fun k ↦ harper1144LogBallotUpperBarrier n k +
              (n : Real) * expand)) ≤
        (Measure.pi G).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ harper1144LogBallotLowerBarrier start n k -
              5 / (n : Real))
            (fun k ↦ harper1144LogBallotUpperBarrier n k +
              5 / (n : Real))) := by
    rw [hlowerEq, hupperEq] at hremove
    simpa only [Q, G] using hremove
  dsimp only [P, Q, G, beta, expand, err] at hreplace hremove' ⊢
  rw [htotalErr] at hreplace
  exact hreplace.trans (add_le_add hremove' le_rfl)

/-- The eventual cutoff theorem supplies the frequency, endpoint,
decorrelation, and deterministic-drift hypotheses simultaneously on every
block of a scheduled length-`n` path. -/
theorem exists_harperTwoHeightCorridorCutoffPathHypotheses_with_drift
    {n : Nat} (hn : 4 ≤ n) :
    ∃ J : Nat, ∀ r start y : Nat, J + (r + 1) ≤ start →
      Problem520.harperBlockEndpoint (start + n) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (r + 1) < |t - s| →
              (∀ i : Fin n,
                4 * (n : Real) ^ (6 : Nat) ≤
                  Real.sqrt
                    (Problem520.harperBlockEndpoint
                      (start + i.val) : Real)) ∧
              (∀ i : Fin n,
                1048576 * (n : Real) ^ (48 : Nat) ≤
                  Real.sqrt
                    (Problem520.harperBlockEndpoint
                      (start + i.val) : Real)) ∧
              (∀ i : Fin n,
                |harperTwoHeightBlockCoordinateCovariance y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + i.val)) t s t s| ≤
                  1 / (n : Real) ^ (40 : Nat)) ∧
              (∀ i : Fin n,
                |harperTwoHeightRelativeBlockDrift y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + i.val)) t s t t| ≤
                  1 / (n : Real) ^ (2 : Nat)) ∧
              (∀ i : Fin n,
                |harperTwoHeightRelativeBlockDrift y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + i.val)) t s s s| ≤
                  1 / (n : Real) ^ (2 : Nat)) := by
  obtain ⟨J, hJ⟩ :=
    exists_harperTwoHeightCorridorCutoffBlockHypotheses_with_drift hn
  refine ⟨J, ?_⟩
  intro r start y hstart hy t ht s hs hsep
  have hblock (i : Fin n) :
      4 * (n : Real) ^ (6 : Nat) ≤
          Real.sqrt
            (Problem520.harperBlockEndpoint (start + i.val) : Real) ∧
        1048576 * (n : Real) ^ (48 : Nat) ≤
          Real.sqrt
            (Problem520.harperBlockEndpoint (start + i.val) : Real) ∧
        |harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s t s| ≤ 1 / (n : Real) ^ (40 : Nat) ∧
        |harperTwoHeightRelativeBlockDrift y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s t t| ≤ 1 / (n : Real) ^ (2 : Nat) ∧
        |harperTwoHeightRelativeBlockDrift y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s s s| ≤ 1 / (n : Real) ^ (2 : Nat) := by
    have hindex : J + (r + 1) ≤ start + i.val := by omega
    have hendIndex : start + i.val + 1 ≤ start + n := by omega
    have hendpoint :
        Problem520.harperBlockEndpoint (start + i.val + 1) ≤ y :=
      (Problem520.strictMono_harperBlockEndpoint.monotone hendIndex).trans hy
    exact hJ r (start + i.val) y hindex hendpoint t ht s hs hsep
  exact ⟨fun i ↦ (hblock i).1,
    fun i ↦ (hblock i).2.1,
    fun i ↦ (hblock i).2.2.1,
    fun i ↦ (hblock i).2.2.2.1,
    fun i ↦ (hblock i).2.2.2.2⟩

/-- The paired literal ballot-vector event is exactly the intersection of the
two one-height forward-pinched cube events. -/
theorem preimage_scheduledBallotBlockVectors_pairedLogBarrier_eq_inter
    (y start n : Nat) (t s : Real) :
    (fun eta : Problem520.HarperPrimeCube y ↦ fun j : Fin n ↦
      harperTwoHeightBallotBlockVector y
        (Problem520.harperScheduledPrimeBlock y (start + j.val)) t s eta) ⁻¹'
        harperPairedPartialSumBarrierSet
          (harper1144LogBallotLowerBarrier start n)
          (harper1144LogBallotUpperBarrier n) =
      harper1144LogBallotCubeEvent y start n t ∩
        harper1144LogBallotCubeEvent y start n s := by
  ext eta
  rfl

/-- Universal paired Gaussian ballot upper bound for arbitrary independent
variance vectors in the standard `[1/3, 3/8]` window and an arbitrary
nonnegative flat ceiling.  The quadratic dependence on the available upper
gap is the suffix estimate needed in the overlap-shell argument. -/
theorem independentGaussianPairedBarrier_real_le
    (n : Nat) (hn : 0 < n)
    (variance₁ variance₂ : Fin n → NNReal)
    (lower upper : Fin n → Real)
    (a : Real) (ha : 0 ≤ a)
    (hupperBarrier : ∀ k, upper k ≤ a)
    (hlower₁ : ∀ i, (1 / 3 : NNReal) ≤ variance₁ i)
    (hupper₁ : ∀ i, variance₁ i ≤ (3 / 8 : NNReal))
    (hlower₂ : ∀ i, (1 / 3 : NNReal) ≤ variance₂ i)
    (hupper₂ : ∀ i, variance₂ i ≤ (3 / 8 : NNReal)) :
    (Measure.pi (fun i : Fin n ↦
      (gaussianReal 0 (variance₁ i)).prod
        (gaussianReal 0 (variance₂ i)))).real
        (harperPairedPartialSumBarrierSet lower upper) ≤
      4096 * (a + 2) ^ (2 : Nat) * (n : Real)⁻¹ := by
  let E : Set (Fin n → Real) :=
    Problem520.harperPartialSumBarrierSet lower upper
  let Q₁ : Measure (Fin n → Real) :=
    Measure.pi fun i : Fin n ↦ gaussianReal 0 (variance₁ i)
  let Q₂ : Measure (Fin n → Real) :=
    Measure.pi fun i : Fin n ↦ gaussianReal 0 (variance₂ i)
  let e := MeasurableEquiv.arrowProdEquivProdArrow Real Real (Fin n)
  have hmp : MeasurePreserving e
      (Measure.pi (fun i : Fin n ↦
        (gaussianReal 0 (variance₁ i)).prod
          (gaussianReal 0 (variance₂ i))))
      (Q₁.prod Q₂) := by
    exact measurePreserving_arrowProdEquivProdArrow Real Real (Fin n)
      (fun i ↦ gaussianReal 0 (variance₁ i))
      (fun i ↦ gaussianReal 0 (variance₂ i))
  have hpre : e ⁻¹' (E ×ˢ E) =
      harperPairedPartialSumBarrierSet lower upper := by
    ext z
    rfl
  have hmass :
      (Measure.pi (fun i : Fin n ↦
        (gaussianReal 0 (variance₁ i)).prod
          (gaussianReal 0 (variance₂ i)))).real
          (harperPairedPartialSumBarrierSet lower upper) =
        (Q₁.prod Q₂).real (E ×ˢ E) := by
    rw [← hmp.map_eq,
      map_measureReal_apply e.measurable
        ((Problem520.measurableSet_harperPartialSumBarrierSet lower upper).prod
          (Problem520.measurableSet_harperPartialSumBarrierSet lower upper)),
      hpre]
  have hsubset : E ⊆ Problem520.gaussianWalkSurvivalSet n a := by
    intro omega homega
    apply (gaussianWalkSurvives_iff_harperPathPartialSum_le
      n a omega).mpr
    intro k
    exact (Problem520.mem_harperPartialSumBarrierSet.mp homega k).2.trans
      (hupperBarrier k)
  have hQ₁ : Q₁.real E ≤
      64 * (a + 2) / Real.sqrt (n : Real) := by
    have hflat := Problem520.gaussianVarianceWalk_third_threeEighths_probability_le_fin
      n hn variance₁ (x := a) ha hlower₁ hupper₁
    exact (measureReal_mono hsubset).trans (by
      simpa only [Q₁] using hflat)
  have hQ₂ : Q₂.real E ≤
      64 * (a + 2) / Real.sqrt (n : Real) := by
    have hflat := Problem520.gaussianVarianceWalk_third_threeEighths_probability_le_fin
      n hn variance₂ (x := a) ha hlower₂ hupper₂
    exact (measureReal_mono hsubset).trans (by
      simpa only [Q₂] using hflat)
  have hproduct : (Q₁.prod Q₂).real (E ×ˢ E) =
      Q₁.real E * Q₂.real E := by
    simp only [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  rw [hmass, hproduct]
  calc
    Q₁.real E * Q₂.real E ≤
        (64 * (a + 2) / Real.sqrt (n : Real)) *
          (64 * (a + 2) / Real.sqrt (n : Real)) :=
      mul_le_mul hQ₁ hQ₂ measureReal_nonneg (by positivity)
    _ = 4096 * (a + 2) ^ (2 : Nat) * (n : Real)⁻¹ := by
      rw [div_mul_div_comm, ← pow_two (Real.sqrt (n : Real)),
        Real.sq_sqrt hnR.le]
      field_simp
      ring

/-- Quantitative conditional-suffix theorem for the literal two-height
ballot increments.  An arbitrary admissible corridor whose translated upper
barrier is at most `a` has probability at most a universal constant times
`(a+4)^2/n` once every suffix block lies beyond the decorrelation cutoff. -/
theorem harperScheduledTwoHeightArbitraryBarrier_real_le
    (y start n : Nat) (t s : Real)
    (lower upper : Fin n → Real) (a : Real)
    (hn : 4 ≤ n) (ha : 0 ≤ a)
    (hupperBarrier : ∀ k, upper k ≤ a)
    (hcorridor : ∀ i, upper i - lower i ≤ 64 * (n : Real) + 1)
    (hfrequency : ∀ i : Fin n,
      4 * (n : Real) ^ (6 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hendpoint : ∀ i : Fin n,
      1048576 * (n : Real) ^ (48 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hcovariance : ∀ i : Fin n,
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t s| ≤ 1 / (n : Real) ^ (40 : Nat))
    (hdriftFirst : ∀ i : Fin n,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t t| ≤ 1 / (n : Real) ^ (2 : Nat))
    (hdriftSecond : ∀ i : Fin n,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s s s| ≤ 1 / (n : Real) ^ (2 : Nat))
    (hvarianceFirst : ∀ i : Fin n,
      (1 / 3 : Real) <
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s t t ∧
        harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s t t < (3 / 8 : Real))
    (hvarianceSecond : ∀ i : Fin n,
      (1 / 3 : Real) <
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s s s ∧
        harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s s s < (3 / 8 : Real)) :
    (Measure.pi (fun i : Fin n ↦
      harperTwoHeightBallotBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
        (harperPairedPartialSumBarrierSet lower upper) ≤
      5000 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹ := by
  let beta : Real :=
    ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
  let p : Real :=
    (Measure.pi (fun i : Fin n ↦
      harperTwoHeightBallotBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
        (harperPairedPartialSumBarrierSet lower upper)
  have hpath :=
    harperScheduledTwoHeightArbitraryBarrierPath_le_independentGaussian
      y start n t s lower upper hn hcorridor hfrequency hendpoint hcovariance
        hdriftFirst hdriftSecond
  dsimp only at hpath
  let variance₁ : Fin n → NNReal := fun i ↦
    harperTwoHeightCoordinateVarianceNNReal y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s t
  let variance₂ : Fin n → NNReal := fun i ↦
    harperTwoHeightCoordinateVarianceNNReal y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s s
  have hnPos : 0 < n := by omega
  have hnR : (4 : Real) ≤ n := by exact_mod_cast hn
  have hfive : 5 / (n : Real) ≤ 2 := by
    apply (div_le_iff₀ (by positivity : (0 : Real) < n)).mpr
    nlinarith
  have hupperRelax (k : Fin n) : upper k + 5 / (n : Real) ≤ a + 2 := by
    linarith [hupperBarrier k]
  have hlower₁ (i : Fin n) : (1 / 3 : NNReal) ≤ variance₁ i := by
    apply NNReal.coe_le_coe.mp
    change (1 / 3 : Real) ≤
      harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s t t
    exact (hvarianceFirst i).1.le
  have hupper₁ (i : Fin n) : variance₁ i ≤ (3 / 8 : NNReal) := by
    apply NNReal.coe_le_coe.mp
    change harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s t t ≤
      (3 / 8 : Real)
    exact (hvarianceFirst i).2.le
  have hlower₂ (i : Fin n) : (1 / 3 : NNReal) ≤ variance₂ i := by
    apply NNReal.coe_le_coe.mp
    change (1 / 3 : Real) ≤
      harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s s s
    exact (hvarianceSecond i).1.le
  have hupper₂ (i : Fin n) : variance₂ i ≤ (3 / 8 : NNReal) := by
    apply NNReal.coe_le_coe.mp
    change harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s s s ≤
      (3 / 8 : Real)
    exact (hvarianceSecond i).2.le
  have hgaussian := independentGaussianPairedBarrier_real_le
    n hnPos variance₁ variance₂
    (fun k ↦ lower k - 5 / (n : Real))
    (fun k ↦ upper k + 5 / (n : Real))
    (a + 2) (by linarith) hupperRelax
    hlower₁ hupper₁ hlower₂ hupper₂
  have hsum : a + 2 + 2 = a + 4 := by ring
  have hgaussian' :
      (Measure.pi (fun i : Fin n ↦
        harperTwoHeightIndependentGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ lower k - 5 / (n : Real))
            (fun k ↦ upper k + 5 / (n : Real))) ≤
        4096 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹ := by
    rw [hsum] at hgaussian
    simpa only [variance₁, variance₂,
      harperTwoHeightIndependentGaussianBlockLaw] using hgaussian
  have hweighted : beta ^ n * p ≤
      4096 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹ +
        6 / (n : Real) ^ (3 : Nat) := by
    dsimp only [beta, p]
    exact hpath.trans (add_le_add hgaussian' le_rfl)
  have hnPosR : (0 : Real) < n := by positivity
  have hnSq : (16 : Real) ≤ (n : Real) ^ (2 : Nat) := by
    nlinarith [sq_nonneg ((n : Real) - 4)]
  have hnLeCube : (n : Real) ≤ (n : Real) ^ (3 : Nat) := by
    have h1 : (1 : Real) ≤ (n : Real) ^ (2 : Nat) := by linarith
    calc
      (n : Real) = (n : Real) * 1 := by ring
      _ ≤ (n : Real) * (n : Real) ^ (2 : Nat) := by gcongr
      _ = (n : Real) ^ (3 : Nat) := by ring
  have herrSmall : 6 / (n : Real) ^ (3 : Nat) ≤ 6 / (n : Real) :=
    div_le_div_of_nonneg_left (by norm_num) hnPosR hnLeCube
  have haSq : (16 : Real) ≤ (a + 4) ^ (2 : Nat) := by
    nlinarith [sq_nonneg a]
  have hright :
      4096 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹ +
          6 / (n : Real) ^ (3 : Nat) ≤
        4375 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹ := by
    calc
      _ ≤ 4096 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹ +
          6 / (n : Real) := add_le_add le_rfl herrSmall
      _ = (4096 * (a + 4) ^ (2 : Nat) + 6) *
          (n : Real)⁻¹ := by ring
      _ ≤ (4375 * (a + 4) ^ (2 : Nat)) * (n : Real)⁻¹ := by
        gcongr
        nlinarith
      _ = _ := by ring
  have hretBase : (7 / 8 : Real) ≤
      1 - 8 / (n : Real) ^ (3 : Nat) := by
    have hden : 0 < (n : Real) ^ (3 : Nat) := by positivity
    have hnCube : (64 : Real) ≤ (n : Real) ^ (3 : Nat) := by
      calc
        (64 : Real) = (4 : Real) ^ (3 : Nat) := by norm_num
        _ ≤ (n : Real) ^ (3 : Nat) := by gcongr
    have hinv : 8 / (n : Real) ^ (3 : Nat) ≤ 1 / 8 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith
    linarith
  have hret : (7 / 8 : Real) ≤ beta ^ n :=
    hretBase.trans (by
      dsimp only [beta]
      exact one_sub_eight_div_cube_le_harperTwoHeightCutoff_retention
        (m := n) (n := n) (by omega) le_rfl)
  have hp0 : 0 ≤ p := by
    dsimp only [p]
    exact measureReal_nonneg
  have hweightedLower : (7 / 8 : Real) * p ≤ beta ^ n * p :=
    mul_le_mul_of_nonneg_right hret hp0
  have hpScaled : (7 / 8 : Real) * p ≤
      4375 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹ :=
    hweightedLower.trans (hweighted.trans hright)
  change p ≤ 5000 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹
  have hscaledTarget :
      (7 / 8 : Real) *
          (5000 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹) =
        4375 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹ := by
    ring
  exact (mul_le_mul_iff_right₀ (by norm_num : (0 : Real) < 7 / 8)).mp (by
    rw [hscaledTarget]
    exact hpScaled)

/-- Eventual separated-height form of the arbitrary-corridor suffix bound.
All analytic hypotheses are discharged uniformly; callers only supply the
translated deterministic corridor and its available upper gap. -/
theorem exists_eventually_harperScheduledTwoHeightArbitraryBarrier_real_le
    {n : Nat} (hn : 4 ≤ n) :
    ∃ J : Nat, ∀ r start y : Nat, J + (r + 1) ≤ start →
      Problem520.harperBlockEndpoint (start + n) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (r + 1) < |t - s| →
              ∀ (lower upper : Fin n → Real) (a : Real),
                0 ≤ a →
                (∀ k, upper k ≤ a) →
                (∀ i, upper i - lower i ≤ 64 * (n : Real) + 1) →
                (Measure.pi (fun i : Fin n ↦
                  harperTwoHeightBallotBlockLaw y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + i.val)) t s)).real
                    (harperPairedPartialSumBarrierSet lower upper) ≤
                  5000 * (a + 4) ^ (2 : Nat) * (n : Real)⁻¹ := by
  obtain ⟨Jcut, hcut⟩ :=
    exists_harperTwoHeightCorridorCutoffPathHypotheses_with_drift hn
  obtain ⟨Jvar, hvar⟩ :=
    exists_eventually_harperTwoHeightScheduledCoordinateVariance_third_threeEighths
  refine ⟨max Jcut Jvar, ?_⟩
  intro r start y hstart hy t ht s hs hsep lower upper a ha hupper hcorridor
  have hcutStart : Jcut + (r + 1) ≤ start := by
    have : Jcut ≤ max Jcut Jvar := le_max_left _ _
    omega
  obtain ⟨hfrequency, hendpoint, hcovariance,
      hdriftFirst, hdriftSecond⟩ :=
    hcut r start y hcutStart hy t ht s hs hsep
  have hvariance (i : Fin n) (u : Real) (hu : u ∈ harperLowerVerticalBand) :
      (1 / 3 : Real) <
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s u u ∧
        harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s u u < (3 / 8 : Real) := by
    have hvarIndex : Jvar ≤ start + i.val := by
      have : Jvar ≤ max Jcut Jvar := le_max_right _ _
      omega
    have hendIndex : start + i.val + 1 ≤ start + n := by omega
    have hyBlock :
        Problem520.harperBlockEndpoint (start + i.val + 1) ≤ y :=
      (Problem520.strictMono_harperBlockEndpoint.monotone hendIndex).trans hy
    exact hvar (start + i.val) hvarIndex y hyBlock t ht s hs u hu
  exact harperScheduledTwoHeightArbitraryBarrier_real_le
    y start n t s lower upper a hn ha hupper hcorridor
      hfrequency hendpoint hcovariance hdriftFirst hdriftSecond
      (fun i ↦ hvariance i t ht) (fun i ↦ hvariance i s hs)

/-- The preceding universal bound specialized to the exact independent
Gaussian marginals of the two-height tilt and the final `5/n`-relaxed
forward logarithmic corridor. -/
theorem harperTwoHeightIndependentGaussianLogBarrier_relaxed_le
    (y start n : Nat) (t s : Real) (hn : 4 ≤ n)
    (hvarianceFirst : ∀ i : Fin n,
      (1 / 3 : Real) <
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s t t ∧
        harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s t t < (3 / 8 : Real))
    (hvarianceSecond : ∀ i : Fin n,
      (1 / 3 : Real) <
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s s s ∧
        harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s s s < (3 / 8 : Real)) :
    (Measure.pi (fun i : Fin n ↦
      harperTwoHeightIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
        (harperPairedPartialSumBarrierSet
          (fun k ↦ harper1144LogBallotLowerBarrier start n k -
            5 / (n : Real))
          (fun k ↦ harper1144LogBallotUpperBarrier n k +
            5 / (n : Real))) ≤
      (102400 : Real) * (n : Real)⁻¹ := by
  let variance₁ : Fin n → NNReal := fun i ↦
    harperTwoHeightCoordinateVarianceNNReal y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s t
  let variance₂ : Fin n → NNReal := fun i ↦
    harperTwoHeightCoordinateVarianceNNReal y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s s
  have hnPos : 0 < n := by omega
  have hupperBarrier (k : Fin n) :
      harper1144LogBallotUpperBarrier n k + 5 / (n : Real) ≤ 3 := by
    have hlog := harper1144LogBallotUpperBarrier_le_one n k
    have hnR : (4 : Real) ≤ n := by exact_mod_cast hn
    have hfrac : 5 / (n : Real) ≤ 5 / 4 := by
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
    linarith
  have hlower₁ (i : Fin n) : (1 / 3 : NNReal) ≤ variance₁ i := by
    apply NNReal.coe_le_coe.mp
    change (1 / 3 : Real) ≤
      harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s t t
    exact (hvarianceFirst i).1.le
  have hupper₁ (i : Fin n) : variance₁ i ≤ (3 / 8 : NNReal) := by
    apply NNReal.coe_le_coe.mp
    change harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s t t ≤
      (3 / 8 : Real)
    exact (hvarianceFirst i).2.le
  have hlower₂ (i : Fin n) : (1 / 3 : NNReal) ≤ variance₂ i := by
    apply NNReal.coe_le_coe.mp
    change (1 / 3 : Real) ≤
      harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s s s
    exact (hvarianceSecond i).1.le
  have hupper₂ (i : Fin n) : variance₂ i ≤ (3 / 8 : NNReal) := by
    apply NNReal.coe_le_coe.mp
    change harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s s s ≤
      (3 / 8 : Real)
    exact (hvarianceSecond i).2.le
  have h := independentGaussianPairedBarrier_real_le
    n hnPos variance₁ variance₂
    (fun k ↦ harper1144LogBallotLowerBarrier start n k -
      5 / (n : Real))
    (fun k ↦ harper1144LogBallotUpperBarrier n k +
      5 / (n : Real))
    3 (by norm_num) hupperBarrier hlower₁ hupper₁ hlower₂ hupper₂
  norm_num at h
  simpa only [variance₁, variance₂,
    harperTwoHeightIndependentGaussianBlockLaw] using h

/-- Explicit separated-height intersection bound once the local cutoff,
drift, and sharp marginal-variance hypotheses are available. -/
theorem harperTwoHeightLogBallotInter_le_inv
    (y start n : Nat) (t s : Real)
    (hn : 4 ≤ n)
    (hfrequency : ∀ i : Fin n,
      4 * (n : Real) ^ (6 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hendpoint : ∀ i : Fin n,
      1048576 * (n : Real) ^ (48 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hcovariance : ∀ i : Fin n,
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t s| ≤ 1 / (n : Real) ^ (40 : Nat))
    (hdriftFirst : ∀ i : Fin n,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t t| ≤ 1 / (n : Real) ^ (2 : Nat))
    (hdriftSecond : ∀ i : Fin n,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s s s| ≤ 1 / (n : Real) ^ (2 : Nat))
    (hvarianceFirst : ∀ i : Fin n,
      (1 / 3 : Real) <
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s t t ∧
        harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s t t < (3 / 8 : Real))
    (hvarianceSecond : ∀ i : Fin n,
      (1 / 3 : Real) <
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s s s ∧
        harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s s s < (3 / 8 : Real)) :
    (harperTwoHeightCubeLaw y t s).real
        (harper1144LogBallotCubeEvent y start n t ∩
          harper1144LogBallotCubeEvent y start n s) ≤
      (120000 : Real) * (n : Real)⁻¹ := by
  let beta : Real :=
    ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
  let p : Real := (harperTwoHeightCubeLaw y t s).real
    (harper1144LogBallotCubeEvent y start n t ∩
      harper1144LogBallotCubeEvent y start n s)
  have hpath := harperScheduledTwoHeightBallotPath_le_independentGaussian
    y start n t s hn hfrequency hendpoint hcovariance
      hdriftFirst hdriftSecond
  dsimp only at hpath
  have hproduct :=
    harperTwoHeightCubeLaw_real_preimage_scheduledBallotBlockVectors_eq_pi
      y start n t s
      (harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start n)
        (harper1144LogBallotUpperBarrier n))
      (measurableSet_harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start n)
        (harper1144LogBallotUpperBarrier n))
  rw [preimage_scheduledBallotBlockVectors_pairedLogBarrier_eq_inter] at hproduct
  have hgaussian := harperTwoHeightIndependentGaussianLogBarrier_relaxed_le
    y start n t s hn hvarianceFirst hvarianceSecond
  have hweighted : beta ^ n * p ≤
      (102400 : Real) * (n : Real)⁻¹ +
        6 / (n : Real) ^ (3 : Nat) := by
    dsimp only [beta, p]
    rw [hproduct]
    exact hpath.trans (add_le_add hgaussian le_rfl)
  have hnR : (4 : Real) ≤ n := by exact_mod_cast hn
  have hnPos : (0 : Real) < n := by linarith
  have hnSq : (16 : Real) ≤ (n : Real) ^ (2 : Nat) := by
    nlinarith [sq_nonneg ((n : Real) - 4)]
  have hnCube : (64 : Real) ≤ (n : Real) ^ (3 : Nat) := by
    calc
      (64 : Real) = 4 * 16 := by norm_num
      _ ≤ (n : Real) * (n : Real) ^ (2 : Nat) :=
        mul_le_mul hnR hnSq (by norm_num) hnPos.le
      _ = (n : Real) ^ (3 : Nat) := by ring
  have hretBase : (7 / 8 : Real) ≤
      1 - 8 / (n : Real) ^ (3 : Nat) := by
    have hden : 0 < (n : Real) ^ (3 : Nat) := by positivity
    have hinv : 8 / (n : Real) ^ (3 : Nat) ≤ 1 / 8 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith
    linarith
  have hret : (7 / 8 : Real) ≤ beta ^ n :=
    hretBase.trans (by
      dsimp only [beta]
      exact one_sub_eight_div_cube_le_harperTwoHeightCutoff_retention
        (m := n) (n := n) (by omega) le_rfl)
  have hp0 : 0 ≤ p := by
    dsimp only [p]
    exact measureReal_nonneg
  have hweightedLower : (7 / 8 : Real) * p ≤ beta ^ n * p :=
    mul_le_mul_of_nonneg_right hret hp0
  have hnLeCube : (n : Real) ≤ (n : Real) ^ (3 : Nat) := by
    have h1 : (1 : Real) ≤ (n : Real) ^ (2 : Nat) := by linarith
    calc
      (n : Real) = (n : Real) * 1 := by ring
      _ ≤ (n : Real) * (n : Real) ^ (2 : Nat) := by gcongr
      _ = (n : Real) ^ (3 : Nat) := by ring
  have herrSmall : 6 / (n : Real) ^ (3 : Nat) ≤ 6 / (n : Real) :=
    div_le_div_of_nonneg_left (by norm_num) hnPos hnLeCube
  have hright :
      (102400 : Real) * (n : Real)⁻¹ +
          6 / (n : Real) ^ (3 : Nat) ≤
        (105000 : Real) / (n : Real) := by
    rw [show (102400 : Real) * (n : Real)⁻¹ = 102400 / (n : Real) by
      rfl]
    calc
      102400 / (n : Real) + 6 / (n : Real) ^ (3 : Nat) ≤
          102400 / (n : Real) + 6 / (n : Real) :=
        add_le_add le_rfl herrSmall
      _ ≤ 105000 / (n : Real) := by
        rw [← add_div]
        gcongr
        norm_num
  have hpScaled : (7 / 8 : Real) * p ≤ 105000 / (n : Real) :=
    hweightedLower.trans (hweighted.trans hright)
  change p ≤ (120000 : Real) * (n : Real)⁻¹
  have hscaledTarget :
      (7 / 8 : Real) * (120000 * (n : Real)⁻¹) =
        105000 / (n : Real) := by
    ring
  exact (mul_le_mul_iff_right₀ (by norm_num : (0 : Real) < 7 / 8)).mp (by
    rw [hscaledTarget]
    exact hpScaled)

/-- Cube-law form of the finite replacement: the two-height tilted mass of
the intersection of pinched events is bounded by the centered independent
Gaussian paired path, with explicit `5/n` corridor and `6/n^3` error. -/
theorem harperTwoHeightLogBallotInter_le_independentGaussian
    (y start n : Nat) (t s : Real)
    (hn : 4 ≤ n)
    (hfrequency : ∀ i : Fin n,
      4 * (n : Real) ^ (6 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hendpoint : ∀ i : Fin n,
      1048576 * (n : Real) ^ (48 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hcovariance : ∀ i : Fin n,
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t s| ≤ 1 / (n : Real) ^ (40 : Nat))
    (hdriftFirst : ∀ i : Fin n,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t t| ≤ 1 / (n : Real) ^ (2 : Nat))
    (hdriftSecond : ∀ i : Fin n,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s s s| ≤ 1 / (n : Real) ^ (2 : Nat)) :
    let beta : Real :=
      ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
    beta ^ n * (harperTwoHeightCubeLaw y t s).real
        (harper1144LogBallotCubeEvent y start n t ∩
          harper1144LogBallotCubeEvent y start n s) ≤
      (Measure.pi (fun i : Fin n ↦
        harperTwoHeightIndependentGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s)).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ harper1144LogBallotLowerBarrier start n k -
              5 / (n : Real))
            (fun k ↦ harper1144LogBallotUpperBarrier n k +
              5 / (n : Real))) +
        6 / (n : Real) ^ (3 : Nat) := by
  dsimp only
  have hproduct :=
    harperTwoHeightCubeLaw_real_preimage_scheduledBallotBlockVectors_eq_pi
      y start n t s
      (harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start n)
        (harper1144LogBallotUpperBarrier n))
      (measurableSet_harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start n)
        (harper1144LogBallotUpperBarrier n))
  rw [preimage_scheduledBallotBlockVectors_pairedLogBarrier_eq_inter] at hproduct
  rw [hproduct]
  exact harperScheduledTwoHeightBallotPath_le_independentGaussian
    y start n t s hn hfrequency hendpoint hcovariance
      hdriftFirst hdriftSecond

/-- The fully packaged separated-height ballot intersection bound.  Once the
schedule starts beyond a fixed index, the cutoff, decorrelation, drift, and
sharp marginal-variance estimates all hold simultaneously on every block of
the path, so the literal tilted cube intersection costs `O(1/n)`. -/
theorem exists_eventually_harperTwoHeightLogBallotInter_le_inv
    {n : Nat} (hn : 4 ≤ n) :
    ∃ J : Nat, ∀ r start y : Nat, J + (r + 1) ≤ start →
      Problem520.harperBlockEndpoint (start + n) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (r + 1) < |t - s| →
              (harperTwoHeightCubeLaw y t s).real
                  (harper1144LogBallotCubeEvent y start n t ∩
                    harper1144LogBallotCubeEvent y start n s) ≤
                (120000 : Real) * (n : Real)⁻¹ := by
  obtain ⟨Jcut, hcut⟩ :=
    exists_harperTwoHeightCorridorCutoffPathHypotheses_with_drift hn
  obtain ⟨Jvar, hvar⟩ :=
    exists_eventually_harperTwoHeightScheduledCoordinateVariance_third_threeEighths
  refine ⟨max Jcut Jvar, ?_⟩
  intro r start y hstart hy t ht s hs hsep
  have hcutStart : Jcut + (r + 1) ≤ start := by
    have : Jcut ≤ max Jcut Jvar := le_max_left _ _
    omega
  obtain ⟨hfrequency, hendpoint, hcovariance,
      hdriftFirst, hdriftSecond⟩ :=
    hcut r start y hcutStart hy t ht s hs hsep
  have hvariance (i : Fin n) (u : Real) (hu : u ∈ harperLowerVerticalBand) :
      (1 / 3 : Real) <
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s u u ∧
        harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s u u < (3 / 8 : Real) := by
    have hvarIndex : Jvar ≤ start + i.val := by
      have : Jvar ≤ max Jcut Jvar := le_max_right _ _
      omega
    have hendIndex : start + i.val + 1 ≤ start + n := by
      omega
    have hyBlock :
        Problem520.harperBlockEndpoint (start + i.val + 1) ≤ y :=
      (Problem520.strictMono_harperBlockEndpoint.monotone hendIndex).trans hy
    exact hvar (start + i.val) hvarIndex y hyBlock t ht s hs u hu
  exact harperTwoHeightLogBallotInter_le_inv y start n t s hn
    hfrequency hendpoint hcovariance hdriftFirst hdriftSecond
    (fun i ↦ hvariance i t ht) (fun i ↦ hvariance i s hs)

#print axioms Erdos.Problem1144.probability_prod_real_le_of_fiberwise
#print axioms Erdos.Problem1144.probability_prod_real_le_of_rectangle_sections
#print axioms Erdos.Problem1144.probability_prod_harperPairedBarrier_coordinate_replacement
#print axioms Erdos.Problem1144.pow_mul_le_of_step_mul_le_add
#print axioms Erdos.Problem1144.pi_harperPairedBarrier_finite_replacement
#print axioms Erdos.Problem1144.harperScheduledTwoHeightArbitraryBarrier_finiteReplacement
#print axioms Erdos.Problem1144.harperScheduledTwoHeightBallotPath_finiteReplacement
#print axioms Erdos.Problem1144.iIndepFun_harperTwoHeightScheduledBallotBlockVectors
#print axioms Erdos.Problem1144.map_harperTwoHeightScheduledBallotBlockVectors_eq_pi
#print axioms Erdos.Problem1144.harperTwoHeightCubeLaw_real_preimage_scheduledBallotBlockVectors_eq_pi
#print axioms Erdos.Problem1144.map_pi_harperPairPathTranslate
#print axioms Erdos.Problem1144.preimage_harperPairPathTranslate_pairedBarrier_subset_relaxed
#print axioms Erdos.Problem1144.pi_translated_pairedBarrier_real_le_relaxed
#print axioms Erdos.Problem1144.harperScheduledDriftedGaussianPath_real_le_independent_relaxed
#print axioms Erdos.Problem1144.harperScheduledTwoHeightArbitraryBarrierPath_le_independentGaussian
#print axioms Erdos.Problem1144.harperScheduledTwoHeightBallotPath_le_independentGaussian
#print axioms Erdos.Problem1144.exists_harperTwoHeightCorridorCutoffPathHypotheses_with_drift
#print axioms Erdos.Problem1144.preimage_scheduledBallotBlockVectors_pairedLogBarrier_eq_inter
#print axioms Erdos.Problem1144.independentGaussianPairedBarrier_real_le
#print axioms Erdos.Problem1144.harperScheduledTwoHeightArbitraryBarrier_real_le
#print axioms Erdos.Problem1144.exists_eventually_harperScheduledTwoHeightArbitraryBarrier_real_le
#print axioms Erdos.Problem1144.harperTwoHeightLogBallotInter_le_inv
#print axioms Erdos.Problem1144.harperTwoHeightLogBallotInter_le_independentGaussian
#print axioms Erdos.Problem1144.exists_eventually_harperTwoHeightLogBallotInter_le_inv

end

end Problem1144
end Erdos
