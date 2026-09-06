import Erdos.Problem1144.HarperFiniteCoordinateReplacement
import Erdos.Problem1144.HarperGaussianTerminalBallot

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Prefix/suffix sections of the paired Harper ballot

This module supplies the exact deterministic and product-measure split used
by the overlap-shell argument.  Once a prefix of a paired path is fixed, the
remaining ballot constraints are literally a paired partial-sum corridor
whose barriers are translated by the two exposed prefix sums.
-/

private theorem map_split_Iic_natAdd
    {d m : Nat} (k : Fin m) :
    (Finset.univ.map (Fin.castAddEmb m)) ∪
        ((Finset.Iic k).map (Fin.natAddEmb d)) =
      Finset.Iic (Fin.natAdd d k) := by
  ext q
  refine Fin.addCases ?_ ?_ q
  · intro i
    simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ,
      true_and, Fin.castAddEmb_apply, Finset.mem_Iic]
    constructor
    · intro _h
      change i.val ≤ d + k.val
      omega
    · intro _h
      exact Or.inl ⟨i, rfl⟩
  · intro i
    simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ,
      true_and, Fin.castAddEmb_apply, Fin.natAddEmb_apply,
      Finset.mem_Iic]
    constructor
    · rintro (⟨j, hj⟩ | ⟨j, hj, hji⟩)
      · have hval := congrArg Fin.val hj
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
        omega
      · have hval := congrArg Fin.val hji
        simp only [Fin.val_natAdd] at hval
        change d + i.val ≤ d + k.val
        omega
    · intro hi
      right
      refine ⟨i, ?_, rfl⟩
      change d + i.val ≤ d + k.val at hi
      exact Fin.le_iff_val_le_val.mpr (by omega)

private theorem map_Iic_castAdd_general
    {d m : Nat} (k : Fin d) :
    (Finset.Iic k).map (Fin.castAddEmb m) =
      Finset.Iic (Fin.castAdd m k) := by
  ext q
  refine Fin.addCases ?_ ?_ q
  · intro i
    simp only [Finset.mem_map, Finset.mem_Iic, Fin.castAddEmb_apply]
    constructor
    · rintro ⟨j, hj, hji⟩
      have hji' : j = i := by
        apply Fin.ext
        have hval := congrArg Fin.val hji
        simpa only [Fin.val_castAdd] using hval
      simpa only [hji'] using hj
    · intro hi
      refine ⟨i, ?_, rfl⟩
      exact_mod_cast hi
  · intro i
    simp only [Finset.mem_map, Finset.mem_Iic, Fin.castAddEmb_apply]
    constructor
    · rintro ⟨j, _hj, hji⟩
      have hval := congrArg Fin.val hji
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
      omega
    · intro hi
      have hval : d + i.val ≤ k.val := by
        exact_mod_cast hi
      omega

/-- Prefix partial sums are unchanged when a suffix is concatenated. -/
theorem harperPathPartialSum_addCases_castAdd
    {d m : Nat} (u : Fin d → Real) (v : Fin m → Real) (k : Fin d) :
    Problem520.harperPathPartialSum (Fin.addCases u v) (Fin.castAdd m k) =
      Problem520.harperPathPartialSum u k := by
  unfold Problem520.harperPathPartialSum
  rw [← map_Iic_castAdd_general k, Finset.sum_map]
  simp only [Fin.castAddEmb_apply, Fin.addCases_left]

/-- Exact partial-sum decomposition after concatenating two finite paths. -/
theorem harperPathPartialSum_addCases_natAdd
    {d m : Nat} (u : Fin d → Real) (v : Fin m → Real) (k : Fin m) :
    Problem520.harperPathPartialSum (Fin.addCases u v) (Fin.natAdd d k) =
      (∑ i, u i) + Problem520.harperPathPartialSum v k := by
  unfold Problem520.harperPathPartialSum
  rw [← map_split_Iic_natAdd k]
  have hdisj : Disjoint
      (Finset.univ.map (Fin.castAddEmb m))
      ((Finset.Iic k).map (Fin.natAddEmb d)) := by
    rw [Finset.disjoint_left]
    intro q hleft hright
    obtain ⟨i, _hi, hiq⟩ := Finset.mem_map.mp hleft
    obtain ⟨j, _hj, hjq⟩ := Finset.mem_map.mp hright
    have hval := congrArg Fin.val (hiq.trans hjq.symm)
    simp only [Fin.castAddEmb_apply, Fin.natAddEmb_apply,
      Fin.val_castAdd, Fin.val_natAdd] at hval
    omega
  rw [Finset.sum_union hdisj, Finset.sum_map, Finset.sum_map]
  simp only [Fin.castAddEmb_apply, Fin.natAddEmb_apply,
    Fin.addCases_left, Fin.addCases_right]

theorem harperPairFirstPath_addCases
    {d m : Nat} (u : Fin d → Real × Real) (v : Fin m → Real × Real) :
    harperPairFirstPath (Fin.addCases u v) =
      Fin.addCases (harperPairFirstPath u) (harperPairFirstPath v) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [harperPairFirstPath, Fin.addCases_left]
  · intro j
    simp only [harperPairFirstPath, Fin.addCases_right]

theorem harperPairSecondPath_addCases
    {d m : Nat} (u : Fin d → Real × Real) (v : Fin m → Real × Real) :
    harperPairSecondPath (Fin.addCases u v) =
      Fin.addCases (harperPairSecondPath u) (harperPairSecondPath v) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [harperPairSecondPath, Fin.addCases_left]
  · intro j
    simp only [harperPairSecondPath, Fin.addCases_right]

/-- The two exposed terminal prefix sums of a paired path. -/
def harperPairedPrefixTerminalSum
    {d : Nat} (u : Fin d → Real × Real) : Real × Real :=
  (∑ i, (u i).1, ∑ i, (u i).2)

/-- Split a paired path into consecutive prefix and suffix vectors. -/
def harperPairFinSplit
    {d m : Nat} (v : Fin (d + m) → Real × Real) :
    (Fin d → Real × Real) × (Fin m → Real × Real) :=
  (fun i ↦ v (Fin.castAdd m i), fun j ↦ v (Fin.natAdd d j))

theorem harperPairFinSplit_addCases
    {d m : Nat} (v : Fin (d + m) → Real × Real) :
    Fin.addCases (harperPairFinSplit v).1 (harperPairFinSplit v).2 = v := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [harperPairFinSplit, Fin.addCases_left]
  · intro j
    simp only [harperPairFinSplit, Fin.addCases_right]

/-- Consecutive splitting preserves an arbitrary finite product of paired
probability laws. -/
theorem measurePreserving_harperPairFinSplit
    (d m : Nat) (M : Fin (d + m) → Measure (Real × Real))
    [∀ i, IsProbabilityMeasure (M i)] :
    MeasurePreserving (harperPairFinSplit (d := d) (m := m))
      (Measure.pi M)
      ((Measure.pi (fun i : Fin d ↦ M (Fin.castAdd m i))).prod
        (Measure.pi (fun j : Fin m ↦ M (Fin.natAdd d j)))) := by
  let E : (Fin d ⊕ Fin m → Real × Real) ≃ᵐ
      (Fin (d + m) → Real × Real) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin (d + m) ↦ Real × Real)
      (finSumFinEquiv (m := d) (n := m))
  have hcongr := measurePreserving_piCongrLeft M
    (finSumFinEquiv (m := d) (n := m))
  have hsum := measurePreserving_sumPiEquivProdPi
    (fun sigma : Fin d ⊕ Fin m ↦ M (finSumFinEquiv sigma))
  exact hsum.comp (hcongr.symm E)

theorem measurable_finAddCases_pair (d m : Nat) :
    Measurable
      (fun z : (Fin d → Real × Real) × (Fin m → Real × Real) ↦
        (Fin.addCases z.1 z.2 : Fin (d + m) → Real × Real)) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.addCases
    (motive := fun i ↦ Measurable
      (fun z : (Fin d → Real × Real) × (Fin m → Real × Real) ↦
        (Fin.addCases z.1 z.2 : Fin (d + m) → Real × Real) i))
    ?_ ?_ i
  · intro j
    simpa only [Fin.addCases_left] using
      (measurable_pi_apply j).comp measurable_fst
  · intro j
    simpa only [Fin.addCases_right] using
      (measurable_pi_apply j).comp measurable_snd

/-- Concatenating a fixed prefix with a variable suffix is measurable. -/
theorem measurable_finAddCases_fixedLeft
    {d m : Nat} (u : Fin d → Real × Real) :
    Measurable (fun v : Fin m → Real × Real ↦
      (Fin.addCases u v : Fin (d + m) → Real × Real)) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.addCases
    (motive := fun i ↦ Measurable
      (fun v : Fin m → Real × Real ↦
        (Fin.addCases u v : Fin (d + m) → Real × Real) i))
    ?_ ?_ i
  · intro j
    simpa only [Fin.addCases_left] using measurable_const
  · intro j
    simpa only [Fin.addCases_right] using measurable_pi_apply j

/-- Exact transport of a measurable path event to prefix/suffix product
coordinates. -/
theorem pi_real_eq_prefixSuffix_prod_real
    {d m : Nat} (M : Fin (d + m) → Measure (Real × Real))
    [∀ i, IsProbabilityMeasure (M i)]
    (A : Set (Fin (d + m) → Real × Real)) (hA : MeasurableSet A) :
    (Measure.pi M).real A =
      ((Measure.pi (fun i : Fin d ↦ M (Fin.castAdd m i))).prod
        (Measure.pi (fun j : Fin m ↦ M (Fin.natAdd d j)))).real
          ((fun z : (Fin d → Real × Real) ×
              (Fin m → Real × Real) ↦
                Fin.addCases z.1 z.2) ⁻¹' A) := by
  let split := harperPairFinSplit (d := d) (m := m)
  let join := fun z : (Fin d → Real × Real) ×
      (Fin m → Real × Real) ↦
        (Fin.addCases z.1 z.2 : Fin (d + m) → Real × Real)
  let B := join ⁻¹' A
  have hB : MeasurableSet B :=
    hA.preimage (measurable_finAddCases_pair d m)
  have hsplit := measurePreserving_harperPairFinSplit d m M
  have hpre : split ⁻¹' B = A := by
    ext v
    simp only [split, B, join, Set.mem_preimage]
    rw [harperPairFinSplit_addCases]
  have hmap := map_measureReal_apply (μ := Measure.pi M)
    hsplit.measurable hB
  rw [hsplit.map_eq] at hmap
  change
    ((Measure.pi (fun i : Fin d ↦ M (Fin.castAdd m i))).prod
      (Measure.pi (fun j : Fin m ↦ M (Fin.natAdd d j)))).real B =
        (Measure.pi M).real (split ⁻¹' B) at hmap
  rw [hpre] at hmap
  simpa only [B, join] using hmap.symm

/-- If every suffix fiber of a measurable finite-product event has mass at
most `C`, then the full event has mass at most `C`. -/
theorem pi_real_le_of_suffix_fiberwise
    {d m : Nat} (M : Fin (d + m) → Measure (Real × Real))
    [∀ i, IsProbabilityMeasure (M i)]
    (A : Set (Fin (d + m) → Real × Real)) (hA : MeasurableSet A)
    (C : Real)
    (hfiber : ∀ u : Fin d → Real × Real,
      (Measure.pi (fun j : Fin m ↦ M (Fin.natAdd d j))).real
        {v | Fin.addCases u v ∈ A} ≤ C) :
    (Measure.pi M).real A ≤ C := by
  let R : Measure (Fin d → Real × Real) :=
    Measure.pi (fun i : Fin d ↦ M (Fin.castAdd m i))
  let mu : Measure (Fin m → Real × Real) :=
    Measure.pi (fun j : Fin m ↦ M (Fin.natAdd d j))
  let B : Set ((Fin d → Real × Real) ×
      (Fin m → Real × Real)) :=
    (fun z ↦ Fin.addCases z.1 z.2) ⁻¹' A
  have hB : MeasurableSet B :=
    hA.preimage (measurable_finAddCases_pair d m)
  have htransport := pi_real_eq_prefixSuffix_prod_real M A hA
  have hlift := probability_prod_real_le_of_fiberwise
    R mu mu (A := B) (B := (∅ : Set ((Fin d → Real × Real) ×
      (Fin m → Real × Real)))) hB MeasurableSet.empty 1 C (by
      intro u
      have hu := hfiber u
      change mu.real (Prod.mk u ⁻¹' B) ≤ C at hu
      have hempty : Prod.mk u ⁻¹'
          (∅ : Set ((Fin d → Real × Real) ×
            (Fin m → Real × Real))) = ∅ := rfl
      rw [hempty, measureReal_empty, zero_add]
      simpa only [one_mul] using hu)
  change (Measure.pi M).real A ≤ C
  rw [htransport]
  simpa only [one_mul, measureReal_empty, zero_add] using hlift

/-- Refined prefix/suffix Fubini bound.  If a full event forces its exposed
prefix into `E` and every suffix fiber above `E` has mass at most `C`, then
the full product mass is at most `P(prefix in E) * C`. -/
theorem pi_real_le_prefixEvent_mul_of_suffix_fiberwise
    {d m : Nat} (M : Fin (d + m) → Measure (Real × Real))
    [∀ i, IsProbabilityMeasure (M i)]
    (A : Set (Fin (d + m) → Real × Real)) (hA : MeasurableSet A)
    (E : Set (Fin d → Real × Real)) (hE : MeasurableSet E)
    (C : Real)
    (hprefix : ∀ u : Fin d → Real × Real,
      ∀ v : Fin m → Real × Real, Fin.addCases u v ∈ A → u ∈ E)
    (hfiber : ∀ u ∈ E,
      (Measure.pi (fun j : Fin m ↦ M (Fin.natAdd d j))).real
        {v | Fin.addCases u v ∈ A} ≤ C) :
    (Measure.pi M).real A ≤
      (Measure.pi (fun i : Fin d ↦ M (Fin.castAdd m i))).real E * C := by
  let R : Measure (Fin d → Real × Real) :=
    Measure.pi (fun i : Fin d ↦ M (Fin.castAdd m i))
  let mu : Measure (Fin m → Real × Real) :=
    Measure.pi (fun j : Fin m ↦ M (Fin.natAdd d j))
  let B : Set ((Fin d → Real × Real) ×
      (Fin m → Real × Real)) :=
    (fun z ↦ (Fin.addCases z.1 z.2 : Fin (d + m) → Real × Real)) ⁻¹' A
  have hB : MeasurableSet B :=
    hA.preimage (measurable_finAddCases_pair d m)
  have hBint : Integrable (B.indicator
      (1 : ((Fin d → Real × Real) ×
        (Fin m → Real × Real)) → Real)) (R.prod mu) :=
    (integrable_const (1 : Real)).indicator hB
  have hrepr : (R.prod mu).real B =
      ∫ u, (mu.real (Prod.mk u ⁻¹' B)) ∂ R := by
    rw [← integral_indicator_one (μ := R.prod mu) hB,
      integral_prod _ hBint]
    apply integral_congr_ae
    exact ae_of_all R fun u ↦ by
      change (∫ v, B.indicator
          (1 : ((Fin d → Real × Real) ×
            (Fin m → Real × Real)) → Real) (u, v) ∂mu) =
        mu.real (Prod.mk u ⁻¹' B)
      rw [← integral_indicator_one (μ := mu) (measurable_prodMk_left hB)]
      rfl
  have hsourceIntegrable : Integrable
      (fun u ↦ mu.real (Prod.mk u ⁻¹' B)) R :=
    Measure.integrable_measure_prodMk_left hB
      (measure_ne_top (R.prod mu) B)
  have htargetIntegrable : Integrable
      (fun u ↦ C * E.indicator (1 : (Fin d → Real × Real) → Real) u) R :=
    ((integrable_const (1 : Real)).indicator hE).const_mul C
  have hpoint (u : Fin d → Real × Real) :
      mu.real (Prod.mk u ⁻¹' B) ≤
        C * E.indicator (1 : (Fin d → Real × Real) → Real) u := by
    by_cases hu : u ∈ E
    · simp only [Set.indicator_of_mem hu, Pi.one_apply, mul_one]
      have hfu := hfiber u hu
      change mu.real (Prod.mk u ⁻¹' B) ≤ C at hfu
      exact hfu
    · simp only [Set.indicator_of_notMem hu, mul_zero]
      have hempty : Prod.mk u ⁻¹' B = ∅ := by
        ext v
        constructor
        · intro hv
          exact False.elim (hu (hprefix u v hv))
        · intro hv
          exact False.elim hv
      rw [hempty, measureReal_empty]
  have htransport := pi_real_eq_prefixSuffix_prod_real M A hA
  rw [htransport, hrepr]
  calc
    (∫ u, (mu.real (Prod.mk u ⁻¹' B)) ∂ R) ≤
        ∫ u, (C * E.indicator
          (1 : (Fin d → Real × Real) → Real) u) ∂ R := by
      exact integral_mono hsourceIntegrable htargetIntegrable hpoint
    _ = C * R.real E := by
      rw [integral_const_mul, integral_indicator_one hE]
    _ = R.real E * C := by ring

/-- Three-way Fubini bound.  The first `r` coordinates carry the prefix
event, the next `b` coordinates are an unrestricted oscillatory buffer, and
only the final `m`-coordinate fiber pays the uniform continuation cost.
The buffer has total mass one, so it introduces no loss. -/
theorem pi_real_le_prefixEvent_mul_of_bufferSuffix_fiberwise
    {r b m : Nat} (M : Fin (r + (b + m)) → Measure (Real × Real))
    [∀ i, IsProbabilityMeasure (M i)]
    (A : Set (Fin (r + (b + m)) → Real × Real))
    (hA : MeasurableSet A)
    (E : Set (Fin r → Real × Real)) (hE : MeasurableSet E)
    (C : Real)
    (hprefix : ∀ u : Fin r → Real × Real,
      ∀ z : Fin (b + m) → Real × Real,
        Fin.addCases u z ∈ A → u ∈ E)
    (hfiber : ∀ u ∈ E, ∀ w : Fin b → Real × Real,
      (Measure.pi (fun j : Fin m ↦
        M (Fin.natAdd r (Fin.natAdd b j)))).real
          {v | Fin.addCases u (Fin.addCases w v) ∈ A} ≤ C) :
    (Measure.pi M).real A ≤
      (Measure.pi (fun i : Fin r ↦
        M (Fin.castAdd (b + m) i))).real E * C := by
  apply pi_real_le_prefixEvent_mul_of_suffix_fiberwise M A hA E hE C
    hprefix
  intro u hu
  let N : Fin (b + m) → Measure (Real × Real) := fun j ↦
    M (Fin.natAdd r j)
  have hsection : MeasurableSet
      {z : Fin (b + m) → Real × Real | Fin.addCases u z ∈ A} := by
    exact hA.preimage (measurable_finAddCases_fixedLeft u)
  apply pi_real_le_of_suffix_fiberwise N
    {z : Fin (b + m) → Real × Real | Fin.addCases u z ∈ A}
    hsection C
  intro w
  simpa only [N, Fin.natAdd_natAdd] using hfiber u hu w

/-- Common lower suffix barrier obtained by translating separately by the
two exposed prefix sums and then taking the weaker of the two constraints. -/
def harperPairedSuffixLower
    {d m : Nat} (lower : Fin (d + m) → Real)
    (u : Fin d → Real × Real) (k : Fin m) : Real :=
  min
    (lower (Fin.natAdd d k) - (harperPairedPrefixTerminalSum u).1)
    (lower (Fin.natAdd d k) - (harperPairedPrefixTerminalSum u).2)

/-- Common upper suffix barrier obtained by translating separately by the
two exposed prefix sums and then taking the weaker of the two constraints. -/
def harperPairedSuffixUpper
    {d m : Nat} (upper : Fin (d + m) → Real)
    (u : Fin d → Real × Real) (k : Fin m) : Real :=
  max
    (upper (Fin.natAdd d k) - (harperPairedPrefixTerminalSum u).1)
    (upper (Fin.natAdd d k) - (harperPairedPrefixTerminalSum u).2)

/-- Fixing a paired prefix turns every admissible full continuation into the
literal translated suffix corridor.  No probabilistic argument enters this
step. -/
theorem mem_harperPairedSuffixBarrier_of_addCases_mem
    {d m : Nat} (lower upper : Fin (d + m) → Real)
    (u : Fin d → Real × Real) (v : Fin m → Real × Real)
    (hfull : Fin.addCases u v ∈
      harperPairedPartialSumBarrierSet lower upper) :
    v ∈ harperPairedPartialSumBarrierSet
      (harperPairedSuffixLower lower u)
      (harperPairedSuffixUpper upper u) := by
  rcases hfull with ⟨hfirst, hsecond⟩
  change harperPairFirstPath (Fin.addCases u v) ∈
    Problem520.harperPartialSumBarrierSet lower upper at hfirst
  change harperPairSecondPath (Fin.addCases u v) ∈
    Problem520.harperPartialSumBarrierSet lower upper at hsecond
  rw [harperPairFirstPath_addCases] at hfirst
  rw [harperPairSecondPath_addCases] at hsecond
  rw [Problem520.mem_harperPartialSumBarrierSet] at hfirst hsecond
  change
    harperPairFirstPath v ∈ Problem520.harperPartialSumBarrierSet
        (harperPairedSuffixLower lower u)
        (harperPairedSuffixUpper upper u) ∧
      harperPairSecondPath v ∈ Problem520.harperPartialSumBarrierSet
        (harperPairedSuffixLower lower u)
        (harperPairedSuffixUpper upper u)
  rw [Problem520.mem_harperPartialSumBarrierSet,
    Problem520.mem_harperPartialSumBarrierSet]
  constructor
  · intro k
    have hf := hfirst (Fin.natAdd d k)
    have hsum := harperPathPartialSum_addCases_natAdd
      (harperPairFirstPath u) (harperPairFirstPath v) k
    rw [hsum] at hf
    constructor
    · exact (min_le_left _ _).trans (by
        dsimp only [harperPairedPrefixTerminalSum,
          harperPairFirstPath] at hf ⊢
        linarith [hf.1])
    · exact (by
        apply le_max_of_le_left
        dsimp only [harperPairedPrefixTerminalSum,
          harperPairFirstPath] at hf ⊢
        linarith [hf.2])
  · intro k
    have hs := hsecond (Fin.natAdd d k)
    have hsum := harperPathPartialSum_addCases_natAdd
      (harperPairSecondPath u) (harperPairSecondPath v) k
    rw [hsum] at hs
    constructor
    · exact (min_le_right _ _).trans (by
        dsimp only [harperPairedPrefixTerminalSum,
          harperPairSecondPath] at hs ⊢
        linarith [hs.1])
    · exact (by
        apply le_max_of_le_right
        dsimp only [harperPairedPrefixTerminalSum,
          harperPairSecondPath] at hs ⊢
        linarith [hs.2])

/-- Every extendable nonempty prefix of the final logarithmic ballot has both
terminal sums in the coarse interval `[-64d, 1]`. -/
theorem harperPairedPrefixTerminalSum_bounds_of_logBallot_continuation
    {start d m : Nat} (hd : 0 < d)
    (u : Fin d → Real × Real) (v : Fin m → Real × Real)
    (hfull : Fin.addCases u v ∈ harperPairedPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start (d + m))
      (harper1144LogBallotUpperBarrier (d + m))) :
    -64 * (d : Real) ≤ (harperPairedPrefixTerminalSum u).1 ∧
      (harperPairedPrefixTerminalSum u).1 ≤ 1 ∧
      -64 * (d : Real) ≤ (harperPairedPrefixTerminalSum u).2 ∧
      (harperPairedPrefixTerminalSum u).2 ≤ 1 := by
  let last : Fin d := ⟨d - 1, by omega⟩
  let fullLast : Fin (d + m) := Fin.castAdd m last
  rcases hfull with ⟨hfirst, hsecond⟩
  change harperPairFirstPath (Fin.addCases u v) ∈
    Problem520.harperPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start (d + m))
      (harper1144LogBallotUpperBarrier (d + m)) at hfirst
  change harperPairSecondPath (Fin.addCases u v) ∈
    Problem520.harperPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start (d + m))
      (harper1144LogBallotUpperBarrier (d + m)) at hsecond
  rw [harperPairFirstPath_addCases,
    Problem520.mem_harperPartialSumBarrierSet] at hfirst
  rw [harperPairSecondPath_addCases,
    Problem520.mem_harperPartialSumBarrierSet] at hsecond
  have hf := hfirst fullLast
  have hs := hsecond fullLast
  have hsumFirst := harperPathPartialSum_addCases_castAdd
    (harperPairFirstPath u) (harperPairFirstPath v) last
  have hsumSecond := harperPathPartialSum_addCases_castAdd
    (harperPairSecondPath u) (harperPairSecondPath v) last
  change Problem520.harperPathPartialSum
      (Fin.addCases (harperPairFirstPath u) (harperPairFirstPath v))
        fullLast = _ at hsumFirst
  change Problem520.harperPathPartialSum
      (Fin.addCases (harperPairSecondPath u) (harperPairSecondPath v))
        fullLast = _ at hsumSecond
  rw [hsumFirst] at hf
  rw [hsumSecond] at hs
  have hIic : Finset.Iic last = Finset.univ := by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
    apply Fin.le_iff_val_le_val.mpr
    dsimp only [last]
    omega
  unfold Problem520.harperPathPartialSum at hf hs
  rw [hIic] at hf hs
  have hlower := le_max_right
    (harperScheduledAutomaticLowerBarrier start (d + m) fullLast)
    (-64 * ((fullLast.val + 1 : Nat) : Real))
  have hfullLastVal : fullLast.val + 1 = d := by
    dsimp only [fullLast, last]
    simp only [Fin.val_castAdd]
    omega
  have hupper := harper1144LogBallotUpperBarrier_le_one (d + m) fullLast
  dsimp only [harperPairedPrefixTerminalSum, harperPairFirstPath,
    harperPairSecondPath]
  rw [hfullLastVal] at hlower
  simp only [harper1144LogBallotLowerBarrier] at hf hs
  rw [hfullLastVal] at hf hs
  simp only [harperPairFirstPath, harperPairSecondPath] at hf hs
  exact ⟨hlower.trans hf.1, hf.2.trans hupper,
    hlower.trans hs.1, hs.2.trans hupper⟩

/-- On an extendable prefix of length `d`, every translated suffix upper
barrier is at most `64d`. -/
theorem harperPairedSuffixUpper_logBallot_le
    {start d m : Nat} (hd : 0 < d)
    (u : Fin d → Real × Real) (v : Fin m → Real × Real)
    (hfull : Fin.addCases u v ∈ harperPairedPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start (d + m))
      (harper1144LogBallotUpperBarrier (d + m)))
    (k : Fin m) :
    harperPairedSuffixUpper (harper1144LogBallotUpperBarrier (d + m)) u k ≤
      64 * (d : Real) := by
  have hb := harperPairedPrefixTerminalSum_bounds_of_logBallot_continuation
    hd u v hfull
  dsimp only [harperPairedPrefixTerminalSum] at hb
  have helapsedNat : 2 ≤ d + k.val + 1 := by omega
  have helapsed : (2 : Real) ≤ ((d + k.val + 1 : Nat) : Real) := by
    exact_mod_cast helapsedNat
  have hlog : Real.log 2 ≤ Real.log ((d + k.val + 1 : Nat) : Real) :=
    Real.log_le_log (by norm_num) helapsed
  have hupperZero :
      harper1144LogBallotUpperBarrier (d + m) (Fin.natAdd d k) ≤ 0 := by
    unfold harper1144LogBallotUpperBarrier
    simp only [Fin.val_natAdd]
    nlinarith [Real.log_two_gt_d9]
  unfold harperPairedSuffixUpper
  apply max_le
  · dsimp only [harperPairedPrefixTerminalSum]
    linarith [hb.1]
  · dsimp only [harperPairedPrefixTerminalSum]
    linarith [hb.2.2.1]

/-- Pointwise form of the translated suffix lower bound.  At suffix time
`k`, the automatic full-path guard has only descended to
`-64(d+k+1)`, and each exposed prefix endpoint is at most one.  Retaining
this elapsed-time dependence is what keeps the natural post-coherence
shifted-lattice cells inside their moderate boxes. -/
theorem neg_sixtyFour_mul_suffixElapsed_sub_one_le_harperPairedSuffixLower_logBallot
    {start d m : Nat} (hd : 0 < d)
    (u : Fin d → Real × Real) (v : Fin m → Real × Real)
    (hfull : Fin.addCases u v ∈ harperPairedPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start (d + m))
      (harper1144LogBallotUpperBarrier (d + m)))
    (k : Fin m) :
    -64 * ((d + k.val + 1 : Nat) : Real) - 1 ≤
      harperPairedSuffixLower
        (harper1144LogBallotLowerBarrier start (d + m)) u k := by
  have hb := harperPairedPrefixTerminalSum_bounds_of_logBallot_continuation
    hd u v hfull
  dsimp only [harperPairedPrefixTerminalSum] at hb
  have hlower :
      -64 * ((d + k.val + 1 : Nat) : Real) ≤
        harper1144LogBallotLowerBarrier start (d + m)
          (Fin.natAdd d k) := by
    exact le_max_right _ _
  unfold harperPairedSuffixLower
  apply le_min
  · dsimp only [harperPairedPrefixTerminalSum]
    linarith [hb.2.1]
  · dsimp only [harperPairedPrefixTerminalSum]
    linarith [hb.2.2.2]

/-- The common translated suffix lower barrier stays above the coarse global
level `-64(d+m)-1`. -/
theorem neg_sixtyFour_mul_add_sub_one_le_harperPairedSuffixLower_logBallot
    {start d m : Nat} (hd : 0 < d)
    (u : Fin d → Real × Real) (v : Fin m → Real × Real)
    (hfull : Fin.addCases u v ∈ harperPairedPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start (d + m))
      (harper1144LogBallotUpperBarrier (d + m)))
    (k : Fin m) :
    -64 * ((d + m : Nat) : Real) - 1 ≤
      harperPairedSuffixLower
        (harper1144LogBallotLowerBarrier start (d + m)) u k := by
  have hb := harperPairedPrefixTerminalSum_bounds_of_logBallot_continuation
    hd u v hfull
  dsimp only [harperPairedPrefixTerminalSum] at hb
  have helapsed : (d + k.val + 1 : Real) ≤ d + m := by
    exact_mod_cast (show d + k.val + 1 ≤ d + m by omega)
  have hlower :
      -64 * ((d + k.val + 1 : Nat) : Real) ≤
        harper1144LogBallotLowerBarrier start (d + m)
          (Fin.natAdd d k) := by
    exact le_max_right _ _
  norm_num only [Nat.cast_add, Nat.cast_one] at hlower
  unfold harperPairedSuffixLower
  norm_num only [Nat.cast_add] at ⊢
  apply le_min
  · dsimp only [harperPairedPrefixTerminalSum]
    linarith [hb.2.1]
  · dsimp only [harperPairedPrefixTerminalSum]
    linarith [hb.2.2.2]

/-- The common translated suffix corridor has width at most `128N+1`, where
`N=d+m` is the original full path length. -/
theorem harperPairedSuffix_logBallot_corridorWidth_le
    {start d m : Nat} (hd : 0 < d)
    (u : Fin d → Real × Real) (v : Fin m → Real × Real)
    (hfull : Fin.addCases u v ∈ harperPairedPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start (d + m))
      (harper1144LogBallotUpperBarrier (d + m)))
    (k : Fin m) :
    harperPairedSuffixUpper (harper1144LogBallotUpperBarrier (d + m)) u k -
        harperPairedSuffixLower
          (harper1144LogBallotLowerBarrier start (d + m)) u k ≤
      128 * ((d + m : Nat) : Real) + 1 := by
  have hu := harperPairedSuffixUpper_logBallot_le hd u v hfull k
  have hl :=
    neg_sixtyFour_mul_add_sub_one_le_harperPairedSuffixLower_logBallot
      hd u v hfull k
  have hdle : (d : Real) ≤ d + m := by norm_num
  norm_num only [Nat.cast_add] at hu hl ⊢
  linarith

/-! ## Replacement with a cutoff scale larger than the suffix length -/

/-- Finite replacement for `m` suffix coordinates using a possibly larger
analytic cutoff scale `q`.  This is the form needed because the translated
lower guard has width governed by the original path, while only `m`
coordinates remain random. -/
theorem harperScheduledTwoHeightScaledBarrier_finiteReplacement
    (y start m q : Nat) (t s : Real)
    (lower upper : Fin m → Real)
    (hq : 4 ≤ q) (hmq : m ≤ q)
    (hcorridor : ∀ i, upper i - lower i ≤ 64 * (q : Real) + 1)
    (hfrequency : ∀ i : Fin m,
      4 * (q : Real) ^ (6 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hendpoint : ∀ i : Fin m,
      1048576 * (q : Real) ^ (48 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hcovariance : ∀ i : Fin m,
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t s| ≤ 1 / (q : Real) ^ (40 : Nat)) :
    let beta : Real :=
      ((1 - 2 / (q : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
    let expand : Real := 4 * (1 / (q : Real) ^ (2 : Nat))
    let err : Real := 6 / (q : Real) ^ (4 : Nat)
    let P : Fin m → Measure (Real × Real) := fun i ↦
      harperTwoHeightBallotBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
    let Q : Fin m → Measure (Real × Real) := fun i ↦
      harperTwoHeightDriftedIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
    beta ^ m * (Measure.pi P).real
        (harperPairedPartialSumBarrierSet lower upper) ≤
      (Measure.pi Q).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ lower k - (m : Real) * expand)
            (fun k ↦ upper k + (m : Real) * expand)) +
        (m : Real) * err := by
  dsimp only
  let beta : Real :=
    ((1 - 2 / (q : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
  let expand : Real := 4 * (1 / (q : Real) ^ (2 : Nat))
  let err : Real := 6 / (q : Real) ^ (4 : Nat)
  let P : Fin m → Measure (Real × Real) := fun i ↦
    harperTwoHeightBallotBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  let Q : Fin m → Measure (Real × Real) := fun i ↦
    harperTwoHeightDriftedIndependentGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  have hqR : (4 : Real) ≤ q := by exact_mod_cast hq
  have hqPos : (0 : Real) < q := by linarith
  have hfracNonneg : 0 ≤ 2 / (q : Real) ^ (4 : Nat) := by positivity
  have hqPow : (2 : Real) ≤ (q : Real) ^ (4 : Nat) := by
    nlinarith [sq_nonneg ((q : Real) ^ (2 : Nat) - 1)]
  have hfracOne : 2 / (q : Real) ^ (4 : Nat) ≤ 1 := by
    exact (div_le_one (by positivity)).mpr hqPow
  have hbeta0 : 0 ≤ beta := by
    dsimp only [beta]
    positivity
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    have huLower : -1 ≤ 1 - 2 / (q : Real) ^ (4 : Nat) := by linarith
    have huUpper : 1 - 2 / (q : Real) ^ (4 : Nat) ≤ 1 := by linarith
    have huSq :
        (1 - 2 / (q : Real) ^ (4 : Nat)) ^ (2 : Nat) ≤ 1 := by
      nlinarith [sq_nonneg
        (1 - 2 / (q : Real) ^ (4 : Nat) - 1),
        sq_nonneg (1 - 2 / (q : Real) ^ (4 : Nat) + 1)]
    nlinarith [sq_nonneg
      ((1 - 2 / (q : Real) ^ (4 : Nat)) ^ (2 : Nat))]
  have herr : 0 ≤ err := by
    dsimp only [err]
    positivity
  have hexpand : 0 ≤ expand := by
    dsimp only [expand]
    positivity
  apply pi_harperPairedBarrier_finite_replacement
    P Q lower upper beta err expand (65 * (q : Real) - 1)
    hbeta0 hbeta1 herr hexpand
  · intro r hr
    let i : Fin m := ⟨r, hr⟩
    have hbase := hcorridor i
    have hrq : (r : Real) ≤ q := by
      exact_mod_cast (show r ≤ q by omega)
    have hsmall : 2 * (r : Real) * expand ≤ 2 := by
      dsimp only [expand]
      have hden : 0 < (q : Real) ^ (2 : Nat) := by positivity
      rw [show 2 * (r : Real) * (4 * (1 / (q : Real) ^ (2 : Nat))) =
        (8 * (r : Real)) / (q : Real) ^ (2 : Nat) by
          field_simp
          ring]
      apply (div_le_iff₀ hden).mpr
      nlinarith
    change upper i - lower i + 2 * (r : Real) * expand ≤
      65 * (q : Real) - 1
    linarith
  · intro i a b c d hab hcd habWidth hcdWidth
    dsimp only [P, Q, beta, expand, err]
    exact
      harperScheduledTwoHeightBallotClosedRectangleMass_le_driftedGaussian_cutoff
        y (start + i.val) q t s hq hab hcd habWidth hcdWidth
          (hfrequency i) (hendpoint i) (hcovariance i)

/-- Drift removal for `m` coordinates at the larger cutoff scale `q`. -/
theorem harperScheduledScaledDriftedGaussianPath_real_le_independent
    (y start m q : Nat) (t s : Real) (hq : 1 ≤ q) (hmq : m ≤ q)
    (lower upper : Fin m → Real)
    (hdriftFirst : ∀ i : Fin m,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t t| ≤ 1 / (q : Real) ^ (2 : Nat))
    (hdriftSecond : ∀ i : Fin m,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s s s| ≤ 1 / (q : Real) ^ (2 : Nat)) :
    (Measure.pi (fun i : Fin m ↦
      harperTwoHeightDriftedIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
        (harperPairedPartialSumBarrierSet lower upper) ≤
      (Measure.pi (fun i : Fin m ↦
        harperTwoHeightIndependentGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
        (harperPairedPartialSumBarrierSet
          (fun k ↦ lower k - 1 / (q : Real))
          (fun k ↦ upper k + 1 / (q : Real))) := by
  let G : Fin m → Measure (Real × Real) := fun i ↦
    harperTwoHeightIndependentGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  let drift : Fin m → Real × Real := fun i ↦
    harperTwoHeightBallotBlockDrift y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  have hqPos : (0 : Real) < q := by exact_mod_cast hq
  have hprefix
      (coord : (Real × Real) → Real)
      (hcoord : ∀ i : Fin m, |coord (drift i)| ≤
        1 / (q : Real) ^ (2 : Nat))
      (k : Fin m) :
      |∑ i ∈ Finset.Iic k, coord (drift i)| ≤ 1 / (q : Real) := by
    calc
      |∑ i ∈ Finset.Iic k, coord (drift i)| ≤
          ∑ i ∈ Finset.Iic k, |coord (drift i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.Iic k,
          1 / (q : Real) ^ (2 : Nat) := by
        exact Finset.sum_le_sum fun i _hi ↦ hcoord i
      _ = ((k.val + 1 : Nat) : Real) *
          (1 / (q : Real) ^ (2 : Nat)) := by
        rw [Finset.sum_const, Fin.card_Iic, nsmul_eq_mul]
      _ ≤ (q : Real) * (1 / (q : Real) ^ (2 : Nat)) := by
        gcongr
        exact_mod_cast (show k.val + 1 ≤ q by omega)
      _ = 1 / (q : Real) := by field_simp
  have hfirst : ∀ k : Fin m,
      |∑ i ∈ Finset.Iic k, (drift i).1| ≤ 1 / (q : Real) := by
    apply hprefix Prod.fst
    intro i
    exact hdriftFirst i
  have hsecond : ∀ k : Fin m,
      |∑ i ∈ Finset.Iic k, (drift i).2| ≤ 1 / (q : Real) := by
    apply hprefix Prod.snd
    intro i
    exact hdriftSecond i
  have hmass := pi_translated_pairedBarrier_real_le_relaxed
    G drift lower upper (1 / (q : Real)) hfirst hsecond
  simpa only [G, drift, harperTwoHeightBallotBlockDrift,
    harperTwoHeightDriftedIndependentGaussianBlockLaw] using hmass

/-- End-to-end scaled replacement, including deterministic drift removal. -/
theorem harperScheduledTwoHeightScaledBarrierPath_le_independentGaussian
    (y start m q : Nat) (t s : Real)
    (lower upper : Fin m → Real)
    (hq : 4 ≤ q) (hmq : m ≤ q)
    (hcorridor : ∀ i, upper i - lower i ≤ 64 * (q : Real) + 1)
    (hfrequency : ∀ i : Fin m,
      4 * (q : Real) ^ (6 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hendpoint : ∀ i : Fin m,
      1048576 * (q : Real) ^ (48 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hcovariance : ∀ i : Fin m,
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t s| ≤ 1 / (q : Real) ^ (40 : Nat))
    (hdriftFirst : ∀ i : Fin m,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t t| ≤ 1 / (q : Real) ^ (2 : Nat))
    (hdriftSecond : ∀ i : Fin m,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s s s| ≤ 1 / (q : Real) ^ (2 : Nat)) :
    let beta : Real :=
      ((1 - 2 / (q : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
    let D : Real :=
      (m : Real) * (4 * (1 / (q : Real) ^ (2 : Nat))) +
        1 / (q : Real)
    beta ^ m * (Measure.pi (fun i : Fin m ↦
      harperTwoHeightBallotBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
          (harperPairedPartialSumBarrierSet lower upper) ≤
      (Measure.pi (fun i : Fin m ↦
        harperTwoHeightIndependentGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ lower k - D) (fun k ↦ upper k + D)) +
        (m : Real) * (6 / (q : Real) ^ (4 : Nat)) := by
  dsimp only
  let expand : Real := 4 * (1 / (q : Real) ^ (2 : Nat))
  let D : Real := (m : Real) * expand + 1 / (q : Real)
  let Q : Fin m → Measure (Real × Real) := fun i ↦
    harperTwoHeightDriftedIndependentGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  have hreplace := harperScheduledTwoHeightScaledBarrier_finiteReplacement
    y start m q t s lower upper hq hmq hcorridor
      hfrequency hendpoint hcovariance
  dsimp only at hreplace
  have hremove := harperScheduledScaledDriftedGaussianPath_real_le_independent
    y start m q t s (by omega) hmq
      (fun k ↦ lower k - (m : Real) * expand)
      (fun k ↦ upper k + (m : Real) * expand)
      hdriftFirst hdriftSecond
  have hlower :
      (fun k : Fin m ↦
        (lower k - (m : Real) * expand) - 1 / (q : Real)) =
        fun k ↦ lower k - D := by
    funext k
    dsimp only [D]
    ring
  have hupper :
      (fun k : Fin m ↦
        (upper k + (m : Real) * expand) + 1 / (q : Real)) =
        fun k ↦ upper k + D := by
    funext k
    dsimp only [D]
    ring
  rw [hlower, hupper] at hremove
  exact hreplace.trans (add_le_add hremove le_rfl)

/-- Quantitative arbitrary-corridor suffix bound with a cutoff scale `q`
larger than the number `m` of remaining blocks. -/
theorem harperScheduledTwoHeightScaledArbitraryBarrier_real_le
    (y start m q : Nat) (t s : Real)
    (lower upper : Fin m → Real) (a : Real)
    (hm : 4 ≤ m) (hq : 4 ≤ q) (hmq : m ≤ q)
    (ha : 0 ≤ a) (hupperBarrier : ∀ k, upper k ≤ a)
    (hcorridor : ∀ i, upper i - lower i ≤ 64 * (q : Real) + 1)
    (hfrequency : ∀ i : Fin m,
      4 * (q : Real) ^ (6 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hendpoint : ∀ i : Fin m,
      1048576 * (q : Real) ^ (48 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + i.val) : Real))
    (hcovariance : ∀ i : Fin m,
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t s| ≤ 1 / (q : Real) ^ (40 : Nat))
    (hdriftFirst : ∀ i : Fin m,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s t t| ≤ 1 / (q : Real) ^ (2 : Nat))
    (hdriftSecond : ∀ i : Fin m,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + i.val))
          t s s s| ≤ 1 / (q : Real) ^ (2 : Nat))
    (hvarianceFirst : ∀ i : Fin m,
      (1 / 3 : Real) <
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s t t ∧
        harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s t t < (3 / 8 : Real))
    (hvarianceSecond : ∀ i : Fin m,
      (1 / 3 : Real) <
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s s s ∧
        harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t s s s < (3 / 8 : Real)) :
    (Measure.pi (fun i : Fin m ↦
      harperTwoHeightBallotBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
        (harperPairedPartialSumBarrierSet lower upper) ≤
      5000 * (a + 4) ^ (2 : Nat) * (m : Real)⁻¹ := by
  let beta : Real :=
    ((1 - 2 / (q : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
  let D : Real :=
    (m : Real) * (4 * (1 / (q : Real) ^ (2 : Nat))) +
      1 / (q : Real)
  let p : Real :=
    (Measure.pi (fun i : Fin m ↦
      harperTwoHeightBallotBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
        (harperPairedPartialSumBarrierSet lower upper)
  have hpath :=
    harperScheduledTwoHeightScaledBarrierPath_le_independentGaussian
      y start m q t s lower upper hq hmq hcorridor
        hfrequency hendpoint hcovariance hdriftFirst hdriftSecond
  dsimp only at hpath
  let variance₁ : Fin m → NNReal := fun i ↦
    harperTwoHeightCoordinateVarianceNNReal y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s t
  let variance₂ : Fin m → NNReal := fun i ↦
    harperTwoHeightCoordinateVarianceNNReal y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s s
  have hmPos : 0 < m := by omega
  have hmR : (4 : Real) ≤ m := by exact_mod_cast hm
  have hqR : (4 : Real) ≤ q := by exact_mod_cast hq
  have hqPos : (0 : Real) < q := by positivity
  have hmPosR : (0 : Real) < m := by positivity
  have hmqR : (m : Real) ≤ q := by exact_mod_cast hmq
  have hqSq : (m : Real) ^ (2 : Nat) ≤ (q : Real) ^ (2 : Nat) := by
    gcongr
  have hDle : D ≤ 5 / (m : Real) := by
    dsimp only [D]
    have hratio :
        (m : Real) / (q : Real) ^ (2 : Nat) ≤ 1 / (m : Real) := by
      apply (div_le_iff₀ (by positivity : (0 : Real) <
        (q : Real) ^ (2 : Nat))).mpr
      rw [show 1 / (m : Real) * (q : Real) ^ (2 : Nat) =
        (q : Real) ^ (2 : Nat) / (m : Real) by ring]
      exact (le_div_iff₀ hmPosR).mpr (by nlinarith [hqSq])
    have hfirst :
        (m : Real) * (4 * (1 / (q : Real) ^ (2 : Nat))) ≤
          4 / (m : Real) := by
      calc
        _ = 4 * ((m : Real) / (q : Real) ^ (2 : Nat)) := by ring
        _ ≤ 4 * (1 / (m : Real)) := by gcongr
        _ = 4 / (m : Real) := by ring
    have hsecond : 1 / (q : Real) ≤ 1 / (m : Real) := by
      exact one_div_le_one_div_of_le hmPosR hmqR
    calc
      _ ≤ 4 / (m : Real) + 1 / (m : Real) :=
        add_le_add hfirst hsecond
      _ = 5 / (m : Real) := by ring
  have hDleTwo : D ≤ 2 := by
    have hfive : 5 / (m : Real) ≤ 2 := by
      apply (div_le_iff₀ hmPosR).mpr
      nlinarith
    exact hDle.trans hfive
  have hupperRelax (k : Fin m) : upper k + D ≤ a + 2 := by
    linarith [hupperBarrier k]
  have hlower₁ (i : Fin m) : (1 / 3 : NNReal) ≤ variance₁ i := by
    apply NNReal.coe_le_coe.mp
    change (1 / 3 : Real) ≤
      harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s t t
    exact (hvarianceFirst i).1.le
  have hupper₁ (i : Fin m) : variance₁ i ≤ (3 / 8 : NNReal) := by
    apply NNReal.coe_le_coe.mp
    change harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s t t ≤
      (3 / 8 : Real)
    exact (hvarianceFirst i).2.le
  have hlower₂ (i : Fin m) : (1 / 3 : NNReal) ≤ variance₂ i := by
    apply NNReal.coe_le_coe.mp
    change (1 / 3 : Real) ≤
      harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s s s
    exact (hvarianceSecond i).1.le
  have hupper₂ (i : Fin m) : variance₂ i ≤ (3 / 8 : NNReal) := by
    apply NNReal.coe_le_coe.mp
    change harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s s s ≤
      (3 / 8 : Real)
    exact (hvarianceSecond i).2.le
  have hgaussian := independentGaussianPairedBarrier_real_le
    m hmPos variance₁ variance₂
    (fun k ↦ lower k - D) (fun k ↦ upper k + D)
    (a + 2) (by linarith) hupperRelax
    hlower₁ hupper₁ hlower₂ hupper₂
  have hsum : a + 2 + 2 = a + 4 := by ring
  rw [hsum] at hgaussian
  have hgaussian' :
      (Measure.pi (fun i : Fin m ↦
        harperTwoHeightIndependentGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
          (harperPairedPartialSumBarrierSet
            (fun k ↦ lower k - D) (fun k ↦ upper k + D)) ≤
        4096 * (a + 4) ^ (2 : Nat) * (m : Real)⁻¹ := by
    simpa only [variance₁, variance₂,
      harperTwoHeightIndependentGaussianBlockLaw] using hgaussian
  have hweighted : beta ^ m * p ≤
      4096 * (a + 4) ^ (2 : Nat) * (m : Real)⁻¹ +
        (m : Real) * (6 / (q : Real) ^ (4 : Nat)) := by
    dsimp only [beta, D, p]
    exact hpath.trans (add_le_add hgaussian' le_rfl)
  have herrSmall :
      (m : Real) * (6 / (q : Real) ^ (4 : Nat)) ≤
        6 / (m : Real) := by
    have hqSqLeFourth : (q : Real) ^ (2 : Nat) ≤
        (q : Real) ^ (4 : Nat) := by
      have hqSqOne : (1 : Real) ≤ (q : Real) ^ (2 : Nat) := by
        nlinarith [sq_nonneg ((q : Real) - 1)]
      calc
        (q : Real) ^ (2 : Nat) ≤
            (q : Real) ^ (2 : Nat) * (q : Real) ^ (2 : Nat) := by
          nlinarith
        _ = (q : Real) ^ (4 : Nat) := by ring
    have hmSqLeFourth : (m : Real) ^ (2 : Nat) ≤
        (q : Real) ^ (4 : Nat) := hqSq.trans hqSqLeFourth
    have hratio :
        (m : Real) / (q : Real) ^ (4 : Nat) ≤ 1 / (m : Real) := by
      apply (div_le_iff₀ (by positivity : (0 : Real) <
        (q : Real) ^ (4 : Nat))).mpr
      rw [show 1 / (m : Real) * (q : Real) ^ (4 : Nat) =
        (q : Real) ^ (4 : Nat) / (m : Real) by ring]
      exact (le_div_iff₀ hmPosR).mpr (by nlinarith [hmSqLeFourth])
    calc
      _ = 6 * ((m : Real) / (q : Real) ^ (4 : Nat)) := by ring
      _ ≤ 6 * (1 / (m : Real)) := by gcongr
      _ = 6 / (m : Real) := by ring
  have haSq : (16 : Real) ≤ (a + 4) ^ (2 : Nat) := by
    nlinarith [sq_nonneg a]
  have hright :
      4096 * (a + 4) ^ (2 : Nat) * (m : Real)⁻¹ +
          (m : Real) * (6 / (q : Real) ^ (4 : Nat)) ≤
        4375 * (a + 4) ^ (2 : Nat) * (m : Real)⁻¹ := by
    calc
      _ ≤ 4096 * (a + 4) ^ (2 : Nat) * (m : Real)⁻¹ +
          6 / (m : Real) := add_le_add le_rfl herrSmall
      _ = (4096 * (a + 4) ^ (2 : Nat) + 6) *
          (m : Real)⁻¹ := by field_simp
      _ ≤ (4375 * (a + 4) ^ (2 : Nat)) * (m : Real)⁻¹ := by
        gcongr
        nlinarith
      _ = _ := by ring
  have hretBase : (7 / 8 : Real) ≤
      1 - 8 / (q : Real) ^ (3 : Nat) := by
    have hden : 0 < (q : Real) ^ (3 : Nat) := by positivity
    have hqCube : (64 : Real) ≤ (q : Real) ^ (3 : Nat) := by
      calc
        (64 : Real) = (4 : Real) ^ (3 : Nat) := by norm_num
        _ ≤ (q : Real) ^ (3 : Nat) := by gcongr
    have hinv : 8 / (q : Real) ^ (3 : Nat) ≤ 1 / 8 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith
    linarith
  have hret : (7 / 8 : Real) ≤ beta ^ m :=
    hretBase.trans (by
      dsimp only [beta]
      exact one_sub_eight_div_cube_le_harperTwoHeightCutoff_retention
        (m := m) (n := q) (by omega) hmq)
  have hp0 : 0 ≤ p := by
    dsimp only [p]
    exact measureReal_nonneg
  have hpScaled : (7 / 8 : Real) * p ≤
      4375 * (a + 4) ^ (2 : Nat) * (m : Real)⁻¹ :=
    (mul_le_mul_of_nonneg_right hret hp0).trans
      (hweighted.trans hright)
  change p ≤ 5000 * (a + 4) ^ (2 : Nat) * (m : Real)⁻¹
  have hscaledTarget :
      (7 / 8 : Real) *
          (5000 * (a + 4) ^ (2 : Nat) * (m : Real)⁻¹) =
        4375 * (a + 4) ^ (2 : Nat) * (m : Real)⁻¹ := by ring
  exact (mul_le_mul_iff_right₀ (by norm_num : (0 : Real) < 7 / 8)).mp (by
    rw [hscaledTarget]
    exact hpScaled)

/-! ## The exact logarithmic suffix bound -/

/-- Once an elapsed prefix of length `d` is exposed, the remaining `m`
blocks of the final logarithmic ballot cost
`O((d+1)^2/m)` under the two-height tilted product law. -/
theorem harperScheduledTwoHeightLogBallotSuffix_real_le
    (y start d m : Nat) (t s : Real)
    (hd : 0 < d) (hm : 4 ≤ m)
    (u : Fin d → Real × Real) (v : Fin m → Real × Real)
    (hfull : Fin.addCases u v ∈ harperPairedPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start (d + m))
      (harper1144LogBallotUpperBarrier (d + m)))
    (hfrequency : ∀ i : Fin m,
      4 * ((2 * (d + m) : Nat) : Real) ^ (6 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + d + i.val) : Real))
    (hendpoint : ∀ i : Fin m,
      1048576 * ((2 * (d + m) : Nat) : Real) ^ (48 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + d + i.val) : Real))
    (hcovariance : ∀ i : Fin m,
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
          t s t s| ≤
        1 / ((2 * (d + m) : Nat) : Real) ^ (40 : Nat))
    (hdriftFirst : ∀ i : Fin m,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
          t s t t| ≤
        1 / ((2 * (d + m) : Nat) : Real) ^ (2 : Nat))
    (hdriftSecond : ∀ i : Fin m,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
          t s s s| ≤
        1 / ((2 * (d + m) : Nat) : Real) ^ (2 : Nat))
    (hvarianceFirst : ∀ i : Fin m,
      (1 / 3 : Real) <
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
            t s t t ∧
        harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
            t s t t < (3 / 8 : Real))
    (hvarianceSecond : ∀ i : Fin m,
      (1 / 3 : Real) <
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
            t s s s ∧
        harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
            t s s s < (3 / 8 : Real)) :
    (Measure.pi (fun i : Fin m ↦
      harperTwoHeightBallotBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + d + i.val)) t s)).real
        (harperPairedPartialSumBarrierSet
          (harperPairedSuffixLower
            (harper1144LogBallotLowerBarrier start (d + m)) u)
          (harperPairedSuffixUpper
            (harper1144LogBallotUpperBarrier (d + m)) u)) ≤
      5000 * (64 * (d : Real) + 4) ^ (2 : Nat) * (m : Real)⁻¹ := by
  let q : Nat := 2 * (d + m)
  have hq : 4 ≤ q := by
    dsimp only [q]
    omega
  have hmq : m ≤ q := by
    dsimp only [q]
    omega
  apply harperScheduledTwoHeightScaledArbitraryBarrier_real_le
    y (start + d) m q t s
    (harperPairedSuffixLower
      (harper1144LogBallotLowerBarrier start (d + m)) u)
    (harperPairedSuffixUpper
      (harper1144LogBallotUpperBarrier (d + m)) u)
    (64 * (d : Real)) hm hq hmq (by positivity)
  · intro k
    exact harperPairedSuffixUpper_logBallot_le hd u v hfull k
  · intro k
    have hw := harperPairedSuffix_logBallot_corridorWidth_le
      hd u v hfull k
    dsimp only [q]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    linarith
  · simpa only [q, add_assoc] using hfrequency
  · simpa only [q, add_assoc] using hendpoint
  · simpa only [q, add_assoc] using hcovariance
  · simpa only [q, add_assoc] using hdriftFirst
  · simpa only [q, add_assoc] using hdriftSecond
  · simpa only [q, add_assoc] using hvarianceFirst
  · simpa only [q, add_assoc] using hvarianceSecond

/-- The paired event consisting of exactly the first `d` constraints of a
full logarithmic path of length `d+m`. -/
def harperPairedLogBallotPrefixSet
    (start d m : Nat) : Set (Fin d → Real × Real) :=
  harperPairedPartialSumBarrierSet
    (fun k ↦ harper1144LogBallotLowerBarrier start (d + m)
      (Fin.castAdd m k))
    (fun k ↦ harper1144LogBallotUpperBarrier (d + m)
      (Fin.castAdd m k))

theorem harperScheduledAutomaticLowerBarrier_castAdd
    (start d m : Nat) (k : Fin d) :
    harperScheduledAutomaticLowerBarrier start (d + m) (Fin.castAdd m k) =
      harperScheduledAutomaticLowerBarrier start d k := by
  unfold harperScheduledAutomaticLowerBarrier
    Problem520.harperCumulativeCellWidth
  have hmoderate :
      (∑ i ∈ Finset.Iic (Fin.castAdd m k),
          Problem520.harperScheduledModerateRadius start (d + m) i) =
        ∑ i ∈ Finset.Iic k,
          Problem520.harperScheduledModerateRadius start d i := by
    rw [← map_Iic_castAdd_general k, Finset.sum_map]
    rfl
  have hwidth :
      (∑ i ∈ Finset.Iic (Fin.castAdd m k),
          Problem520.harperScheduledRelativeCellWidth start (d + m) i) =
        ∑ i ∈ Finset.Iic k,
          Problem520.harperScheduledRelativeCellWidth start d i := by
    rw [← map_Iic_castAdd_general k, Finset.sum_map]
    rfl
  rw [hmoderate, hwidth]

theorem harper1144LogBallotLowerBarrier_castAdd
    (start d m : Nat) (k : Fin d) :
    harper1144LogBallotLowerBarrier start (d + m) (Fin.castAdd m k) =
      harper1144LogBallotLowerBarrier start d k := by
  unfold harper1144LogBallotLowerBarrier
  rw [harperScheduledAutomaticLowerBarrier_castAdd]
  rfl

theorem harper1144LogBallotUpperBarrier_castAdd
    (d m : Nat) (k : Fin d) :
    harper1144LogBallotUpperBarrier (d + m) (Fin.castAdd m k) =
      harper1144LogBallotUpperBarrier d k := by
  rfl

theorem harperPairedLogBallotPrefixSet_eq
    (start d m : Nat) :
    harperPairedLogBallotPrefixSet start d m =
      harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start d)
        (harper1144LogBallotUpperBarrier d) := by
  unfold harperPairedLogBallotPrefixSet
  congr 1
  · funext k
    exact harper1144LogBallotLowerBarrier_castAdd start d m k

theorem measurableSet_harperPairedLogBallotPrefixSet
    (start d m : Nat) :
    MeasurableSet (harperPairedLogBallotPrefixSet start d m) := by
  exact measurableSet_harperPairedPartialSumBarrierSet _ _

theorem harperTwoHeightCubeLaw_logBallotPrefixInter_eq_pi
    (y start d m : Nat) (t s : Real) :
    (harperTwoHeightCubeLaw y t s).real
        (harper1144LogBallotCubeEvent y start d t ∩
          harper1144LogBallotCubeEvent y start d s) =
      (Measure.pi (fun i : Fin d ↦
        harperTwoHeightBallotBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
        (harperPairedLogBallotPrefixSet start d m) := by
  have hproduct :=
    harperTwoHeightCubeLaw_real_preimage_scheduledBallotBlockVectors_eq_pi
      y start d t s
      (harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start d)
        (harper1144LogBallotUpperBarrier d))
      (measurableSet_harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start d)
        (harper1144LogBallotUpperBarrier d))
  rw [preimage_scheduledBallotBlockVectors_pairedLogBarrier_eq_inter] at hproduct
  rw [harperPairedLogBallotPrefixSet_eq]
  exact hproduct

theorem mem_harperPairedLogBallotPrefixSet_of_addCases_mem
    {start d m : Nat} (u : Fin d → Real × Real)
    (v : Fin m → Real × Real)
    (hfull : Fin.addCases u v ∈ harperPairedPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start (d + m))
      (harper1144LogBallotUpperBarrier (d + m))) :
    u ∈ harperPairedLogBallotPrefixSet start d m := by
  rcases hfull with ⟨hfirst, hsecond⟩
  change harperPairFirstPath (Fin.addCases u v) ∈
    Problem520.harperPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start (d + m))
      (harper1144LogBallotUpperBarrier (d + m)) at hfirst
  change harperPairSecondPath (Fin.addCases u v) ∈
    Problem520.harperPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start (d + m))
      (harper1144LogBallotUpperBarrier (d + m)) at hsecond
  rw [harperPairFirstPath_addCases,
    Problem520.mem_harperPartialSumBarrierSet] at hfirst
  rw [harperPairSecondPath_addCases,
    Problem520.mem_harperPartialSumBarrierSet] at hsecond
  change
    harperPairFirstPath u ∈ Problem520.harperPartialSumBarrierSet
        (fun k ↦ harper1144LogBallotLowerBarrier start (d + m)
          (Fin.castAdd m k))
        (fun k ↦ harper1144LogBallotUpperBarrier (d + m)
          (Fin.castAdd m k)) ∧
      harperPairSecondPath u ∈ Problem520.harperPartialSumBarrierSet
        (fun k ↦ harper1144LogBallotLowerBarrier start (d + m)
          (Fin.castAdd m k))
        (fun k ↦ harper1144LogBallotUpperBarrier (d + m)
          (Fin.castAdd m k))
  rw [Problem520.mem_harperPartialSumBarrierSet,
    Problem520.mem_harperPartialSumBarrierSet]
  constructor
  · intro k
    have hk := hfirst (Fin.castAdd m k)
    rw [harperPathPartialSum_addCases_castAdd] at hk
    exact hk
  · intro k
    have hk := hsecond (Fin.castAdd m k)
    rw [harperPathPartialSum_addCases_castAdd] at hk
    exact hk

/-- Product-factor form of the logarithmic suffix theorem: the full paired
mass is the prefix-event mass times the `O((d+1)^2/m)` continuation cost. -/
theorem harperScheduledTwoHeightLogBallotProduct_real_le_prefix_mul
    (y start d m : Nat) (t s : Real)
    (hd : 0 < d) (hm : 4 ≤ m)
    (hfrequency : ∀ i : Fin m,
      4 * ((2 * (d + m) : Nat) : Real) ^ (6 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + d + i.val) : Real))
    (hendpoint : ∀ i : Fin m,
      1048576 * ((2 * (d + m) : Nat) : Real) ^ (48 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + d + i.val) : Real))
    (hcovariance : ∀ i : Fin m,
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
          t s t s| ≤
        1 / ((2 * (d + m) : Nat) : Real) ^ (40 : Nat))
    (hdriftFirst : ∀ i : Fin m,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
          t s t t| ≤
        1 / ((2 * (d + m) : Nat) : Real) ^ (2 : Nat))
    (hdriftSecond : ∀ i : Fin m,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
          t s s s| ≤
        1 / ((2 * (d + m) : Nat) : Real) ^ (2 : Nat))
    (hvarianceFirst : ∀ i : Fin m,
      (1 / 3 : Real) <
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
            t s t t ∧
        harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
            t s t t < (3 / 8 : Real))
    (hvarianceSecond : ∀ i : Fin m,
      (1 / 3 : Real) <
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
            t s s s ∧
        harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
            t s s s < (3 / 8 : Real)) :
    (Measure.pi (fun i : Fin (d + m) ↦
      harperTwoHeightBallotBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
        (harperPairedPartialSumBarrierSet
          (harper1144LogBallotLowerBarrier start (d + m))
          (harper1144LogBallotUpperBarrier (d + m))) ≤
      (Measure.pi (fun i : Fin d ↦
        harperTwoHeightBallotBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
          (harperPairedLogBallotPrefixSet start d m) *
        (5000 * (64 * (d : Real) + 4) ^ (2 : Nat) * (m : Real)⁻¹) := by
  let M : Fin (d + m) → Measure (Real × Real) := fun i ↦
    harperTwoHeightBallotBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  apply pi_real_le_prefixEvent_mul_of_suffix_fiberwise M
    (harperPairedPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start (d + m))
      (harper1144LogBallotUpperBarrier (d + m)))
    (measurableSet_harperPairedPartialSumBarrierSet _ _)
    (harperPairedLogBallotPrefixSet start d m)
    (measurableSet_harperPairedLogBallotPrefixSet start d m)
    (5000 * (64 * (d : Real) + 4) ^ (2 : Nat) * (m : Real)⁻¹)
  · intro u v huv
    exact mem_harperPairedLogBallotPrefixSet_of_addCases_mem u v huv
  · intro u _hu
    by_cases hcont : ∃ v : Fin m → Real × Real,
        Fin.addCases u v ∈ harperPairedPartialSumBarrierSet
          (harper1144LogBallotLowerBarrier start (d + m))
          (harper1144LogBallotUpperBarrier (d + m))
    · obtain ⟨v, hv⟩ := hcont
      have hsubset :
          {w : Fin m → Real × Real | Fin.addCases u w ∈
            harperPairedPartialSumBarrierSet
              (harper1144LogBallotLowerBarrier start (d + m))
              (harper1144LogBallotUpperBarrier (d + m))} ⊆
            harperPairedPartialSumBarrierSet
              (harperPairedSuffixLower
                (harper1144LogBallotLowerBarrier start (d + m)) u)
              (harperPairedSuffixUpper
                (harper1144LogBallotUpperBarrier (d + m)) u) := by
        intro w hw
        exact mem_harperPairedSuffixBarrier_of_addCases_mem _ _ u w hw
      have hsuffix := harperScheduledTwoHeightLogBallotSuffix_real_le
        y start d m t s hd hm u v hv hfrequency hendpoint hcovariance
          hdriftFirst hdriftSecond hvarianceFirst hvarianceSecond
      exact (measureReal_mono hsubset (measure_ne_top _ _)).trans (by
        simpa only [M, Fin.val_natAdd, add_assoc] using hsuffix)
    · have hempty :
          {w : Fin m → Real × Real | Fin.addCases u w ∈
            harperPairedPartialSumBarrierSet
              (harper1144LogBallotLowerBarrier start (d + m))
              (harper1144LogBallotUpperBarrier (d + m))} = ∅ := by
        ext w
        constructor
        · intro hw
          exact False.elim (hcont ⟨w, hw⟩)
        · intro hw
          exact False.elim hw
      rw [hempty, measureReal_empty]
      positivity

/-- Single-scale rooted prefix-times-suffix cancellation.  This is useful
when the density pinch and the suffix decorrelation cutoff occur at the same
block.  The overlap-shell proof uses the two-scale refinement below. -/
theorem exists_harper1144LogBallot_rooted_prefix_suffix_le :
    ∃ B > 0, ∃ J : Nat,
      ∀ start d m y : Nat, J + 1 ≤ start → 0 < d → 4 ≤ m →
        Problem520.harperBlockEndpoint (start + (d + m)) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
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
                let P := Problem520.harperScheduledPrimeRangeFrom y start d
                harperTwoHeightCorrelation y t s *
                    (harperTwoHeightCubeLaw y t s).real
                      (harper1144LogBallotCubeEvent y start (d + m) t ∩
                        harper1144LogBallotCubeEvent y start (d + m) s) ≤
                  ((B * (2 : Real) ^ d / (d : Real) ^ (4 : Nat)) *
                    harperSubsetCorrelation y Pᶜ t s) *
                      (5000 * (64 * (d : Real) + 4) ^ (2 : Nat) *
                        (m : Real)⁻¹) := by
  obtain ⟨B, hB, J, hroot⟩ :=
    exists_harper1144LogBallot_correlation_probability_le_powTwo_div_fourth_compl
  refine ⟨B, hB, J, ?_⟩
  intro start d m y hstart hd hm hy t ht s hs
    hfrequency hendpoint hcovariance hdriftFirst hdriftSecond
    hvarianceFirst hvarianceSecond
  dsimp only
  let C : Real :=
    5000 * (64 * (d : Real) + 4) ^ (2 : Nat) * (m : Real)⁻¹
  let M : Real := B * (2 : Real) ^ d / (d : Real) ^ (4 : Nat)
  have hprefixY : Problem520.harperBlockEndpoint (start + d) ≤ y := by
    apply (Problem520.strictMono_harperBlockEndpoint.monotone ?_).trans hy
    omega
  let last : Fin d := ⟨d - 1, by omega⟩
  have hlastVal : last.val + 1 = d := by
    dsimp only [last]
    omega
  have hprefixRoot := hroot start d y hstart hprefixY t ht s hs last
  dsimp only at hprefixRoot
  rw [hlastVal] at hprefixRoot
  have hprefixProduct :=
    harperScheduledTwoHeightLogBallotProduct_real_le_prefix_mul
      y start d m t s hd hm hfrequency hendpoint hcovariance
        hdriftFirst hdriftSecond hvarianceFirst hvarianceSecond
  have hfullEq :=
    harperTwoHeightCubeLaw_real_preimage_scheduledBallotBlockVectors_eq_pi
      y start (d + m) t s
      (harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start (d + m))
        (harper1144LogBallotUpperBarrier (d + m)))
      (measurableSet_harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start (d + m))
        (harper1144LogBallotUpperBarrier (d + m)))
  rw [preimage_scheduledBallotBlockVectors_pairedLogBarrier_eq_inter] at hfullEq
  have hprefixEq :=
    harperTwoHeightCubeLaw_logBallotPrefixInter_eq_pi
      y start d m t s
  have hprob :
      (harperTwoHeightCubeLaw y t s).real
          (harper1144LogBallotCubeEvent y start (d + m) t ∩
            harper1144LogBallotCubeEvent y start (d + m) s) ≤
        (harperTwoHeightCubeLaw y t s).real
          (harper1144LogBallotCubeEvent y start d t ∩
            harper1144LogBallotCubeEvent y start d s) * C := by
    rw [hfullEq, hprefixEq]
    simpa only [C] using hprefixProduct
  have hcorrNonneg : 0 ≤ harperTwoHeightCorrelation y t s :=
    (harperTwoHeightCorrelation_pos y t s).le
  have hCnonneg : 0 ≤ C := by
    dsimp only [C]
    positivity
  calc
    harperTwoHeightCorrelation y t s *
        (harperTwoHeightCubeLaw y t s).real
          (harper1144LogBallotCubeEvent y start (d + m) t ∩
            harper1144LogBallotCubeEvent y start (d + m) s) ≤
      harperTwoHeightCorrelation y t s *
        ((harperTwoHeightCubeLaw y t s).real
          (harper1144LogBallotCubeEvent y start d t ∩
            harper1144LogBallotCubeEvent y start d s) * C) :=
        mul_le_mul_of_nonneg_left hprob hcorrNonneg
    _ = (harperTwoHeightCorrelation y t s *
        (harperTwoHeightCubeLaw y t s).real
          (harper1144LogBallotCubeEvent y start d t ∩
            harper1144LogBallotCubeEvent y start d s)) * C := by ring
    _ ≤ (M * harperSubsetCorrelation y
        (Problem520.harperScheduledPrimeRangeFrom y start d)ᶜ t s) * C :=
      mul_le_mul_of_nonneg_right (by simpa only [M] using hprefixRoot) hCnonneg
    _ = _ := by rfl

/-- Two-scale rooted prefix-times-suffix cancellation.  The rooted-density
cap is taken after only `r` common-history blocks, while the conditional
two-walk estimate starts after `d ≥ r` exposed blocks.  The intervening
`d-r` blocks are the oscillatory buffer in Harper's shell decomposition. -/
theorem exists_harper1144LogBallot_rooted_commonPrefix_suffix_le :
    ∃ B > 0, ∃ J : Nat,
      ∀ start r d m y : Nat, J + 1 ≤ start → 0 < r → r ≤ d → 4 ≤ m →
        Problem520.harperBlockEndpoint (start + (d + m)) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
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
                let P := Problem520.harperScheduledPrimeRangeFrom y start r
                harperTwoHeightCorrelation y t s *
                    (harperTwoHeightCubeLaw y t s).real
                      (harper1144LogBallotCubeEvent y start (d + m) t ∩
                        harper1144LogBallotCubeEvent y start (d + m) s) ≤
                  ((B * (2 : Real) ^ r / (r : Real) ^ (4 : Nat)) *
                    harperSubsetCorrelation y Pᶜ t s) *
                      (5000 * (64 * (d : Real) + 4) ^ (2 : Nat) *
                        (m : Real)⁻¹) := by
  obtain ⟨B, hB, J, hroot⟩ :=
    exists_harper1144LogBallot_correlation_probability_le_powTwo_div_fourth_compl
  refine ⟨B, hB, J, ?_⟩
  intro start r d m y hstart hr hrd hm hy t ht s hs
    hfrequency hendpoint hcovariance hdriftFirst hdriftSecond
    hvarianceFirst hvarianceSecond
  dsimp only
  let C : Real :=
    5000 * (64 * (d : Real) + 4) ^ (2 : Nat) * (m : Real)⁻¹
  let M : Real := B * (2 : Real) ^ r / (r : Real) ^ (4 : Nat)
  have hprefixY : Problem520.harperBlockEndpoint (start + d) ≤ y := by
    apply (Problem520.strictMono_harperBlockEndpoint.monotone ?_).trans hy
    omega
  let commonLast : Fin d := ⟨r - 1, by omega⟩
  have hcommonLastVal : commonLast.val + 1 = r := by
    dsimp only [commonLast]
    omega
  have hprefixRoot := hroot start d y hstart hprefixY t ht s hs commonLast
  dsimp only at hprefixRoot
  rw [hcommonLastVal] at hprefixRoot
  have hprefixProduct :=
    harperScheduledTwoHeightLogBallotProduct_real_le_prefix_mul
      y start d m t s (hr.trans_le hrd) hm hfrequency hendpoint hcovariance
        hdriftFirst hdriftSecond hvarianceFirst hvarianceSecond
  have hfullEq :=
    harperTwoHeightCubeLaw_real_preimage_scheduledBallotBlockVectors_eq_pi
      y start (d + m) t s
      (harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start (d + m))
        (harper1144LogBallotUpperBarrier (d + m)))
      (measurableSet_harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start (d + m))
        (harper1144LogBallotUpperBarrier (d + m)))
  rw [preimage_scheduledBallotBlockVectors_pairedLogBarrier_eq_inter] at hfullEq
  have hprefixEq :=
    harperTwoHeightCubeLaw_logBallotPrefixInter_eq_pi
      y start d m t s
  have hprob :
      (harperTwoHeightCubeLaw y t s).real
          (harper1144LogBallotCubeEvent y start (d + m) t ∩
            harper1144LogBallotCubeEvent y start (d + m) s) ≤
        (harperTwoHeightCubeLaw y t s).real
          (harper1144LogBallotCubeEvent y start d t ∩
            harper1144LogBallotCubeEvent y start d s) * C := by
    rw [hfullEq, hprefixEq]
    simpa only [C] using hprefixProduct
  have hcorrNonneg : 0 ≤ harperTwoHeightCorrelation y t s :=
    (harperTwoHeightCorrelation_pos y t s).le
  have hCnonneg : 0 ≤ C := by
    dsimp only [C]
    positivity
  calc
    harperTwoHeightCorrelation y t s *
        (harperTwoHeightCubeLaw y t s).real
          (harper1144LogBallotCubeEvent y start (d + m) t ∩
            harper1144LogBallotCubeEvent y start (d + m) s) ≤
      harperTwoHeightCorrelation y t s *
        ((harperTwoHeightCubeLaw y t s).real
          (harper1144LogBallotCubeEvent y start d t ∩
            harper1144LogBallotCubeEvent y start d s) * C) :=
        mul_le_mul_of_nonneg_left hprob hcorrNonneg
    _ = (harperTwoHeightCorrelation y t s *
        (harperTwoHeightCubeLaw y t s).real
          (harper1144LogBallotCubeEvent y start d t ∩
            harper1144LogBallotCubeEvent y start d s)) * C := by ring
    _ ≤ (M * harperSubsetCorrelation y
        (Problem520.harperScheduledPrimeRangeFrom y start r)ᶜ t s) * C :=
      mul_le_mul_of_nonneg_right (by simpa only [M] using hprefixRoot) hCnonneg
    _ = _ := by rfl

/-- Fubini-integrated form: the entire paired logarithmic ballot is bounded
by the same `O((d+1)^2/m)` suffix estimate. -/
theorem harperScheduledTwoHeightLogBallotProduct_real_le
    (y start d m : Nat) (t s : Real)
    (hd : 0 < d) (hm : 4 ≤ m)
    (hfrequency : ∀ i : Fin m,
      4 * ((2 * (d + m) : Nat) : Real) ^ (6 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + d + i.val) : Real))
    (hendpoint : ∀ i : Fin m,
      1048576 * ((2 * (d + m) : Nat) : Real) ^ (48 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + d + i.val) : Real))
    (hcovariance : ∀ i : Fin m,
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
          t s t s| ≤
        1 / ((2 * (d + m) : Nat) : Real) ^ (40 : Nat))
    (hdriftFirst : ∀ i : Fin m,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
          t s t t| ≤
        1 / ((2 * (d + m) : Nat) : Real) ^ (2 : Nat))
    (hdriftSecond : ∀ i : Fin m,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
          t s s s| ≤
        1 / ((2 * (d + m) : Nat) : Real) ^ (2 : Nat))
    (hvarianceFirst : ∀ i : Fin m,
      (1 / 3 : Real) <
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
            t s t t ∧
        harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
            t s t t < (3 / 8 : Real))
    (hvarianceSecond : ∀ i : Fin m,
      (1 / 3 : Real) <
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
            t s s s ∧
        harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
            t s s s < (3 / 8 : Real)) :
    (Measure.pi (fun i : Fin (d + m) ↦
      harperTwoHeightBallotBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s)).real
        (harperPairedPartialSumBarrierSet
          (harper1144LogBallotLowerBarrier start (d + m))
          (harper1144LogBallotUpperBarrier (d + m))) ≤
      5000 * (64 * (d : Real) + 4) ^ (2 : Nat) * (m : Real)⁻¹ := by
  let M : Fin (d + m) → Measure (Real × Real) := fun i ↦
    harperTwoHeightBallotBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  apply pi_real_le_of_suffix_fiberwise M
    (harperPairedPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start (d + m))
      (harper1144LogBallotUpperBarrier (d + m)))
    (measurableSet_harperPairedPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start (d + m))
      (harper1144LogBallotUpperBarrier (d + m)))
    (5000 * (64 * (d : Real) + 4) ^ (2 : Nat) * (m : Real)⁻¹)
  intro u
  by_cases hu : ∃ v : Fin m → Real × Real,
      Fin.addCases u v ∈ harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start (d + m))
        (harper1144LogBallotUpperBarrier (d + m))
  · obtain ⟨v, hv⟩ := hu
    have hsubset :
        {w : Fin m → Real × Real | Fin.addCases u w ∈
          harperPairedPartialSumBarrierSet
            (harper1144LogBallotLowerBarrier start (d + m))
            (harper1144LogBallotUpperBarrier (d + m))} ⊆
          harperPairedPartialSumBarrierSet
            (harperPairedSuffixLower
              (harper1144LogBallotLowerBarrier start (d + m)) u)
            (harperPairedSuffixUpper
              (harper1144LogBallotUpperBarrier (d + m)) u) := by
      intro w hw
      exact mem_harperPairedSuffixBarrier_of_addCases_mem _ _ u w hw
    have hsuffix := harperScheduledTwoHeightLogBallotSuffix_real_le
      y start d m t s hd hm u v hv hfrequency hendpoint hcovariance
        hdriftFirst hdriftSecond hvarianceFirst hvarianceSecond
    exact (measureReal_mono hsubset (measure_ne_top _ _)).trans (by
      simpa only [M, Fin.val_natAdd, add_assoc] using hsuffix)
  · have hempty :
        {w : Fin m → Real × Real | Fin.addCases u w ∈
          harperPairedPartialSumBarrierSet
            (harper1144LogBallotLowerBarrier start (d + m))
            (harper1144LogBallotUpperBarrier (d + m))} = ∅ := by
      ext w
      constructor
      · intro hw
        exact False.elim (hu ⟨w, hw⟩)
      · intro hw
        exact False.elim hw
    rw [hempty, measureReal_empty]
    positivity

/-- The preceding prefix/suffix estimate on the literal two-height tilted
cube event. -/
theorem harperTwoHeightLogBallotInter_split_le
    (y start d m : Nat) (t s : Real)
    (hd : 0 < d) (hm : 4 ≤ m)
    (hfrequency : ∀ i : Fin m,
      4 * ((2 * (d + m) : Nat) : Real) ^ (6 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + d + i.val) : Real))
    (hendpoint : ∀ i : Fin m,
      1048576 * ((2 * (d + m) : Nat) : Real) ^ (48 : Nat) ≤
        Real.sqrt
          (Problem520.harperBlockEndpoint (start + d + i.val) : Real))
    (hcovariance : ∀ i : Fin m,
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
          t s t s| ≤
        1 / ((2 * (d + m) : Nat) : Real) ^ (40 : Nat))
    (hdriftFirst : ∀ i : Fin m,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
          t s t t| ≤
        1 / ((2 * (d + m) : Nat) : Real) ^ (2 : Nat))
    (hdriftSecond : ∀ i : Fin m,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
          t s s s| ≤
        1 / ((2 * (d + m) : Nat) : Real) ^ (2 : Nat))
    (hvarianceFirst : ∀ i : Fin m,
      (1 / 3 : Real) <
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
            t s t t ∧
        harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
            t s t t < (3 / 8 : Real))
    (hvarianceSecond : ∀ i : Fin m,
      (1 / 3 : Real) <
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
            t s s s ∧
        harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y (start + d + i.val))
            t s s s < (3 / 8 : Real)) :
    (harperTwoHeightCubeLaw y t s).real
        (harper1144LogBallotCubeEvent y start (d + m) t ∩
          harper1144LogBallotCubeEvent y start (d + m) s) ≤
      5000 * (64 * (d : Real) + 4) ^ (2 : Nat) * (m : Real)⁻¹ := by
  have hproduct :=
    harperTwoHeightCubeLaw_real_preimage_scheduledBallotBlockVectors_eq_pi
      y start (d + m) t s
      (harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start (d + m))
        (harper1144LogBallotUpperBarrier (d + m)))
      (measurableSet_harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start (d + m))
        (harper1144LogBallotUpperBarrier (d + m)))
  rw [preimage_scheduledBallotBlockVectors_pairedLogBarrier_eq_inter] at hproduct
  rw [hproduct]
  exact harperScheduledTwoHeightLogBallotProduct_real_le
    y start d m t s hd hm hfrequency hendpoint hcovariance
      hdriftFirst hdriftSecond hvarianceFirst hvarianceSecond

/-- Exact Fubini handoff for a paired ballot.  It is enough to bound the
translated suffix corridor for every prefix which admits at least one full
continuation. -/
theorem pi_harperPairedBarrier_real_le_of_suffix
    {d m : Nat} (M : Fin (d + m) → Measure (Real × Real))
    [∀ i, IsProbabilityMeasure (M i)]
    (lower upper : Fin (d + m) → Real) (C : Real) (hC : 0 ≤ C)
    (hsuffix : ∀ u : Fin d → Real × Real,
      (∃ v : Fin m → Real × Real,
        Fin.addCases u v ∈ harperPairedPartialSumBarrierSet lower upper) →
      (Measure.pi (fun j : Fin m ↦ M (Fin.natAdd d j))).real
          (harperPairedPartialSumBarrierSet
            (harperPairedSuffixLower lower u)
            (harperPairedSuffixUpper upper u)) ≤ C) :
    (Measure.pi M).real (harperPairedPartialSumBarrierSet lower upper) ≤ C := by
  apply pi_real_le_of_suffix_fiberwise M
    (harperPairedPartialSumBarrierSet lower upper)
    (measurableSet_harperPairedPartialSumBarrierSet lower upper) C
  intro u
  by_cases hu : ∃ v : Fin m → Real × Real,
      Fin.addCases u v ∈ harperPairedPartialSumBarrierSet lower upper
  · have hsubset :
        {v : Fin m → Real × Real |
          Fin.addCases u v ∈ harperPairedPartialSumBarrierSet lower upper} ⊆
          harperPairedPartialSumBarrierSet
            (harperPairedSuffixLower lower u)
            (harperPairedSuffixUpper upper u) := by
      intro v hv
      exact mem_harperPairedSuffixBarrier_of_addCases_mem
        lower upper u v hv
    exact (measureReal_mono hsubset (measure_ne_top _ _)).trans
      (hsuffix u hu)
  · have hempty :
        {v : Fin m → Real × Real |
          Fin.addCases u v ∈ harperPairedPartialSumBarrierSet lower upper} =
          ∅ := by
      ext v
      constructor
      · intro hv
        exact False.elim (hu ⟨v, hv⟩)
      · intro hv
        exact False.elim hv
    rw [hempty, measureReal_empty]
    exact hC

end
end Problem1144
end Erdos

#print axioms Erdos.Problem1144.harperPathPartialSum_addCases_natAdd
#print axioms Erdos.Problem1144.mem_harperPairedSuffixBarrier_of_addCases_mem
#print axioms Erdos.Problem1144.measurePreserving_harperPairFinSplit
#print axioms Erdos.Problem1144.pi_harperPairedBarrier_real_le_of_suffix
#print axioms Erdos.Problem1144.pi_real_le_prefixEvent_mul_of_bufferSuffix_fiberwise
#print axioms Erdos.Problem1144.neg_sixtyFour_mul_suffixElapsed_sub_one_le_harperPairedSuffixLower_logBallot
#print axioms Erdos.Problem1144.harperScheduledTwoHeightScaledArbitraryBarrier_real_le
#print axioms Erdos.Problem1144.harperScheduledTwoHeightLogBallotProduct_real_le
#print axioms Erdos.Problem1144.harperScheduledTwoHeightLogBallotProduct_real_le_prefix_mul
#print axioms Erdos.Problem1144.harperTwoHeightLogBallotInter_split_le
#print axioms Erdos.Problem1144.exists_harper1144LogBallot_rooted_prefix_suffix_le
#print axioms Erdos.Problem1144.exists_harper1144LogBallot_rooted_commonPrefix_suffix_le
