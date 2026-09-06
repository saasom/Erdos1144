import Erdos.Problem1144.HarperCandidateGaussianFresh
import Erdos.Problem1144.HarperCandidateLogScreen

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos.Problem1144

/-- The subset of a finite fresh family selected by a Boolean flip pattern. -/
def candidateFreshFlipSet {n : ℕ} (q : Fin n → ℕ) (b : Fin n → Bool) : Finset ℕ :=
  (Finset.univ.filter fun p => b p = true).image q

theorem candidateFreshFlipSet_subset {n : ℕ} (q : Fin n → ℕ) (b : Fin n → Bool) :
    candidateFreshFlipSet q b ⊆ Finset.univ.image q := by
  exact Finset.image_subset_image (Finset.filter_subset _ _)

private theorem candidateFreshFlipSet_mem {n : ℕ} (q : Fin n → ℕ)
    (hq : Function.Injective q) (b : Fin n → Bool) (p : Fin n) :
    q p ∈ candidateFreshFlipSet q b ↔ b p = true := by
  simp only [candidateFreshFlipSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨j, hj, hp⟩
    simpa only [hq hp] using hj
  · intro hp
    exact ⟨p, hp, rfl⟩

private theorem candidate_flipSign_coin_map (s : Bool) :
    coin.map (fun b : Bool => if b then -boolSign s else boolSign s) =
      candidateRademacherLaw := by
  ext E hE
  rw [Measure.map_apply (measurable_of_finite _) hE]
  cases s <;> by_cases hp : (1 : ℝ) ∈ E <;> by_cases hn : (-1 : ℝ) ∈ E <;>
    simp [coin, boolSign, candidateRademacherLaw, Set.indicator, Set.preimage,
      hp, hn, add_comm]

/-- Flipping a fair finite Boolean cube gives exactly independent fair real
signs at the fresh coordinates, for every frozen complementary world. -/
theorem candidate_freshFlip_eps_law {n : ℕ} (q : Fin n → ℕ)
    (hq : Function.Injective q) (omega : Omega) :
    (Measure.pi (fun _ : Fin n => coin)).map
        (fun b p => eps (freshSignFlip (candidateFreshFlipSet q b) omega) (q p)) =
      Measure.pi (fun _ : Fin n => candidateRademacherLaw) := by
  have he : (fun (b : Fin n → Bool) p =>
      eps (freshSignFlip (candidateFreshFlipSet q b) omega) (q p)) =
      (fun b p => if b p then -boolSign (omega (q p)) else boolSign (omega (q p))) := by
    funext b p
    by_cases hb : b p = true
    · rw [eps_freshSignFlip_of_mem _ _ ((candidateFreshFlipSet_mem q hq b p).mpr hb)]
      simp [hb, eps_eq_boolSign]
    · rw [eps_freshSignFlip_of_notMem _ _ (fun hp => hb
        ((candidateFreshFlipSet_mem q hq b p).mp hp))]
      simp [hb, eps_eq_boolSign]
  rw [he, Measure.pi_map_pi (μ := fun _ : Fin n => coin) (f := fun (p : Fin n) (b : Bool) =>
    if b then -boolSign (omega (q p)) else boolSign (omega (q p)))
    (fun _ => (measurable_of_finite _).aemeasurable)]
  congr 1
  funext p
  exact candidate_flipSign_coin_map (omega (q p))

/-- The finite sign law identifies each selected crossing fiber with its
literal fresh-flip event. Selectors and coefficients may depend arbitrarily
on the frozen world, provided fresh flips leave them unchanged. -/
theorem candidate_selected_freshFlip_fiber_eq {n m : ℕ}
    (q : Fin n → ℕ) (hq : Function.Injective q)
    (a : Omega → Fin n → Fin m → ℝ) (J : Omega → Finset (Fin m))
    (ha : ∀ omega b, a (freshSignFlip (candidateFreshFlipSet q b) omega) = a omega)
    (hJ : ∀ omega b, J (freshSignFlip (candidateFreshFlipSet q b) omega) = J omega)
    (omega : Omega) (K : ℝ) :
    (Measure.pi (fun _ : Fin n => candidateRademacherLaw)).real
        {v | ∃ i ∈ J omega, K < |∑ p, a omega p i * v p|} =
      (Measure.pi (fun _ : Fin n => coin)).real
        {b | ∃ i ∈ J (freshSignFlip (candidateFreshFlipSet q b) omega),
          K < |∑ p, a (freshSignFlip (candidateFreshFlipSet q b) omega) p i *
            eps (freshSignFlip (candidateFreshFlipSet q b) omega) (q p)|} := by
  have hE : MeasurableSet {v : Fin n → ℝ |
      ∃ i ∈ J omega, K < |∑ p, a omega p i * v p|} := by
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    by_cases hi : i ∈ J omega
    · simp only [hi, true_and]
      exact measurableSet_lt measurable_const
        (Finset.measurable_sum _ fun p _ => measurable_const.mul (measurable_pi_apply p)).abs
    · simp [hi]
  rw [← candidate_freshFlip_eps_law q hq omega, measureReal_def,
    Measure.map_apply (measurable_of_finite _) hE]
  simp only [ha, hJ, measureReal_def, Set.preimage_setOf_eq]

/-- Averaging fair finite fresh-flip fibers recovers the original event
probability under every law preserved by those flips. -/
theorem candidate_freshFlip_fiber_average {n : ℕ}
    (q : Fin n → ℕ) (P : Measure Omega) [IsProbabilityMeasure P]
    (hP : ∀ b, MeasurePreserving (freshSignFlip (candidateFreshFlipSet q b)) P P)
    {E : Set Omega} (hE : MeasurableSet E) :
    (∫ omega, (Measure.pi (fun _ : Fin n => coin)).real
      {b | freshSignFlip (candidateFreshFlipSet q b) omega ∈ E} ∂P) = P.real E := by
  classical
  let B := Measure.pi (fun _ : Fin n => coin)
  have hpoint (omega : Omega) : B.real
      {b | freshSignFlip (candidateFreshFlipSet q b) omega ∈ E} =
      ∑ b : Fin n → Bool, B.real {b} *
        (freshSignFlip (candidateFreshFlipSet q b) ⁻¹' E).indicator
          (fun _ => (1 : ℝ)) omega := by
    let D : Set (Fin n → Bool) :=
      {b | freshSignFlip (candidateFreshFlipSet q b) omega ∈ E}
    have hD : MeasurableSet D := Set.toFinite D |>.measurableSet
    rw [← integral_indicator_one (μ := B) hD]
    change (∫ b, D.indicator (fun _ => (1 : ℝ)) b ∂B) = _
    rw [integral_fintype ((integrable_const (1 : ℝ)).indicator hD)]
    apply Finset.sum_congr rfl
    intro b _
    simp only [smul_eq_mul, D, Set.indicator, Set.mem_preimage, Set.mem_setOf_eq]
  change (∫ omega, B.real {b | freshSignFlip (candidateFreshFlipSet q b) omega ∈ E} ∂P) = _
  simp_rw [hpoint]
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul]
    have hterm (b : Fin n → Bool) :
        (∫ omega, (freshSignFlip (candidateFreshFlipSet q b) ⁻¹' E).indicator
          (fun _ => (1 : ℝ)) omega ∂P) = P.real E := by
      calc
        _ = P.real (freshSignFlip (candidateFreshFlipSet q b) ⁻¹' E) := by
          simpa using integral_indicator_one (μ := P) (hE.preimage (hP b).measurable)
        _ = P.real E := (hP b).measureReal_preimage hE.nullMeasurableSet
    simp_rw [hterm]
    rw [← Finset.sum_mul]
    simp [B]
  · intro b _
    exact ((integrable_const (1 : ℝ)).indicator
      (hE.preimage (hP b).measurable)).const_mul _

/-- The averaged conditional sign law for an arbitrary old-world selector.
The hypotheses state literal invariance of the data, not a probability
comparison. -/
theorem candidate_selected_fresh_sign_fiber_average {n m : ℕ}
    (q : Fin n → ℕ) (hq : Function.Injective q)
    (a : Omega → Fin n → Fin m → ℝ) (J : Omega → Finset (Fin m))
    (ha : ∀ omega b, a (freshSignFlip (candidateFreshFlipSet q b) omega) = a omega)
    (hJ : ∀ omega b, J (freshSignFlip (candidateFreshFlipSet q b) omega) = J omega)
    (P : Measure Omega) [IsProbabilityMeasure P]
    (hP : ∀ b, MeasurePreserving (freshSignFlip (candidateFreshFlipSet q b)) P P)
    (K : ℝ) (hE : MeasurableSet {omega | ∃ i ∈ J omega,
      K < |∑ p, a omega p i * eps omega (q p)|}) :
    (∫ omega, (Measure.pi (fun _ : Fin n => candidateRademacherLaw)).real
      {v | ∃ i ∈ J omega, K < |∑ p, a omega p i * v p|} ∂P) =
      P.real {omega | ∃ i ∈ J omega, K < |∑ p, a omega p i * eps omega (q p)|} := by
  simp_rw [candidate_selected_freshFlip_fiber_eq q hq a J ha hJ]
  exact candidate_freshFlip_fiber_average q P hP hE

/-- A fixed old assignment preserves every finite fresh flip used by the
preceding exact conditional-fiber identities. -/
theorem candidateCylinderLaw_freshFlipSet {n : ℕ}
    (s : Finset ℕ) (eta : s → Bool) (q : Fin n → ℕ)
    (hq : ∀ p, q p ∉ s) (b : Fin n → Bool) :
    MeasurePreserving (freshSignFlip (candidateFreshFlipSet q b))
      (candidateCylinderLaw s eta) (candidateCylinderLaw s eta) := by
  apply candidateCylinderLaw_freshSignFlip
  apply Finset.disjoint_left.mpr
  intro p hp ht
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (candidateFreshFlipSet_subset q b ht)
  exact hq j hp

/-- In the candidate range every literal fresh coefficient is unchanged by
the complete finite fresh cube. -/
theorem candidate_log_fresh_coefficient_freshFlipSet {n m : ℕ}
    (q : Fin n → ℕ) (u : Fin m → ℝ) (X : ℕ)
    (hq : ∀ p, X < q p) (hu : ∀ i, ⌊Real.exp (u i)⌋₊ < X ^ 2)
    (omega : Omega) (b : Fin n → Bool) (p : Fin n) (i : Fin m) :
    S (freshSignFlip (candidateFreshFlipSet q b) omega) (⌊Real.exp (u i)⌋₊ / q p) /
        Real.exp (u i / 2) =
      S omega (⌊Real.exp (u i)⌋₊ / q p) / Real.exp (u i / 2) := by
  have hsmall : ⌊Real.exp (u i)⌋₊ / q p < X :=
    quotient_lt_X_of_le_div_large (hu i) (hq p) le_rfl
  have hsmooth : ∀ k ∈ Finset.Icc 1 (⌊Real.exp (u i)⌋₊ / q p), IsXSmooth X k :=
    fun k hk => isXSmooth_of_lt ((Finset.mem_Icc.mp hk).2.trans_lt hsmall)
  rw [← smoothSum_eq_S_of_forall_smooth _ hsmooth,
    ← smoothSum_eq_S_of_forall_smooth omega hsmooth]
  rw [smoothSum_freshSignFlip_eq_of_above]
  intro r hr
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (candidateFreshFlipSet_subset q b hr)
  exact hq j

/-- The actual old-field retained selector is constant on the finite fresh
cube, including its fallback to the full grid when the density test fails. -/
theorem candidate_log_retained_freshFlipSet {n m : ℕ}
    (q : Fin n → ℕ) (u : Fin m → ℝ) (X : ℕ)
    (hq : ∀ p, X < q p) (b ρ : ℝ) (omega : Omega) (v : Fin n → Bool) :
    candidateRetainedIndices (fun omega i => harperCandidateLogOld omega X (u i)) b ρ
        (freshSignFlip (candidateFreshFlipSet q v) omega) =
      candidateRetainedIndices (fun omega i => harperCandidateLogOld omega X (u i))
        b ρ omega := by
  apply candidateRetainedIndices_invariant
  intro omega i
  unfold harperCandidateLogOld
  rw [smoothProcess_freshSignFlip_eq_of_above]
  intro r hr
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (candidateFreshFlipSet_subset q v hr)
  exact hq j

end Erdos.Problem1144
