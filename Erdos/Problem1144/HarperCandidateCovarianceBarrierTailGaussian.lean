import Erdos.Problem1144.HarperGaussianFenceTail

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

noncomputable section

/-!
# The terminal interval factor in strong-barrier deletion

Two independent ballot bounds alone give an inverse-length bound.  Harper's
strong-barrier deletion needs the additional inverse-square-root factor
obtained by leaving a middle Gaussian block unconstrained and locating its
sum in the terminal interval.  The lemmas below use the actual finite
Gaussian laws, their proved sum law, and the proved Gaussian density bound.
-/

/-- A Gaussian block sum falls in any interval of length `r` with probability
at most `r / sqrt(total variance)`. -/
theorem candidate_gaussianBlock_interval_probability_le
    (n : ℕ) (v : Fin n → ℝ≥0) (hv : (∑ i, v i) ≠ 0)
    (a r : ℝ) (hr : 0 ≤ r) :
    (Measure.pi (fun i : Fin n => gaussianReal 0 (v i))).real
      {z | ∑ i, z i ∈ Set.Icc a (a + r)} ≤
        r / Real.sqrt ((∑ i, v i : ℝ≥0) : ℝ) := by
  have hsum : Measurable (fun z : Fin n → ℝ => ∑ i, z i) := by fun_prop
  have hmap := map_pi_gaussianReal_sum_eq n v
  rw [List.sum_ofFn] at hmap
  have hreal := map_measureReal_apply
    (μ := Measure.pi (fun i : Fin n => gaussianReal 0 (v i))) hsum
    (measurableSet_Icc (a := a) (b := a + r))
  rw [hmap] at hreal
  change (Measure.pi (fun i : Fin n => gaussianReal 0 (v i))).real
    ((fun z : Fin n → ℝ => ∑ i, z i) ⁻¹' Set.Icc a (a + r)) ≤ _
  rw [← hreal]
  simpa only [add_sub_cancel_left] using
    Problem520.gaussianReal_real_Icc_le_inv_sqrt 0 hv
      (show a ≤ a + r by linarith)

/-- Conditioning on the outer variables gives the exact middle-block
interval cost, uniformly over their measurable contribution to the sum. -/
theorem candidate_gaussianMiddle_interval_probability_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set Ω) (hA : MeasurableSet A) (g : Ω → ℝ) (hg : Measurable g)
    (n : ℕ) (v : Fin n → ℝ≥0) (hv : (∑ i, v i) ≠ 0)
    (x r : ℝ) (hr : 0 ≤ r) :
    (μ.prod (Measure.pi (fun i : Fin n => gaussianReal 0 (v i)))).real
      {z | z.1 ∈ A ∧ x - r ≤ g z.1 + ∑ i, z.2 i ∧
        g z.1 + ∑ i, z.2 i ≤ x} ≤
      μ.real A * (r / Real.sqrt ((∑ i, v i : ℝ≥0) : ℝ)) := by
  let ν : Measure (Fin n → ℝ) := Measure.pi fun i => gaussianReal 0 (v i)
  let E : Set (Ω × (Fin n → ℝ)) :=
    {z | z.1 ∈ A ∧ x - r ≤ g z.1 + ∑ i, z.2 i ∧ g z.1 + ∑ i, z.2 i ≤ x}
  let F : Ω × (Fin n → ℝ) → ℝ := E.indicator 1
  let q : ℝ := r / Real.sqrt ((∑ i, v i : ℝ≥0) : ℝ)
  have hq : 0 ≤ q := div_nonneg hr (Real.sqrt_nonneg _)
  have hE : MeasurableSet E := by
    exact (hA.preimage measurable_fst).inter
      ((measurableSet_le measurable_const
        ((hg.comp measurable_fst).add (by fun_prop))).inter
          (measurableSet_le ((hg.comp measurable_fst).add (by fun_prop)) measurable_const))
  have hF : Integrable F (μ.prod ν) := (integrable_const 1).indicator hE
  have hinner (ω : Ω) : (∫ z, F (ω, z) ∂ν) ≤ A.indicator (fun _ => q) ω := by
    by_cases hω : ω ∈ A
    · have hfun : (fun z => F (ω, z)) =
          {z : Fin n → ℝ | ∑ i, z i ∈ Set.Icc (x - r - g ω) (x - g ω)}.indicator 1 := by
        funext z
        simp only [F, E, Set.indicator, Set.mem_setOf_eq, hω, true_and,
          Set.mem_Icc, Pi.one_apply]
        congr 1
        apply propext
        constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
      rw [hfun, integral_indicator_one (by measurability), Set.indicator_of_mem hω]
      have h := candidate_gaussianBlock_interval_probability_le n v hv
        (x - r - g ω) r hr
      simpa only [show x - r - g ω + r = x - g ω by ring] using h
    · have hfun : (fun z => F (ω, z)) = 0 := by
        funext z
        simp [F, E, hω]
      simp only [hfun, integral_zero', Set.indicator_of_notMem hω]
      exact le_rfl
  calc
    _ = ∫ z, F z ∂μ.prod ν := (integral_indicator_one hE).symm
    _ = ∫ ω, ∫ z, F (ω, z) ∂ν ∂μ := integral_prod F hF
    _ ≤ ∫ ω, A.indicator (fun _ => q) ω ∂μ :=
      integral_mono hF.integral_prod_left ((integrable_const q).indicator hA) hinner
    _ = μ.real A * q := by
      rw [integral_indicator hA]
      simp only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]

/-- The product event retained by the three-block argument: the first and
reversed last blocks survive, and the sum of all three blocks lies in the
terminal interval.  The middle block has no path constraints. -/
def candidateGaussianThreeBlockTerminalEvent (m n k : ℕ) (x r : ℝ) :
    Set (((Fin m → ℝ) × (Fin k → ℝ)) × (Fin n → ℝ)) :=
  {z | Problem520.gaussianWalkSurvives m x z.1.1 ∧
    Problem520.gaussianWalkSurvives k r (harperReverseNegate z.1.2) ∧
    x - r ≤ (∑ i, z.1.1 i) + (∑ i, z.1.2 i) + ∑ i, z.2 i ∧
    (∑ i, z.1.1 i) + (∑ i, z.1.2 i) + ∑ i, z.2 i ≤ x}

/-- Two ballot costs and the independent middle-block density cost.
When the three block lengths are comparable this is the required
`O((x+2)(r+2)r / n^(3/2))` terminal-near estimate. -/
theorem candidate_gaussianThreeBlock_terminal_probability_le
    (m n k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (v₁ : Fin m → ℝ≥0) (v₂ : Fin n → ℝ≥0) (v₃ : Fin k → ℝ≥0)
    (hv₂ : (∑ i, v₂ i) ≠ 0) (x r : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hlo₁ : ∀ i, (1 / 4 : ℝ≥0) ≤ v₁ i) (hhi₁ : ∀ i, v₁ i ≤ (1 / 2 : ℝ≥0))
    (hlo₃ : ∀ i, (1 / 4 : ℝ≥0) ≤ v₃ i) (hhi₃ : ∀ i, v₃ i ≤ (1 / 2 : ℝ≥0)) :
    (((Measure.pi (fun i : Fin m => gaussianReal 0 (v₁ i))).prod
      (Measure.pi (fun i : Fin k => gaussianReal 0 (v₃ i)))).prod
        (Measure.pi (fun i : Fin n => gaussianReal 0 (v₂ i)))).real
      (candidateGaussianThreeBlockTerminalEvent m n k x r) ≤
      (64 * (x + 2) / Real.sqrt (m : ℝ)) *
        (64 * (r + 2) / Real.sqrt (k : ℝ)) *
          (r / Real.sqrt ((∑ i, v₂ i : ℝ≥0) : ℝ)) := by
  let P₁ := Measure.pi (fun i : Fin m => gaussianReal 0 (v₁ i))
  let P₃ := Measure.pi (fun i : Fin k => gaussianReal 0 (v₃ i))
  let A₁ := Problem520.gaussianWalkSurvivalSet m x
  let A₃ := harperReverseNegate ⁻¹' Problem520.gaussianWalkSurvivalSet k r
  have hrev := measurePreserving_harperReverseNegate k v₃
  have hA₁ : MeasurableSet A₁ := Problem520.measurableSet_gaussianWalkSurvivalSet m hx
  have hA₃ : MeasurableSet A₃ :=
    (Problem520.measurableSet_gaussianWalkSurvivalSet k hr).preimage hrev.measurable
  have houter : (P₁.prod P₃).real (A₁ ×ˢ A₃) ≤
      (64 * (x + 2) / Real.sqrt (m : ℝ)) *
        (64 * (r + 2) / Real.sqrt (k : ℝ)) := by
    rw [measureReal_prod_prod]
    have hfirst := Problem520.gaussianVarianceWalk_quarter_half_probability_le_fin
      m hm v₁ hx hlo₁ hhi₁
    have hlast : P₃.real A₃ ≤ 64 * (r + 2) / Real.sqrt (k : ℝ) := by
      have hmap := map_measureReal_apply (μ := P₃) hrev.measurable
        (Problem520.measurableSet_gaussianWalkSurvivalSet k hr)
      rw [hrev.map_eq] at hmap
      change _ ≤ _
      rw [← hmap]
      exact Problem520.gaussianVarianceWalk_quarter_half_probability_le_fin
        k hk (fun i => v₃ i.rev) hr (fun i => hlo₃ i.rev) (fun i => hhi₃ i.rev)
    exact mul_le_mul hfirst hlast (by positivity) (by positivity)
  have hmiddle := candidate_gaussianMiddle_interval_probability_le (P₁.prod P₃)
    (A₁ ×ˢ A₃) (hA₁.prod hA₃)
    (fun z => (∑ i, z.1 i) + ∑ i, z.2 i) (by fun_prop) n v₂ hv₂ x r hr
  have hE : {z : ((Fin m → ℝ) × (Fin k → ℝ)) × (Fin n → ℝ) |
      z.1 ∈ A₁ ×ˢ A₃ ∧ x - r ≤ (∑ i, z.1.1 i) + (∑ i, z.1.2 i) + ∑ i, z.2 i ∧
        (∑ i, z.1.1 i) + (∑ i, z.1.2 i) + ∑ i, z.2 i ≤ x} =
        candidateGaussianThreeBlockTerminalEvent m n k x r := by
    ext z
    simp only [A₁, A₃, Problem520.gaussianWalkSurvivalSet,
      candidateGaussianThreeBlockTerminalEvent, Set.mem_setOf_eq,
      Set.mem_prod, Set.mem_preimage]
    tauto
  rw [hE] at hmiddle
  exact hmiddle.trans (mul_le_mul_of_nonneg_right houter
    (div_nonneg hr (Real.sqrt_nonneg _)))

private theorem survives_split_fst {m n : ℕ} (x : ℝ)
    (ω : Fin (m + n) → ℝ) (h : Problem520.gaussianWalkSurvives (m + n) x ω) :
    Problem520.gaussianWalkSurvives m x (harperFinSplit ω).1 := by
  apply (gaussianWalkSurvives_iff_harperPathPartialSum_le m x _).2
  intro k
  have hmap : (Finset.Iic k).map (Fin.castAddEmb n) = Finset.Iic (Fin.castAdd n k) := by
    ext i
    simp only [Finset.mem_map, Finset.mem_Iic, Fin.castAddEmb_apply]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact_mod_cast hj
    · intro hi
      have hiv : i.val < m := lt_of_le_of_lt (by exact_mod_cast hi) k.isLt
      exact ⟨⟨i.val, hiv⟩, by exact_mod_cast hi, Fin.ext rfl⟩
  have hfull := (gaussianWalkSurvives_iff_harperPathPartialSum_le (m + n) x ω).1 h
    (Fin.castAdd n k)
  unfold Problem520.harperPathPartialSum at hfull ⊢
  rw [← hmap, Finset.sum_map] at hfull
  exact hfull

private theorem survives_reverse_of_terminal_near {n : ℕ}
    (x r : ℝ) (hx : 0 ≤ x) (ω : Fin n → ℝ)
    (h : Problem520.gaussianWalkSurvives n x ω)
    (ht : Problem520.gaussianWalkTerminalDistance n x ω ≤ r) :
    Problem520.gaussianWalkSurvives n r (harperReverseNegate ω) := by
  have hbefore (j : Fin n) : (∑ i ∈ Finset.Iio j, ω i) ≤ x := by
    by_cases hj : j.val = 0
    · have hempty : Finset.Iio j = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hij := Finset.mem_Iio.mp hi
        have := Fin.lt_iff_val_lt_val.mp hij
        omega
      simpa only [hempty, Finset.sum_empty] using hx
    · let q : Fin n := ⟨j.val - 1, by omega⟩
      have heq : Finset.Iio j = Finset.Iic q := by
        ext i
        simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_iff_val_lt_val,
          Fin.le_iff_val_le_val, q]
        omega
      rw [heq]
      exact (gaussianWalkSurvives_iff_harperPathPartialSum_le n x ω).1 h q
  apply (gaussianWalkSurvives_iff_harperPathPartialSum_le n r _).2
  intro k
  rw [harperPathPartialSum_reverseNegate]
  have hdisj : Disjoint (Finset.Iio k.rev) (Finset.Ici k.rev) := by
    simp only [Finset.disjoint_left, Finset.mem_Iio, Finset.mem_Ici]
    exact fun i hi hki => (not_le_of_gt hi) hki
  have hunion : Finset.Iio k.rev ∪ Finset.Ici k.rev = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_Iio, Finset.mem_Ici, Finset.mem_univ, iff_true]
    exact lt_or_ge i k.rev
  have hsum : (∑ i, ω i) =
      (∑ i ∈ Finset.Iio k.rev, ω i) + ∑ i ∈ Finset.Ici k.rev, ω i := by
    rw [← Finset.sum_union hdisj, hunion]
  unfold Problem520.gaussianWalkTerminalDistance at ht
  rw [hsum] at ht
  linarith [hbefore k.rev]

private theorem measurable_threeBlockTerminalEvent (m n k : ℕ)
    (x r : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r) :
    MeasurableSet (candidateGaussianThreeBlockTerminalEvent m n k x r) := by
  have hrev : Measurable (harperReverseNegate (n := k)) := by
    unfold harperReverseNegate
    fun_prop
  unfold candidateGaussianThreeBlockTerminalEvent
  simp only [Set.setOf_and]
  exact ((Problem520.measurableSet_gaussianWalkSurvivalSet m hx).preimage
    (by fun_prop)).inter
      (((Problem520.measurableSet_gaussianWalkSurvivalSet k hr).preimage
        (hrev.comp (by fun_prop))).inter
          ((measurableSet_le measurable_const (by fun_prop)).inter
            (measurableSet_le (by fun_prop) measurable_const)))

/-- The sharp terminal-near bound for the full Gaussian walk, split into
three consecutive blocks.  The middle variance is left exact. -/
theorem candidate_gaussianWalkTerminalNear_probability_le_three_blocks
    (m n k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (v : Fin (m + (n + k)) → ℝ≥0)
    (hv : (∑ i : Fin n, v (Fin.natAdd m (Fin.castAdd k i))) ≠ 0)
    (x r : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hlo : ∀ i, (1 / 4 : ℝ≥0) ≤ v i) (hhi : ∀ i, v i ≤ (1 / 2 : ℝ≥0)) :
    (Measure.pi (fun i : Fin (m + (n + k)) => gaussianReal 0 (v i))).real
      (gaussianWalkTerminalNearSet (m + (n + k)) x r) ≤
      (64 * (x + 2) / Real.sqrt (m : ℝ)) *
        (64 * (r + 2) / Real.sqrt (k : ℝ)) *
          (r / Real.sqrt ((∑ i : Fin n, v (Fin.natAdd m (Fin.castAdd k i)) : ℝ≥0) : ℝ)) := by
  let v₁ : Fin m → ℝ≥0 := fun i => v (Fin.castAdd (n + k) i)
  let vs : Fin (n + k) → ℝ≥0 := fun i => v (Fin.natAdd m i)
  let v₂ : Fin n → ℝ≥0 := fun i => vs (Fin.castAdd k i)
  let v₃ : Fin k → ℝ≥0 := fun i => vs (Fin.natAdd n i)
  let P₁ := Measure.pi fun i : Fin m => gaussianReal 0 (v₁ i)
  let Ps := Measure.pi fun i : Fin (n + k) => gaussianReal 0 (vs i)
  let P₂ := Measure.pi fun i : Fin n => gaussianReal 0 (v₂ i)
  let P₃ := Measure.pi fun i : Fin k => gaussianReal 0 (v₃ i)
  let T : (Fin (m + (n + k)) → ℝ) →
      ((Fin m → ℝ) × (Fin k → ℝ)) × (Fin n → ℝ) := fun ω =>
    (((harperFinSplit ω).1, (harperFinSplit (harperFinSplit ω).2).2),
      (harperFinSplit (harperFinSplit ω).2).1)
  have hsplit := measurePreserving_harperFinSplit m (n + k) v
  have hsecond := (MeasurePreserving.id P₁).prod (measurePreserving_harperFinSplit n k vs)
  have hswap := (MeasurePreserving.id P₁).prod (Measure.measurePreserving_swap (μ := P₂) (ν := P₃))
  have hassoc := (measurePreserving_prodAssoc P₁ P₃ P₂).symm MeasurableEquiv.prodAssoc
  have hT : MeasurePreserving T
      (Measure.pi fun i : Fin (m + (n + k)) => gaussianReal 0 (v i))
      ((P₁.prod P₃).prod P₂) := by
    exact hassoc.comp (hswap.comp (hsecond.comp hsplit))
  have hsubset : gaussianWalkTerminalNearSet (m + (n + k)) x r ⊆
      T ⁻¹' candidateGaussianThreeBlockTerminalEvent m n k x r := by
    intro ω hω
    obtain ⟨hs, ht⟩ := hω
    change Problem520.gaussianWalkTerminalDistance (m + (n + k)) x ω ≤ r at ht
    let u := (harperFinSplit ω).1
    let z := (harperFinSplit ω).2
    let b := (harperFinSplit z).1
    let w := (harperFinSplit z).2
    have hu := survives_split_fst x ω hs
    have hz := gaussianWalkSurvives_snd_of_harperFinSplit x ω hs
    have hx₁ : 0 ≤ x - ∑ i, u i :=
      Problem520.gaussianWalkTerminalDistance_nonneg_of_survives m x u hx hu
    have hb := survives_split_fst (x - ∑ i, u i) z hz
    have hx₂ : 0 ≤ x - (∑ i, u i) - ∑ i, b i :=
      Problem520.gaussianWalkTerminalDistance_nonneg_of_survives n
        (x - ∑ i, u i) b hx₁ hb
    have hw := gaussianWalkSurvives_snd_of_harperFinSplit (x - ∑ i, u i) z hz
    have hsum : (∑ i, ω i) = (∑ i, u i) + (∑ i, b i) + ∑ i, w i := by
      rw [sum_harperFinSplit ω, sum_harperFinSplit z]
      dsimp [u, z, b, w]
      ring
    have ht' : Problem520.gaussianWalkTerminalDistance k
        (x - (∑ i, u i) - ∑ i, b i) w ≤ r := by
      unfold Problem520.gaussianWalkTerminalDistance at ht ⊢
      rw [hsum] at ht
      linarith
    have hwrev := survives_reverse_of_terminal_near
      (x - (∑ i, u i) - ∑ i, b i) r hx₂ w hw ht'
    have htop := Problem520.gaussianWalkTerminalDistance_nonneg_of_survives
      (m + (n + k)) x ω hx hs
    unfold Problem520.gaussianWalkTerminalDistance at ht htop
    rw [hsum] at ht htop
    change Problem520.gaussianWalkSurvives m x u ∧
      Problem520.gaussianWalkSurvives k r (harperReverseNegate w) ∧
      x - r ≤ (∑ i, u i) + (∑ i, w i) + ∑ i, b i ∧
      (∑ i, u i) + (∑ i, w i) + ∑ i, b i ≤ x
    exact ⟨hu, hwrev, by linarith, by linarith⟩
  have htransport := map_measureReal_apply
    (μ := Measure.pi fun i : Fin (m + (n + k)) => gaussianReal 0 (v i)) hT.measurable
    (measurable_threeBlockTerminalEvent m n k x r hx hr)
  rw [hT.map_eq] at htransport
  calc
    _ ≤ (Measure.pi fun i : Fin (m + (n + k)) => gaussianReal 0 (v i)).real
        (T ⁻¹' candidateGaussianThreeBlockTerminalEvent m n k x r) := measureReal_mono hsubset
    _ = ((P₁.prod P₃).prod P₂).real
        (candidateGaussianThreeBlockTerminalEvent m n k x r) := htransport.symm
    _ ≤ _ := candidate_gaussianThreeBlock_terminal_probability_le m n k hm hk
      v₁ v₂ v₃ hv x r hx hr (fun i => hlo _) (fun i => hhi _)
        (fun i => hlo _) (fun i => hhi _)

/-- Equal-length thirds expose the sharp inverse-three-halves decay with
the explicit constant inherited from the two ballot and one density bounds. -/
theorem candidate_gaussianWalkTerminalNear_probability_le_three_halves
    (m : ℕ) (hm : 0 < m) (v : Fin (m + (m + m)) → ℝ≥0)
    (x r : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hlo : ∀ i, (1 / 4 : ℝ≥0) ≤ v i) (hhi : ∀ i, v i ≤ (1 / 2 : ℝ≥0)) :
    (Measure.pi (fun i : Fin (m + (m + m)) => gaussianReal 0 (v i))).real
      (gaussianWalkTerminalNearSet (m + (m + m)) x r) ≤
        8192 * (x + 2) * (r + 2) * r / (Real.sqrt (m : ℝ)) ^ 3 := by
  let V : ℝ≥0 := ∑ i : Fin m, v (Fin.natAdd m (Fin.castAdd m i))
  have hVnn : (m : ℝ≥0) * (1 / 4) ≤ V := by
    calc
      _ = ∑ _i : Fin m, (1 / 4 : ℝ≥0) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => hlo _
  have hVR : (m : ℝ) * (1 / 4) ≤ (V : ℝ) := by exact_mod_cast hVnn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hVpos : (0 : ℝ) < V := by linarith
  have hv : V ≠ 0 := by exact_mod_cast hVpos.ne'
  have hsM : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmR
  have hsV : 0 < Real.sqrt (V : ℝ) := Real.sqrt_pos.2 hVpos
  have hsqrt : Real.sqrt (m : ℝ) / 2 ≤ Real.sqrt (V : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, Real.sq_sqrt hmR.le]
    norm_num
    linarith
  have hquot : r / Real.sqrt (V : ℝ) ≤ 2 * r / Real.sqrt (m : ℝ) := by
    apply (div_le_div_iff₀ hsV hsM).2
    nlinarith [mul_le_mul_of_nonneg_left hsqrt hr]
  have h := candidate_gaussianWalkTerminalNear_probability_le_three_blocks
    m m m hm hm v hv x r hx hr hlo hhi
  calc
    _ ≤ (64 * (x + 2) / Real.sqrt (m : ℝ)) *
        (64 * (r + 2) / Real.sqrt (m : ℝ)) * (r / Real.sqrt (V : ℝ)) := h
    _ ≤ (64 * (x + 2) / Real.sqrt (m : ℝ)) *
        (64 * (r + 2) / Real.sqrt (m : ℝ)) * (2 * r / Real.sqrt (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hquot (by positivity)
    _ = _ := by ring

end

end Erdos.Problem1144
