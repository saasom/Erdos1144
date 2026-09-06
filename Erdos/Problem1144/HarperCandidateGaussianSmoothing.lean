import Erdos.Problem1144.HarperCandidateGaussianIteration
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos.Problem1144

/-- The Leibniz rule sums to a power of the sum of coordinate bounds. This
is the dimension-independent estimate needed for product smoothing. -/
theorem candidate_iteratedDeriv_prod_bound {ι : Type*}
    (s : Finset ι) (f : ι → ℝ → ℝ) (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (q : ℕ)
    (hf : ∀ i ∈ s, ContDiff ℝ q (f i))
    (hb : ∀ i ∈ s, ∀ k ≤ q, ∀ t, |iteratedDeriv k (f i) t| ≤ r i ^ k)
    (k : ℕ) (hk : k ≤ q) (t : ℝ) :
    |iteratedDeriv k (fun x => ∏ i ∈ s, f i x) t| ≤ (∑ i ∈ s, r i) ^ k := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty => cases k <;> simp [iteratedDeriv_const]
  | @insert i s hi ih =>
      have hfi := hf i (Finset.mem_insert_self _ _)
      have hfs : ∀ j ∈ s, ContDiff ℝ q (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have hbs : ∀ j ∈ s, ∀ l ≤ q, ∀ x, |iteratedDeriv l (f j) x| ≤ r j ^ l :=
        fun j hj => hb j (Finset.mem_insert_of_mem hj)
      have hfp : ContDiff ℝ q (fun x => ∏ j ∈ s, f j x) := contDiff_prod hfs
      have he : (fun x => ∏ j ∈ insert i s, f j x) =
          (fun x => f i x * ∏ j ∈ s, f j x) := by
        funext x
        exact Finset.prod_insert hi
      rw [he, iteratedDeriv_fun_mul
        (hfi.of_le (by exact_mod_cast hk)).contDiffAt
        (hfp.of_le (by exact_mod_cast hk)).contDiffAt,
        Finset.sum_insert hi, add_pow]
      calc
        _ ≤ ∑ j ∈ Finset.range (k + 1),
            |(k.choose j : ℝ) * iteratedDeriv j (f i) t *
              iteratedDeriv (k - j) (fun x => ∏ l ∈ s, f l x) t| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.range (k + 1), r i ^ j * (∑ l ∈ s, r l) ^ (k - j) *
            (k.choose j : ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          have hleft := hb i (Finset.mem_insert_self _ _) j (hjk.trans hk) t
          have hright := ih hfs hbs (k - j) ((Nat.sub_le _ _).trans hk)
          rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
          calc
            _ ≤ (k.choose j : ℝ) * r i ^ j * (∑ l ∈ s, r l) ^ (k - j) := by
              gcongr
              exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hr i) _)
            _ = _ := by ring

private theorem candidate_compactSupport_iteratedDeriv
    {f : ℝ → ℝ} (hf : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k f) := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv

/-- A fixed smooth bump has one constant controlling its first three
derivatives. This constant depends only on the two radii. -/
theorem candidate_bump_derivative_power_bound (b : ContDiffBump (0 : ℝ)) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k ≤ 3, ∀ t : ℝ, |iteratedDeriv k b t| ≤ B ^ k := by
  have hex : ∀ k : Fin 4, ∃ C : ℝ, ∀ t : ℝ, |iteratedDeriv (k : ℕ) b t| ≤ C := by
    intro k
    have hc : Continuous (iteratedDeriv (k : ℕ) b) :=
      (b.contDiff : ContDiff ℝ (k : ℕ) b).continuous_iteratedDeriv' _
    simpa only [Real.norm_eq_abs] using
      (candidate_compactSupport_iteratedDeriv b.hasCompactSupport (k : ℕ)).exists_bound_of_continuous hc
  choose C hC using hex
  let B : ℝ := 1 + ∑ k : Fin 4, max 0 (C k)
  have hB : 1 ≤ B := by
    have hs : 0 ≤ ∑ k : Fin 4, max 0 (C k) := Finset.sum_nonneg fun _ _ => le_max_left _ _
    dsimp [B]
    linarith
  refine ⟨B, hB, ?_⟩
  intro k hk t
  by_cases hk0 : k = 0
  · subst k
    simpa only [iteratedDeriv_zero, pow_zero, abs_of_nonneg b.nonneg] using b.le_one (x := t)
  · let j : Fin 4 := ⟨k, by omega⟩
    have hj : C j ≤ B := by
      have hsum := Finset.single_le_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin 4))) =>
        le_max_left 0 (C l)) (Finset.mem_univ j)
      dsimp only [B]
      exact (le_max_right 0 (C j)).trans (hsum.trans (by linarith))
    exact (hC j t).trans (hj.trans (le_self_pow₀ hB hk0))

/-- A selected absolute-maximum test obtained by multiplying fixed
one-dimensional bumps. -/
noncomputable def candidateAbsoluteMaxSmooth {ι : Type*}
    (b : ContDiffBump (0 : ℝ)) (J : Finset ι) (x : ι → ℝ) : ℝ :=
  1 - ∏ i ∈ J, b (x i)

theorem candidateAbsoluteMaxSmooth_mem_Icc {ι : Type*}
    (b : ContDiffBump (0 : ℝ)) (J : Finset ι) (x : ι → ℝ) :
    candidateAbsoluteMaxSmooth b J x ∈ Icc 0 1 := by
  have h0 : 0 ≤ ∏ i ∈ J, b (x i) := Finset.prod_nonneg fun _ _ => b.nonneg
  have h1 : (∏ i ∈ J, b (x i)) ≤ 1 := Finset.prod_le_one
    (fun _ _ => b.nonneg) (fun _ _ => b.le_one)
  constructor <;> dsimp [candidateAbsoluteMaxSmooth] <;> linarith

theorem candidateAbsoluteMaxSmooth_eq_zero {ι : Type*}
    (b : ContDiffBump (0 : ℝ)) (J : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ J, |x i| ≤ b.rIn) : candidateAbsoluteMaxSmooth b J x = 0 := by
  have hb : ∀ i ∈ J, b (x i) = 1 := by
    intro i hi
    apply b.one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hx i hi
  simp [candidateAbsoluteMaxSmooth, Finset.prod_eq_one hb]

theorem candidateAbsoluteMaxSmooth_eq_one {ι : Type*}
    (b : ContDiffBump (0 : ℝ)) (J : Finset ι) (x : ι → ℝ)
    (hx : ∃ i ∈ J, b.rOut ≤ |x i|) : candidateAbsoluteMaxSmooth b J x = 1 := by
  obtain ⟨i, hi, hx⟩ := hx
  have hb : b (x i) = 0 := b.zero_of_le_dist (by simpa only [Real.dist_eq, sub_zero] using hx)
  simp [candidateAbsoluteMaxSmooth, Finset.prod_eq_zero (f := fun i => b (x i)) hi hb]

/-- The third derivative in any affine direction has a cubic `l¹` bound.
There is no factor exponential in the number of selected coordinates. -/
theorem candidateAbsoluteMaxSmooth_affine_third_bound {ι : Type*}
    (b : ContDiffBump (0 : ℝ)) {B : ℝ} (hB : 1 ≤ B)
    (hb : ∀ k ≤ 3, ∀ t : ℝ, |iteratedDeriv k b t| ≤ B ^ k)
    (J : Finset ι) (z a : ι → ℝ) (t : ℝ) :
    |iteratedDeriv 3 (fun s => candidateAbsoluteMaxSmooth b J (fun i => z i + a i * s)) t| ≤
      B ^ 3 * (∑ i ∈ J, |a i|) ^ 3 := by
  have hf (i : ι) : ContDiff ℝ 3 (fun s => b (z i + a i * s)) :=
    b.contDiff.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hd (i : ι) (k : ℕ) (hk : k ≤ 3) (s : ℝ) :
      |iteratedDeriv k (fun t => b (z i + a i * t)) s| ≤ (B * |a i|) ^ k := by
    have hc : ContDiff ℝ k (fun t => b (z i + t)) :=
      b.contDiff.comp (contDiff_const.add contDiff_id)
    rw [iteratedDeriv_comp_const_mul hc (a i), iteratedDeriv_comp_const_add,
      abs_mul, abs_pow, mul_pow]
    exact (mul_le_mul_of_nonneg_left (hb k hk _) (pow_nonneg (abs_nonneg _) _)).trans_eq (by ring)
  have h := candidate_iteratedDeriv_prod_bound J
    (fun i s => b (z i + a i * s)) (fun i => B * |a i|)
    (fun i => mul_nonneg (by linarith) (abs_nonneg _)) 3
    (fun i _ => hf i) (fun i _ => hd i) 3 le_rfl t
  change |iteratedDeriv 3 (fun s => 1 - ∏ i ∈ J, b (z i + a i * s)) t| ≤ _
  rw [iteratedDeriv_const_sub (by norm_num), iteratedDeriv_neg, abs_neg]
  simpa only [← Finset.mul_sum, mul_pow] using h

private theorem candidate_linearForm_update {n : ℕ}
    (a v : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    (∑ p, a p * Function.update v j t p) =
      (∑ p ∈ Finset.univ.erase j, a p * v p) + a j * t := by
  classical
  have he : (fun p => a p * Function.update v j t p) =
      Function.update (fun p => a p * v p) j (a j * t) := by
    funext p
    by_cases hp : p = j
    · subst p
      simp
    · simp [hp]
  rw [he, Finset.sum_update_of_mem (Finset.mem_univ j)]
  simp only [Finset.sdiff_singleton_eq_erase]
  ring

private theorem candidate_selected_linear_smooth_replacement
    {n : ℕ} {ι : Type*} (b : ContDiffBump (0 : ℝ)) {B : ℝ} (hB : 1 ≤ B)
    (hb : ∀ k ≤ 3, ∀ t : ℝ, |iteratedDeriv k b t| ≤ B ^ k)
    (J : Finset ι) (a : Fin n → ι → ℝ) :
    let F : (Fin n → ℝ) → ℝ := fun v =>
      candidateAbsoluteMaxSmooth b J (fun i => ∑ p, a p i * v p)
    |(∫ v, F v ∂Measure.pi (fun _ : Fin n => candidateRademacherLaw)) -
      ∫ v, F v ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)| ≤
      (B ^ 3 / 6) * (1 + ∫ t : ℝ, |t| ^ 3 ∂gaussianReal 0 1) *
        ∑ p, (∑ i ∈ J, |a p i|) ^ 3 := by
  classical
  dsimp only
  let F : (Fin n → ℝ) → ℝ := fun v =>
    candidateAbsoluteMaxSmooth b J (fun i => ∑ p, a p i * v p)
  have hF : Measurable F := by
    unfold F candidateAbsoluteMaxSmooth
    apply measurable_const.sub
    apply Finset.measurable_prod
    intro i _
    exact (b.contDiff : ContDiff ℝ 3 b).continuous.measurable.comp
      (Finset.measurable_sum _ fun p _ => measurable_const.mul (measurable_pi_apply p))
  have hD : ∀ v, |F v| ≤ 1 := by
    intro v
    have h := candidateAbsoluteMaxSmooth_mem_Icc b J (fun i => ∑ p, a p i * v p)
    exact (abs_le.mpr ⟨by linarith [h.1], h.2⟩)
  have hsection (j : Fin n) (v : Fin n → ℝ) :
      (fun t => F (Function.update v j t)) =
        (fun t => candidateAbsoluteMaxSmooth b J
          (fun i => (∑ p ∈ Finset.univ.erase j, a p i * v p) + a j i * t)) := by
    funext t
    unfold F
    congr 1
    funext i
    exact candidate_linearForm_update (fun p => a p i) v j t
  have hC3 (j : Fin n) (v : Fin n → ℝ) :
      ContDiff ℝ 3 (fun t => F (Function.update v j t)) := by
    rw [hsection]
    unfold candidateAbsoluteMaxSmooth
    apply contDiff_const.sub
    apply contDiff_prod
    intro i _
    exact b.contDiff.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hC (j : Fin n) (v : Fin n → ℝ) (t : ℝ) :
      |iteratedDeriv 3 (fun s => F (Function.update v j s)) t| ≤
        B ^ 3 * (∑ i ∈ J, |a j i|) ^ 3 := by
    rw [hsection]
    exact candidateAbsoluteMaxSmooth_affine_third_bound b hB hb J _ _ t
  have h := candidate_pi_rademacher_gaussian_smooth_replacement F hF
    (fun j => B ^ 3 * (∑ i ∈ J, |a j i|) ^ 3) hD hC3 hC
  rw [← Finset.mul_sum] at h
  exact h.trans_eq (by ring)

private theorem candidate_selected_linear_max_comparison_of_bump
    {n : ℕ} {ι : Type*} (b : ContDiffBump (0 : ℝ)) {B : ℝ} (hB : 1 ≤ B)
    (hb : ∀ k ≤ 3, ∀ t : ℝ, |iteratedDeriv k b t| ≤ B ^ k)
    (J : Finset ι) (a : Fin n → ι → ℝ) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
        {v | ∃ i ∈ J, b.rOut ≤ |∑ p, a p i * v p|} ≤
      (Measure.pi (fun _ : Fin n => candidateRademacherLaw)).real
        {v | ∃ i ∈ J, b.rIn < |∑ p, a p i * v p|} +
      (B ^ 3 / 6) * (1 + ∫ t : ℝ, |t| ^ 3 ∂gaussianReal 0 1) *
        ∑ p, (∑ i ∈ J, |a p i|) ^ 3 := by
  classical
  let R : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => candidateRademacherLaw
  let G : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => gaussianReal 0 1
  let F : (Fin n → ℝ) → ℝ := fun v =>
    candidateAbsoluteMaxSmooth b J (fun i => ∑ p, a p i * v p)
  let ER : Set (Fin n → ℝ) := {v | ∃ i ∈ J, b.rIn < |∑ p, a p i * v p|}
  let EG : Set (Fin n → ℝ) := {v | ∃ i ∈ J, b.rOut ≤ |∑ p, a p i * v p|}
  have hlin (i : ι) : Measurable fun v : Fin n → ℝ => ∑ p, a p i * v p :=
    Finset.measurable_sum _ fun p _ => measurable_const.mul (measurable_pi_apply p)
  have hER : MeasurableSet ER := by
    convert J.measurableSet_biUnion (fun i _ => measurableSet_lt
      (measurable_const : Measurable (fun _ : Fin n → ℝ => b.rIn)) (hlin i).abs) using 1
    ext v
    simp [ER]
  have hEG : MeasurableSet EG := by
    convert J.measurableSet_biUnion (fun i _ => measurableSet_le
      (measurable_const : Measurable (fun _ : Fin n → ℝ => b.rOut)) (hlin i).abs) using 1
    ext v
    simp [EG]
  have hF : Measurable F := measurable_const.sub
    (Finset.measurable_prod _ fun i _ =>
      (b.contDiff : ContDiff ℝ 3 b).continuous.measurable.comp (hlin i))
  have hFi (P : Measure (Fin n → ℝ)) [IsProbabilityMeasure P] : Integrable F P := by
    apply Integrable.of_bound hF.aestronglyMeasurable 1
    filter_upwards [] with v
    have h := candidateAbsoluteMaxSmooth_mem_Icc b J (fun i => ∑ p, a p i * v p)
    exact abs_le.mpr ⟨by linarith [h.1], h.2⟩
  have hFR : (∫ v, F v ∂R) ≤ R.real ER := by
    rw [← integral_indicator_one hER]
    apply integral_mono (hFi R) ((integrable_const _).indicator hER)
    intro v
    by_cases hv : v ∈ ER
    · rw [indicator_of_mem hv]
      exact (candidateAbsoluteMaxSmooth_mem_Icc b J _).2
    · rw [indicator_of_notMem hv]
      apply le_of_eq
      apply candidateAbsoluteMaxSmooth_eq_zero
      intro i hi
      exact le_of_not_gt fun h => hv ⟨i, hi, h⟩
  have hFG : G.real EG ≤ ∫ v, F v ∂G := by
    rw [← integral_indicator_one hEG]
    apply integral_mono ((integrable_const _).indicator hEG) (hFi G)
    intro v
    by_cases hv : v ∈ EG
    · rw [indicator_of_mem hv]
      exact le_of_eq (candidateAbsoluteMaxSmooth_eq_one b J _ hv).symm
    · rw [indicator_of_notMem hv]
      exact (candidateAbsoluteMaxSmooth_mem_Icc b J _).1
  have hrep := candidate_selected_linear_smooth_replacement b hB hb J a
  change |(∫ v, F v ∂R) - ∫ v, F v ∂G| ≤ _ at hrep
  rw [abs_sub_comm] at hrep
  have hdiff := (le_abs_self ((∫ v, F v ∂G) - ∫ v, F v ∂R)).trans hrep
  change G.real EG ≤ R.real ER + _
  linarith

/-- The complete selected-maximum replacement theorem. For each fixed
threshold and smoothing margin there is one positive constant, independent
of both dimensions and of the retained set. All smoothness estimates are
proved by the compact bump construction above. -/
theorem candidate_selected_linear_max_rademacher_comparison
    {K δ : ℝ} (hK : 0 < K) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (J : Finset (Fin m)) (a : Fin n → Fin m → ℝ),
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
          {v | ∃ i ∈ J, K + δ ≤ |∑ p, a p i * v p|} ≤
        (Measure.pi (fun _ : Fin n => candidateRademacherLaw)).real
          {v | ∃ i ∈ J, K < |∑ p, a p i * v p|} +
        C * ∑ p, (∑ i ∈ J, |a p i|) ^ 3 := by
  let b : ContDiffBump (0 : ℝ) := ⟨K, K + δ, hK, by linarith⟩
  obtain ⟨B, hB, hb⟩ := candidate_bump_derivative_power_bound b
  let C := (B ^ 3 / 6) * (1 + ∫ t : ℝ, |t| ^ 3 ∂gaussianReal 0 1)
  have hC : 0 < C := by
    have hthird : 0 ≤ ∫ t : ℝ, |t| ^ 3 ∂gaussianReal 0 1 :=
      integral_nonneg fun t => pow_nonneg (abs_nonneg t) 3
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro n m J a
  exact candidate_selected_linear_max_comparison_of_bump b hB hb J a

end Erdos.Problem1144
