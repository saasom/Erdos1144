import Erdos.Problem1144.HarperCandidateWeightedEulerInterval

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-!
# Conditioning the actual Euler interval energy on the small primes

This file applies concavity to the independent large-prime cube, after
identifying the joint finite law exactly. There is no conditional-moment
hypothesis: the product normalizer is calculated from the fair signs.
-/

private abbrev Cube (s : Finset ℕ) := s → Bool
private def cubeLaw (s : Finset ℕ) : Measure (Cube s) :=
  Measure.pi (fun _ ↦ Problem520.coin)
private instance (s : Finset ℕ) : IsProbabilityMeasure (cubeLaw s) := by
  unfold cubeLaw
  infer_instance
private def restrictSigns (s : Finset ℕ) (ω : Problem520.Omega) : Cube s := fun p ↦ ω p.1
private def setDensity (s : Finset ℕ) (a : ℝ) (ω : Problem520.Omega) (t : ℝ) : ℝ :=
  ∏ p ∈ s, harperRankinEulerFactor ω p a t
private def cubeDensity (s : Finset ℕ) (a : ℝ) (η : Cube s) (t : ℝ) : ℝ :=
  ∏ p : s, harperRankinCoordinateFactor p.1 a t (η p)

private theorem cubeDensity_restrict (s : Finset ℕ) (a t : ℝ)
    (ω : Problem520.Omega) :
    cubeDensity s a (restrictSigns s ω) t = setDensity s a ω t := by
  unfold cubeDensity setDensity
  change (∏ p : s, harperRankinEulerFactor ω p.1 a t) = _
  exact Finset.prod_coe_sort s (fun p ↦ harperRankinEulerFactor ω p a t)

private theorem integral_restrictSigns (s : Finset ℕ) (g : Cube s → ℝ) :
    (∫ ω, g (restrictSigns s ω) ∂Problem520.μ) = ∫ η, g η ∂cubeLaw s := by
  have hm : Measurable (restrictSigns s) :=
    measurable_pi_lambda _ fun p ↦ measurable_pi_apply p.1
  have hIndep : iIndepFun (fun p : s ↦ fun ω : Problem520.Omega ↦ ω p.1)
      Problem520.μ := Problem520.iIndepFun_coordinates.precomp Subtype.val_injective
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map
    (μ := Problem520.μ)
    (f := fun p : s ↦ fun ω : Problem520.Omega ↦ ω p.1)
    (fun p ↦ (measurable_pi_apply p.1).aemeasurable)).mp hIndep
  have hmap' : Problem520.μ.map (restrictSigns s) = cubeLaw s := by
    rw [show restrictSigns s = (fun ω p ↦ ω p.1) from rfl, hmap]
    unfold cubeLaw
    congr 1
    funext p
    exact Measure.infinitePi_map_eval (fun _ : ℕ ↦ Problem520.coin) p.1
  rw [← integral_map hm.aemeasurable (measurable_of_finite g).aestronglyMeasurable,
    hmap']

private theorem cubeDensity_nonneg (s : Finset ℕ) (a t : ℝ) (η : Cube s) :
    0 ≤ cubeDensity s a η t :=
  Finset.prod_nonneg fun p _ ↦ harperRankinEulerFactor_nonneg (fun _ ↦ η p) p.1 a t

private theorem cubeDensity_continuous (s : Finset ℕ) (a : ℝ) (η : Cube s) :
    Continuous (cubeDensity s a η) := by
  unfold cubeDensity harperRankinCoordinateFactor harperRankinEulerFactor
  fun_prop

private theorem integral_cubeDensity (s : Finset ℕ) (a t : ℝ) :
    (∫ η, cubeDensity s a η t ∂cubeLaw s) =
      ∏ p ∈ s, harperRankinEulerNormalizer p a := by
  let X : s → Cube s → ℝ := fun p η ↦ harperRankinCoordinateFactor p.1 a t (η p)
  have hbase : iIndepFun (fun p : s ↦ fun η : Cube s ↦ η p) (cubeLaw s) := by
    unfold cubeLaw
    exact iIndepFun_pi (X := fun _ : s ↦ id) (fun _ ↦ aemeasurable_id)
  have hX : iIndepFun X (cubeLaw s) := by
    simpa only [X, Function.comp_def] using
      hbase.comp (fun p b ↦ harperRankinCoordinateFactor p.1 a t b)
        (fun _ ↦ measurable_of_finite _)
  have hprod := hX.integral_fun_prod_eq_prod_integral
    (fun p ↦ (measurable_of_finite (X p)).aestronglyMeasurable)
  change (∫ η, ∏ p, X p η ∂cubeLaw s) = _
  rw [hprod]
  rw [← Finset.prod_coe_sort s (fun p ↦ harperRankinEulerNormalizer p a)]
  apply Finset.prod_congr rfl
  intro p _
  have hmp : MeasurePreserving (fun η : Cube s ↦ η p) (cubeLaw s) Problem520.coin := by
    unfold cubeLaw
    exact measurePreserving_eval (fun _ : s ↦ Problem520.coin) p
  have hi := integral_map (μ := cubeLaw s) hmp.measurable.aemeasurable
    (measurable_of_finite (harperRankinCoordinateFactor p.1 a t)).aestronglyMeasurable
  rw [hmp.map_eq] at hi
  change (∫ η, harperRankinCoordinateFactor p.1 a t (η p) ∂cubeLaw s) = _
  rw [← hi, Problem520.integral_coin_bool,
    harperRankinCoordinateFactor_false_add_true]
  ring

private theorem cubeDensity_union {s z : Finset ℕ} (h : Disjoint s z)
    (a t : ℝ) (η : Cube s) (ξ : Cube z) :
    cubeDensity (s ∪ z) a (MeasurableEquiv.piFinsetUnion (fun _ : ℕ ↦ Bool) h (η, ξ)) t =
      cubeDensity s a η t * cubeDensity z a ξ t := by
  let ω : Problem520.Omega := fun p ↦
    if hp : p ∈ s then η ⟨p, hp⟩ else if hp : p ∈ z then ξ ⟨p, hp⟩ else false
  have hs : restrictSigns s ω = η := by
    funext p
    simp [restrictSigns, ω, p.2]
  have hz : restrictSigns z ω = ξ := by
    funext p
    have hps : p.1 ∉ s := fun hps ↦ Finset.disjoint_left.mp h hps p.2
    simp [restrictSigns, ω, p.2, hps]
  have hu : restrictSigns (s ∪ z) ω =
      MeasurableEquiv.piFinsetUnion (fun _ : ℕ ↦ Bool) h (η, ξ) := by
    funext p
    rcases Finset.mem_union.mp p.2 with hp | hp
    · change ω p.1 = Equiv.piFinsetUnion (fun _ : ℕ ↦ Bool) h (η, ξ) p
      rw [Equiv.piFinsetUnion_left _ h hp p.2]
      simp [ω, hp]
    · have hps : p.1 ∉ s := fun hps ↦ Finset.disjoint_left.mp h hps hp
      change ω p.1 = Equiv.piFinsetUnion (fun _ : ℕ ↦ Bool) h (η, ξ) p
      rw [Equiv.piFinsetUnion_right _ h hp p.2]
      simp [ω, hp, hps]
  rw [← hu, ← hs, ← hz, cubeDensity_restrict, cubeDensity_restrict, cubeDensity_restrict]
  exact Finset.prod_union h

private theorem finite_swap {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ → ℝ)
    (u v : ℝ) (hf : ∀ ω, IntegrableOn (f ω) (Icc u v)) :
    (∫ ω, (∫ t in Icc u v, f ω t) ∂P) =
      ∫ t in Icc u v, ∫ ω, f ω t ∂P := by
  simp_rw [integral_fintype (Integrable.of_finite : Integrable _ P), smul_eq_mul]
  rw [integral_finset_sum _ (fun ω _ ↦ (hf ω).const_mul _)]
  simp_rw [integral_const_mul]

private theorem split_interval_moment {s z : Finset ℕ} (hsz : Disjoint s z)
    (a u v : ℝ) :
    (∫ ω, (∫ t in Icc u v, setDensity (s ∪ z) a ω t) ^ (1 / 8 : ℝ)
      ∂Problem520.μ) ≤
    (∏ p ∈ z, harperRankinEulerNormalizer p a) ^ (1 / 8 : ℝ) *
      (∫ ω, (∫ t in Icc u v, setDensity s a ω t) ^ (1 / 8 : ℝ)
        ∂Problem520.μ) := by
  let G : Cube (s ∪ z) → ℝ := fun θ ↦
    (∫ t in Icc u v, cubeDensity (s ∪ z) a θ t) ^ (1 / 8 : ℝ)
  have hleft := integral_restrictSigns (s ∪ z) G
  simp only [G, cubeDensity_restrict] at hleft
  rw [hleft]
  have hmp := measurePreserving_piFinsetUnion hsz (fun _ : ℕ ↦ Problem520.coin)
  have hconvert := hmp.integral_comp' G
  change (∫ θ, G θ ∂Measure.pi (fun _ : (s ∪ z : Finset ℕ) ↦ Problem520.coin)) ≤ _
  rw [← hconvert]
  rw [integral_prod _ Integrable.of_finite]
  have hnorm : 0 ≤ ∏ p ∈ z, harperRankinEulerNormalizer p a :=
    Finset.prod_nonneg fun p _ ↦ (harperRankinEulerNormalizer_pos p a).le
  have hsmall := integral_restrictSigns s
    (fun η ↦ (∫ t in Icc u v, cubeDensity s a η t) ^ (1 / 8 : ℝ))
  simp only [cubeDensity_restrict] at hsmall
  rw [hsmall, ← integral_const_mul]
  apply integral_mono Integrable.of_finite Integrable.of_finite
  intro η
  let Z : Cube z → ℝ := fun ξ ↦
    ∫ t in Icc u v, cubeDensity s a η t * cubeDensity z a ξ t
  have hZ (ξ : Cube z) : 0 ≤ Z ξ :=
    integral_nonneg fun t ↦ mul_nonneg
      (cubeDensity_nonneg s a t η) (cubeDensity_nonneg z a t ξ)
  have hJ : (∫ ξ, Z ξ ^ (1 / 8 : ℝ) ∂cubeLaw z) ≤
      (∫ ξ, Z ξ ∂cubeLaw z) ^ (1 / 8 : ℝ) := by
    exact (Real.concaveOn_rpow (by norm_num : (0 : ℝ) ≤ 1 / 8)
      (by norm_num : (1 / 8 : ℝ) ≤ 1)).le_map_integral
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 8)).continuousOn
      isClosed_Ici (ae_of_all _ hZ) Integrable.of_finite Integrable.of_finite
  have hmean : (∫ ξ, Z ξ ∂cubeLaw z) =
      (∏ p ∈ z, harperRankinEulerNormalizer p a) *
        (∫ t in Icc u v, cubeDensity s a η t) := by
    dsimp only [Z]
    rw [finite_swap (cubeLaw z)
      (fun ξ t ↦ cubeDensity s a η t * cubeDensity z a ξ t) u v (fun ξ ↦
        ((cubeDensity_continuous s a η).mul (cubeDensity_continuous z a ξ)).integrableOn_Icc)]
    simp_rw [integral_const_mul, integral_cubeDensity]
    rw [integral_mul_const]
    ring
  change (∫ ξ, G (MeasurableEquiv.piFinsetUnion (fun _ : ℕ ↦ Bool) hsz (η, ξ))
      ∂cubeLaw z) ≤ _
  simp only [G, cubeDensity_union]
  exact hJ.trans_eq (by
    rw [hmean, Real.mul_rpow hnorm (integral_nonneg fun t ↦ cubeDensity_nonneg s a t η)])

/-- The exact large-prime conditional Jensen bound for the actual interval
energy. Its only loss is the literal product of the fair one-prime second
moments over `y < p ≤ Y`. -/
theorem candidate_integral_shifted_euler_interval_split_le
    {y Y : ℕ} (hyY : y ≤ Y) (a u v : ℝ) :
    (∫ ω, candidateShiftedEulerIntervalEnergy Y a u v ω ^ (1 / 8 : ℝ)
        ∂Problem520.μ) ≤
      (∏ p ∈ (Y + 1).primesBelow \ (y + 1).primesBelow,
        harperRankinEulerNormalizer p a) ^ (1 / 8 : ℝ) *
      (∫ ω, candidateShiftedEulerIntervalEnergy y a u v ω ^ (1 / 8 : ℝ)
        ∂Problem520.μ) := by
  have hs : (y + 1).primesBelow ⊆ (Y + 1).primesBelow := by
    intro p hp
    rcases Nat.mem_primesBelow.mp hp with ⟨hp, hpP⟩
    exact Nat.mem_primesBelow.mpr ⟨by omega, hpP⟩
  have hd : Disjoint (y + 1).primesBelow
      ((Y + 1).primesBelow \ (y + 1).primesBelow) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_sdiff.mp hq).2 hp
  have hu : (y + 1).primesBelow ∪
      ((Y + 1).primesBelow \ (y + 1).primesBelow) = (Y + 1).primesBelow :=
    Finset.union_sdiff_of_subset hs
  have h := split_interval_moment hd a u v
  rw [hu] at h
  exact h

/-- The actual full finite Euler interval moment after retaining the
small-prime real-axis damping and integrating out every larger prime. -/
theorem candidate_integral_shifted_euler_interval_large_eighth_le
    {y Y : ℕ} (hy : 2 ≤ y) (hyY : y ≤ Y) {a u v : ℝ}
    (ha : 0 ≤ a) (huv : u ≤ v)
    (hwindow : ∀ t ∈ Icc u v, |t| ≤ (Real.log (y : ℝ))⁻¹) :
    (∫ ω, candidateShiftedEulerIntervalEnergy Y a u v ω ^ (1 / 8 : ℝ)
        ∂Problem520.μ) ≤
      Real.exp (-(∑ p ∈ (y + 1).primesBelow,
        harperRankinEulerRadius p a ^ 2) / 16) *
      ((∏ p ∈ (Y + 1).primesBelow \ (y + 1).primesBelow,
        harperRankinEulerNormalizer p a) *
        Real.exp (8 * (1 + (Real.log 4 + 4) / Real.log 2)) *
        (v - u)) ^ (1 / 8 : ℝ) := by
  have hnorm : 0 ≤ ∏ p ∈ (Y + 1).primesBelow \ (y + 1).primesBelow,
      harperRankinEulerNormalizer p a :=
    Finset.prod_nonneg fun p _ ↦ (harperRankinEulerNormalizer_pos p a).le
  refine (candidate_integral_shifted_euler_interval_split_le hyY a u v).trans ?_
  refine (mul_le_mul_of_nonneg_left
    (candidate_integral_shifted_euler_interval_eighth_le hy ha huv hwindow)
    (Real.rpow_nonneg hnorm (1 / 8 : ℝ))).trans_eq ?_
  rw [show (∏ p ∈ (Y + 1).primesBelow \ (y + 1).primesBelow,
      harperRankinEulerNormalizer p a) *
      Real.exp (8 * (1 + (Real.log 4 + 4) / Real.log 2)) * (v - u) =
    (∏ p ∈ (Y + 1).primesBelow \ (y + 1).primesBelow,
      harperRankinEulerNormalizer p a) *
      (Real.exp (8 * (1 + (Real.log 4 + 4) / Real.log 2)) * (v - u)) by ring,
    Real.mul_rpow hnorm (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr huv))]
  ring

end
end Erdos.Problem1144
