import Erdos.Problem1144.HarperCandidateCovarianceRowPower
import Erdos.Problem1144.HarperCandidateCovarianceRowResonance
import Erdos.Problem1144.HarperCandidateEnergyFatouIdentity
import Erdos.Problem1144.HarperCandidateCovarianceScreen

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- Product over both sets of `k` coordinates in the exact row expansion. -/
def candidateRowProduct {X : Type*} {k : ℕ} (f : X → ℝ)
    (z : (Fin k → X) × (Fin k → X)) : ℝ :=
  (∏ i, f (z.1 i)) * ∏ i, f (z.2 i)

/-- The actual unshifted squarefree Euler density, with its exact Cauchy
denominator inherited from the Perron transform. -/
def candidateEulerBandSquaredWeight (Y : ℕ) (ω : Omega) (t : ℝ) : ℝ :=
  Problem520.harperEulerDensity Y ω t / ((1 / 2 : ℝ) ^ 2 + t ^ 2)

/-- At zero Rankin shift the two literal finite Euler densities agree. -/
theorem candidate_critical_rankinDensity_eq (Y : ℕ) (ω : Omega) (t : ℝ) :
    harperRankinEulerDensity Y 0 ω t = Problem520.harperEulerDensity Y ω t := by
  unfold harperRankinEulerDensity Problem520.harperEulerDensity
  apply Finset.prod_congr rfl
  intro p hp
  simp only [harperRankinEulerFactor, Problem520.harperEulerFactor,
    harperRankinEulerRadius_zero, div_eq_mul_inv]
  ring

theorem candidate_eulerBandSquaredWeight_eq_norm_sq (Y : ℕ) (ω : Omega) (t : ℝ) :
    candidateEulerBandSquaredWeight Y ω t = ‖candidateEulerAngularApprox Y 0 ω t‖ ^ 2 := by
  rw [candidate_criticalEuler_norm_sq_eq_density, candidate_shifted_euler_density_neg,
    candidate_critical_rankinDensity_eq]
  rfl

/-- A common scalar screen and the literal near-diagonal restriction. -/
def candidateRowPairDomain (S : Set ℝ) (d : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ S ∧ z.2 ∈ S ∧ |z.1 - z.2| ≤ d}

theorem candidate_measurableSet_rowPairDomain {S : Set ℝ} (hS : MeasurableSet S) (d : ℝ) :
    MeasurableSet (candidateRowPairDomain S d) := by
  exact (hS.preimage measurable_fst).inter ((hS.preimage measurable_snd).inter
    (measurableSet_le (show Measurable (fun z : ℝ × ℝ => |z.1 - z.2|) by fun_prop)
      measurable_const))

private theorem rowProduct_nonneg {X : Type*} {k : ℕ} {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) (z : (Fin k → X) × (Fin k → X)) : 0 ≤ candidateRowProduct f z :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => hf _) (Finset.prod_nonneg fun _ _ => hf _)

private theorem rowProduct_mul {X : Type*} {k : ℕ} (f g : X → ℝ)
    (z : (Fin k → X) × (Fin k → X)) :
    candidateRowProduct (fun x => f x * g x) z = candidateRowProduct f z * candidateRowProduct g z := by
  simp only [candidateRowProduct, Finset.prod_mul_distrib]
  ring

private theorem rowProduct_sq {X : Type*} {k : ℕ} (f : X → ℝ)
    (z : (Fin k → X) × (Fin k → X)) :
    candidateRowProduct (fun x => f x ^ 2) z = candidateRowProduct f z ^ 2 := by
  simp only [candidateRowProduct, Finset.prod_pow, mul_pow]

private theorem rowProduct_integrable {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [SigmaFinite ν] {f : X → ℝ} (hf : Integrable f ν) (k : ℕ) :
    Integrable (candidateRowProduct f) (candidateRowPowerMeasure ν k) := by
  have hp : Integrable (fun z : Fin k → X => ∏ i, f (z i)) (Measure.pi fun _ => ν) :=
    Integrable.fintype_prod fun _ => hf
  exact hp.mul_prod hp

/-- The elementary pairing step acts on the whole `2k`-fold product. It
replaces paired absolute Euler factors by just `2k` squared Euler densities,
while retaining every reciprocal-time kernel weight. -/
theorem candidate_eulerBand_paired_product_le {k : ℕ} (Y : ℕ) (ω : Omega) (T B : ℝ)
    (z : (Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ)) :
    candidateRowProduct (candidateEulerBandRowWeight Y ω T B) z ≤
      ((candidateRowProduct (fun x : ℝ × ℝ => candidateEulerBandSquaredWeight Y ω x.1) z +
        candidateRowProduct (fun x : ℝ × ℝ => candidateEulerBandSquaredWeight Y ω x.2) z) / 2) *
      candidateRowProduct (fun x : ℝ × ℝ => ‖candidateCovarianceWhiteKernel T B (x.1 - x.2)‖) z := by
  change candidateRowProduct (fun x : ℝ × ℝ =>
    ‖candidateEulerAngularApprox Y 0 ω x.1‖ * ‖candidateEulerAngularApprox Y 0 ω x.2‖ *
      ‖candidateCovarianceWhiteKernel T B (x.1 - x.2)‖) z ≤ _
  simp_rw [candidate_eulerBandSquaredWeight_eq_norm_sq]
  simp only [rowProduct_mul, rowProduct_sq]
  apply mul_le_mul_of_nonneg_right _ (rowProduct_nonneg (fun _ => norm_nonneg _) z)
  nlinarith [sq_nonneg (candidateRowProduct
    (fun x : ℝ × ℝ => ‖candidateEulerAngularApprox Y 0 ω x.1‖) z -
      candidateRowProduct (fun x : ℝ × ℝ => ‖candidateEulerAngularApprox Y 0 ω x.2‖) z)]

private theorem squared_kernel_integrable (Y : ℕ) (ω : Omega) (H : ℝ)
    {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) (E : Set (ℝ × ℝ)) (side : Bool) :
    Integrable (fun x : ℝ × ℝ =>
      candidateEulerBandSquaredWeight Y ω (if side then x.1 else x.2) *
        ‖candidateCovarianceWhiteKernel T B (x.1 - x.2)‖)
      (((volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H))).restrict E) := by
  have hA : Integrable (fun t => ‖candidateEulerAngularApprox Y 0 ω t‖ ^ 2)
      (volume.restrict (Icc (-H) H)) :=
    ((candidate_continuous_criticalEulerAngularApprox Y ω).norm.pow 2).integrableOn_Icc
  have hK := candidate_measurable_whiteKernel T B
  have hAm := (candidate_continuous_criticalEulerAngularApprox Y ω).measurable
  have hOne : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc (-H) H)) := integrable_const _
  have hmajor : Integrable (fun x : ℝ × ℝ =>
      ‖candidateEulerAngularApprox Y 0 ω (if side then x.1 else x.2)‖ ^ 2 * Real.log (B / T))
      ((volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H))) := by
    cases side
    · simpa using (hOne.mul_prod hA).mul_const (Real.log (B / T))
    · simpa using (hA.mul_prod hOne).mul_const (Real.log (B / T))
  simp_rw [candidate_eulerBandSquaredWeight_eq_norm_sq]
  apply (hmajor.mono' ?_ ?_).mono_measure Measure.restrict_le_self
  · apply Measurable.aestronglyMeasurable
    cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  · exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (candidate_whiteKernel_norm_le_log hT hTB _) (sq_nonneg _)

private theorem paired_integrable (Y : ℕ) (ω : Omega) (H : ℝ)
    {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) (E : Set (ℝ × ℝ)) (k : ℕ) :
    Integrable (candidateRowProduct (candidateEulerBandRowWeight Y ω T B))
      (candidateRowPowerMeasure
        (((volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H))).restrict E) k) := by
  apply rowProduct_integrable
  have h := (candidate_integrable_eulerBandRowAmplitude Y ω H 0 hT hTB E).norm
  simpa only [candidate_eulerBandRowAmplitude_norm] using h

private theorem density_kernel_product_integrable (Y : ℕ) (ω : Omega) (H : ℝ)
    {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) (E : Set (ℝ × ℝ)) (k : ℕ) (side : Bool) :
    Integrable (fun z => candidateRowProduct
      (fun x : ℝ × ℝ => candidateEulerBandSquaredWeight Y ω (if side then x.1 else x.2)) z *
      candidateRowProduct (fun x : ℝ × ℝ => ‖candidateCovarianceWhiteKernel T B (x.1 - x.2)‖) z)
      (candidateRowPowerMeasure
        (((volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H))).restrict E) k) := by
  convert rowProduct_integrable (squared_kernel_integrable Y ω H hT hTB E side) k using 1
  funext z
  exact (rowProduct_mul _ _ z).symm

/-- On the literal screened near-diagonal domain, a resonant paired integral
is bounded by the two squared-density integrals in the same integer cell,
enlarged by exactly `2k d`. No expected mixed-moment estimate is assumed. -/
theorem candidate_integral_resonant_paired_euler_le (Y : ℕ) (ω : Omega) (H : ℝ)
    {T B d : ℝ} (hT : 0 < T) (hTB : T ≤ B) (hd : 0 ≤ d)
    {S : Set ℝ} (hS : MeasurableSet S) (k : ℕ) (m : ℤ) (ε : ℝ) :
    let ν := ((volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H))).restrict
      (candidateRowPairDomain S d)
    let Q := candidateRowPowerMeasure ν k
    (∫ z in {z | |candidateRowPowerFrequency Prod.snd z - m| ≤ ε},
      candidateRowProduct (candidateEulerBandRowWeight Y ω T B) z ∂Q) ≤
    ((∫ z in {z | |candidateRowPowerFrequency Prod.fst z - m| ≤ ε + 2 * k * d},
        candidateRowProduct (fun x : ℝ × ℝ => candidateEulerBandSquaredWeight Y ω x.1) z *
          candidateRowProduct (fun x : ℝ × ℝ => ‖candidateCovarianceWhiteKernel T B (x.1 - x.2)‖) z ∂Q) +
      (∫ z in {z | |candidateRowPowerFrequency Prod.snd z - m| ≤ ε + 2 * k * d},
        candidateRowProduct (fun x : ℝ × ℝ => candidateEulerBandSquaredWeight Y ω x.2) z *
          candidateRowProduct (fun x : ℝ × ℝ => ‖candidateCovarianceWhiteKernel T B (x.1 - x.2)‖) z ∂Q)) / 2 := by
  let E := candidateRowPairDomain S d
  let ν := ((volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H))).restrict E
  let Q := candidateRowPowerMeasure ν k
  let A : Set ((Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ)) :=
    {z | |candidateRowPowerFrequency Prod.snd z - m| ≤ ε}
  let A₁ : Set ((Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ)) :=
    {z | |candidateRowPowerFrequency Prod.fst z - m| ≤ ε + 2 * k * d}
  let A₂ : Set ((Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ)) :=
    {z | |candidateRowPowerFrequency Prod.snd z - m| ≤ ε + 2 * k * d}
  let f₀ := candidateRowProduct (candidateEulerBandRowWeight Y ω T B) (k := k)
  let f₁ := fun z : (Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ) => candidateRowProduct
    (fun x : ℝ × ℝ => candidateEulerBandSquaredWeight Y ω x.1) z *
      candidateRowProduct (fun x : ℝ × ℝ => ‖candidateCovarianceWhiteKernel T B (x.1 - x.2)‖) z
  let f₂ := fun z : (Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ) => candidateRowProduct
    (fun x : ℝ × ℝ => candidateEulerBandSquaredWeight Y ω x.2) z *
      candidateRowProduct (fun x : ℝ × ℝ => ‖candidateCovarianceWhiteKernel T B (x.1 - x.2)‖) z
  have hA : MeasurableSet A := by
    unfold A candidateRowPowerFrequency
    exact measurableSet_le (by fun_prop) measurable_const
  have hA₁ : MeasurableSet A₁ := by
    unfold A₁ candidateRowPowerFrequency
    exact measurableSet_le (by fun_prop) measurable_const
  have hA₂ : MeasurableSet A₂ := by
    unfold A₂ candidateRowPowerFrequency
    exact measurableSet_le (by fun_prop) measurable_const
  have hi₀ : Integrable (A.indicator f₀) Q :=
    (paired_integrable Y ω H hT hTB E k).indicator hA
  have hi₁ : Integrable (A₁.indicator f₁) Q :=
    (density_kernel_product_integrable Y ω H hT hTB E k true).indicator hA₁
  have hi₂ : Integrable (A₂.indicator f₂) Q :=
    (density_kernel_product_integrable Y ω H hT hTB E k false).indicator hA₂
  have hn (side : Bool) (z : (Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ)) :
      0 ≤ candidateRowProduct (fun x : ℝ × ℝ =>
        candidateEulerBandSquaredWeight Y ω (if side then x.1 else x.2)) z *
        candidateRowProduct (fun x : ℝ × ℝ => ‖candidateCovarianceWhiteKernel T B (x.1 - x.2)‖) z := by
    simp_rw [candidate_eulerBandSquaredWeight_eq_norm_sq]
    exact mul_nonneg (rowProduct_nonneg (fun _ => sq_nonneg _) z)
      (rowProduct_nonneg (fun _ => norm_nonneg _) z)
  have hν : ∀ᵐ x ∂ν, x ∈ E := ae_restrict_mem (candidate_measurableSet_rowPairDomain hS d)
  have hπ : ∀ᵐ z : Fin k → ℝ × ℝ ∂Measure.pi (fun _ => ν), ∀ i, z i ∈ E :=
    Filter.eventually_all.mpr fun i => Measure.tendsto_eval_ae_ae.eventually hν
  have hpoint : ∀ᵐ z ∂Q, A.indicator f₀ z ≤ (A₁.indicator f₁ z + A₂.indicator f₂ z) / 2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hπ,
      Measure.quasiMeasurePreserving_snd.ae hπ] with z hz₁ hz₂
    by_cases hz : z ∈ A
    · have hzA₁ : z ∈ A₁ := candidate_rowPowerFrequency_resonance_transfer
        Prod.fst Prod.snd z m (fun i => (hz₁ i).2.2) (fun i => (hz₂ i).2.2) hz
      have hzA₂ : z ∈ A₂ := hz.trans (show ε ≤ ε + 2 * (k : ℝ) * d from
        le_add_of_nonneg_right (by positivity))
      simp only [indicator_of_mem hz, indicator_of_mem hzA₁, indicator_of_mem hzA₂]
      have hp := candidate_eulerBand_paired_product_le Y ω T B z
      convert hp using 1 <;> dsimp [f₀, f₁, f₂] <;> ring
    · rw [indicator_of_notMem hz]
      exact div_nonneg (add_nonneg
        (indicator_nonneg (fun z _ => hn true z) _) (indicator_nonneg (fun z _ => hn false z) _)) (by norm_num)
  have hi := integral_mono_ae hi₀ ((hi₁.add hi₂).div_const 2) hpoint
  rw [integral_div] at hi
  dsimp only [Pi.add_apply] at hi
  rw [integral_add hi₁ hi₂, integral_indicator hA,
    integral_indicator hA₁, integral_indicator hA₂] at hi
  exact hi

end
end Erdos.Problem1144
