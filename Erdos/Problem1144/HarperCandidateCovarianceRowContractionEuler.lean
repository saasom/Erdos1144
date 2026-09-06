import Erdos.Problem1144.HarperCandidateCovarianceRowContraction

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

private theorem rowProduct_nonneg {X : Type*} {k : ℕ} {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) (z : (Fin k → X) × (Fin k → X)) : 0 ≤ candidateRowProduct f z :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => hf _) (Finset.prod_nonneg fun _ _ => hf _)

private theorem rowProduct_integrable {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [SigmaFinite ν] {f : X → ℝ} (hf : Integrable f ν) (k : ℕ) :
    Integrable (candidateRowProduct f) (candidateRowPowerMeasure ν k) := by
  have hp : Integrable (fun x : Fin k → X => ∏ i, f (x i)) (Measure.pi fun _ => ν) :=
    Integrable.fintype_prod fun _ => hf
  exact hp.mul_prod hp

/-- Contract the actual kernel-only partner heights, retaining the screen
and finite frequency cutoff on every height on which `F` depends. -/
theorem candidate_integral_screened_white_row_contraction (H : ℝ)
    {T B d : ℝ} (hT : 0 < T) (hTB : T ≤ B)
    {S : Set ℝ} (hS : MeasurableSet S) (k : ℕ)
    {F : ((Fin k → ℝ) × (Fin k → ℝ)) → ℝ}
    (hFm : Measurable F)
    (hFi : Integrable F (candidateRowPowerMeasure ((volume.restrict (Icc (-H) H)).restrict S) k))
    (hF : ∀ x, 0 ≤ F x) :
    (∫ z, F ((candidateRowRearrange k z).1) * candidateRowProduct
      (fun x : ℝ × ℝ => ‖candidateCovarianceWhiteKernel T B (x.1 - x.2)‖) z
      ∂candidateRowPowerMeasure
        (((volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H))).restrict
          (candidateRowPairDomain S d)) k) ≤
    candidateCovarianceLocalKernelMass T B d ^ (2 * k) *
      ∫ x, F x ∂candidateRowPowerMeasure ((volume.restrict (Icc (-H) H)).restrict S) k := by
  let μ₀ := volume.restrict (Icc (-H) H)
  let μ := μ₀.restrict S
  let E := candidateRowPairDomain S d
  let ν := (μ₀.prod μ₀).restrict E
  let w := fun x : ℝ × ℝ => (Icc (-d) d).indicator
    (fun h => ‖candidateCovarianceWhiteKernel T B h‖) (x.1 - x.2)
  have hw : ∀ x, 0 ≤ w x := fun x => indicator_nonneg (fun _ _ => norm_nonneg _) _
  have hwM : Measurable w :=
    ((candidate_measurable_whiteKernel T B).norm.indicator measurableSet_Icc).comp
      (measurable_fst.sub measurable_snd)
  have hC : 0 ≤ Real.log (B / T) := (norm_nonneg _).trans (candidate_whiteKernel_norm_le_log hT hTB 0)
  have hwC (x : ℝ × ℝ) : w x ≤ Real.log (B / T) := by
    by_cases hx : x.1 - x.2 ∈ Icc (-d) d
    · simpa only [w, indicator_of_mem hx] using candidate_whiteKernel_norm_le_log hT hTB (x.1 - x.2)
    · simpa only [w, indicator_of_notMem hx] using hC
  have hrow (x : ℝ) : (∫ y, w (x, y) ∂μ₀) ≤ candidateCovarianceLocalKernelMass T B d :=
    candidate_integral_local_whiteKernel_row_le hT hTB d x (Icc (-H) H)
  have hc := candidate_integral_row_kernel_contraction μ μ₀ k hFm hFi hF hwM hw hC
    (candidateCovarianceLocalKernelMass_nonneg T B d) hwC hrow
  have hmeasure : candidateRowPowerMeasure ν k ≤ candidateRowPowerMeasure (μ.prod μ₀) k := by
    dsimp only [ν, μ]
    rw [show (μ₀.restrict S).prod μ₀ = (μ₀.prod μ₀).restrict (S ×ˢ univ) from
      Measure.restrict_prod_eq_prod_univ S]
    rw [candidate_rowPowerMeasure_restrict, candidate_rowPowerMeasure_restrict]
    apply Measure.restrict_mono _ le_rfl
    intro z hz
    constructor
    · intro i hi
      exact ⟨(hz.1 i hi).1, mem_univ _⟩
    · intro i hi
      exact ⟨(hz.2 i hi).1, mem_univ _⟩
  have hν : ∀ᵐ x ∂ν, x ∈ E := ae_restrict_mem (candidate_measurableSet_rowPairDomain hS d)
  have hπ : ∀ᵐ z : Fin k → ℝ × ℝ ∂Measure.pi (fun _ => ν), ∀ i, z i ∈ E :=
    Filter.eventually_all.mpr fun i => Measure.tendsto_eval_ae_ae.eventually hν
  have he : ∀ᵐ z ∂candidateRowPowerMeasure ν k,
      candidateRowProduct (fun x : ℝ × ℝ => ‖candidateCovarianceWhiteKernel T B (x.1 - x.2)‖) z =
        candidateRowProduct w z := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hπ,
      Measure.quasiMeasurePreserving_snd.ae hπ] with z hz₁ hz₂
    unfold candidateRowProduct
    apply congrArg₂ (fun a b : ℝ => a * b)
    · apply Finset.prod_congr rfl
      intro i hi
      exact (indicator_of_mem (show (z.1 i).1 - (z.1 i).2 ∈ Icc (-d) d from abs_le.mp (hz₁ i).2.2) (fun h => ‖candidateCovarianceWhiteKernel T B h‖)).symm
    · apply Finset.prod_congr rfl
      intro i hi
      exact (indicator_of_mem (show (z.2 i).1 - (z.2 i).2 ∈ Icc (-d) d from abs_le.mp (hz₂ i).2.2) (fun h => ‖candidateCovarianceWhiteKernel T B h‖)).symm
  calc
    _ = ∫ z, F ((candidateRowRearrange k z).1) * candidateRowProduct w z
        ∂candidateRowPowerMeasure ν k := integral_congr_ae (he.mono fun z hz => by rw [hz])
    _ ≤ ∫ z, F ((candidateRowRearrange k z).1) * candidateRowProduct w z
        ∂candidateRowPowerMeasure (μ.prod μ₀) k :=
      integral_mono_measure hmeasure (ae_of_all _ fun z => mul_nonneg (hF _)
        (rowProduct_nonneg hw z)) hc.1
    _ ≤ _ := hc.2

/-- The squared-density resonant integral contracts to exactly `2k`
screened scalar heights. The Cauchy denominators and integer cell remain
literal; the only extracted factor is the local kernel mass to power `2k`. -/
theorem candidate_integral_resonant_euler_first_contraction (Y : ℕ) (ω : Omega) (H : ℝ)
    {T B d : ℝ} (hT : 0 < T) (hTB : T ≤ B)
    {S : Set ℝ} (hS : MeasurableSet S) (k : ℕ) (m : ℤ) (ε : ℝ) :
    (∫ z in {z | |candidateRowPowerFrequency Prod.fst z - m| ≤ ε},
      candidateRowProduct (fun x : ℝ × ℝ => candidateEulerBandSquaredWeight Y ω x.1) z *
        candidateRowProduct (fun x : ℝ × ℝ => ‖candidateCovarianceWhiteKernel T B (x.1 - x.2)‖) z
      ∂candidateRowPowerMeasure
        (((volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H))).restrict
          (candidateRowPairDomain S d)) k) ≤
    candidateCovarianceLocalKernelMass T B d ^ (2 * k) *
      ∫ x in {x | |candidateRowPowerFrequency id x - m| ≤ ε},
        candidateRowProduct (candidateEulerBandSquaredWeight Y ω) x
        ∂candidateRowPowerMeasure ((volume.restrict (Icc (-H) H)).restrict S) k := by
  let A : Set ((Fin k → ℝ) × (Fin k → ℝ)) := {x | |candidateRowPowerFrequency id x - m| ≤ ε}
  let F := A.indicator (candidateRowProduct (candidateEulerBandSquaredWeight Y ω))
  have hA : MeasurableSet A := by
    unfold A candidateRowPowerFrequency
    exact measurableSet_le (by fun_prop) measurable_const
  have hD : Measurable (candidateEulerBandSquaredWeight Y ω) := by
    rw [show candidateEulerBandSquaredWeight Y ω = (fun t => ‖candidateEulerAngularApprox Y 0 ω t‖ ^ 2) from funext (candidate_eulerBandSquaredWeight_eq_norm_sq Y ω)]
    exact (candidate_continuous_criticalEulerAngularApprox Y ω).measurable.norm.pow_const 2
  have hFm : Measurable F := by
    apply Measurable.indicator _ hA
    unfold candidateRowProduct
    fun_prop
  have hDi : Integrable (candidateEulerBandSquaredWeight Y ω)
      ((volume.restrict (Icc (-H) H)).restrict S) := by
    have hi : Integrable (fun t => ‖candidateEulerAngularApprox Y 0 ω t‖ ^ 2)
        (volume.restrict (Icc (-H) H)) :=
      ((candidate_continuous_criticalEulerAngularApprox Y ω).norm.pow 2).integrableOn_Icc
    rw [show candidateEulerBandSquaredWeight Y ω = (fun t => ‖candidateEulerAngularApprox Y 0 ω t‖ ^ 2) from funext (candidate_eulerBandSquaredWeight_eq_norm_sq Y ω)]
    exact hi.mono_measure Measure.restrict_le_self
  have hFi := (rowProduct_integrable hDi k).indicator hA
  have hF (x : (Fin k → ℝ) × (Fin k → ℝ)) : 0 ≤ F x := by
    apply indicator_nonneg _ x
    intro y hy
    apply rowProduct_nonneg _ y
    intro t
    rw [candidate_eulerBandSquaredWeight_eq_norm_sq]
    positivity
  have hc := candidate_integral_screened_white_row_contraction H hT hTB hS k hFm hFi hF (d := d)
  have hAc : MeasurableSet {z : (Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ) |
      |candidateRowPowerFrequency Prod.fst z - m| ≤ ε} := by
    unfold candidateRowPowerFrequency
    exact measurableSet_le (by fun_prop) measurable_const
  rw [← integral_indicator hAc, ← integral_indicator hA]
  convert hc using 1
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    by_cases hz : |candidateRowPowerFrequency Prod.fst z - m| ≤ ε
    · rw [indicator_of_mem (show z ∈ {z | |candidateRowPowerFrequency Prod.fst z - m| ≤ ε} from hz)]
      change _ = A.indicator _ ((candidateRowRearrange k z).1) * _
      rw [indicator_of_mem (show (candidateRowRearrange k z).1 ∈ A from hz)]
      rfl
    · rw [indicator_of_notMem (show z ∉ {z | |candidateRowPowerFrequency Prod.fst z - m| ≤ ε} from hz)]
      change _ = A.indicator _ ((candidateRowRearrange k z).1) * _
      rw [indicator_of_notMem (show (candidateRowRearrange k z).1 ∉ A from hz), zero_mul]

private theorem whiteKernel_norm_neg (T B h : ℝ) :
    ‖candidateCovarianceWhiteKernel T B (-h)‖ = ‖candidateCovarianceWhiteKernel T B h‖ := by
  have hc : candidateCovarianceWhiteKernel T B (-h) =
      starRingEnd ℂ (candidateCovarianceWhiteKernel T B h) := by
    unfold candidateCovarianceWhiteKernel candidateCovarianceMeasureKernel
    calc
      _ = ∫ r in Icc T B, starRingEnd ℂ (((1 / r : ℝ) : ℂ) * candidateCovariancePhase (-h * r)) := by
        apply integral_congr_ae
        exact ae_of_all _ fun r => by
          simp only [map_mul, Complex.conj_ofReal]
          congr 1
          unfold candidateCovariancePhase
          rw [← Complex.exp_conj]
          simp
      _ = _ := integral_conj
  rw [hc, RCLike.norm_conj]

private def rowSwap (k : ℕ) :
    ((Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ)) ≃ᵐ
      ((Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ)) where
  toFun z := (fun i => (z.1 i).swap, fun i => (z.2 i).swap)
  invFun z := (fun i => (z.1 i).swap, fun i => (z.2 i).swap)
  left_inv z := by ext <;> rfl
  right_inv z := by ext <;> rfl
  measurable_toFun := by dsimp; fun_prop
  measurable_invFun := by dsimp; fun_prop

private theorem rowSwap_preserving (H d : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (k : ℕ) :
    let ν := ((volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H))).restrict
      (candidateRowPairDomain S d)
    MeasurePreserving (rowSwap k) (candidateRowPowerMeasure ν k) (candidateRowPowerMeasure ν k) := by
  let μ₀ := volume.restrict (Icc (-H) H)
  let E := candidateRowPairDomain S d
  let ν := (μ₀.prod μ₀).restrict E
  have hE : MeasurableSet E := candidate_measurableSet_rowPairDomain hS d
  have hp : Prod.swap ⁻¹' E = E := by
    ext x
    change (x.2 ∈ S ∧ x.1 ∈ S ∧ |x.2 - x.1| ≤ d) ↔
      (x.1 ∈ S ∧ x.2 ∈ S ∧ |x.1 - x.2| ≤ d)
    rw [abs_sub_comm x.2 x.1]
    tauto
  have hswap : MeasurePreserving Prod.swap ν ν := by
    have h := (Measure.measurePreserving_swap (μ := μ₀) (ν := μ₀)).restrict_preimage hE
    rwa [hp] at h
  have hπ := measurePreserving_pi (fun _ : Fin k => ν) (fun _ : Fin k => ν) (fun _ => hswap)
  exact hπ.prod hπ

/-- Swapping the pair coordinates gives the identical contraction for the
second squared-density term; the screen and near-diagonal restriction are symmetric. -/
theorem candidate_integral_resonant_euler_second_contraction (Y : ℕ) (ω : Omega) (H : ℝ)
    {T B d : ℝ} (hT : 0 < T) (hTB : T ≤ B)
    {S : Set ℝ} (hS : MeasurableSet S) (k : ℕ) (m : ℤ) (ε : ℝ) :
    (∫ z in {z | |candidateRowPowerFrequency Prod.snd z - m| ≤ ε},
      candidateRowProduct (fun x : ℝ × ℝ => candidateEulerBandSquaredWeight Y ω x.2) z *
        candidateRowProduct (fun x : ℝ × ℝ => ‖candidateCovarianceWhiteKernel T B (x.1 - x.2)‖) z
      ∂candidateRowPowerMeasure
        (((volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H))).restrict
          (candidateRowPairDomain S d)) k) ≤
    candidateCovarianceLocalKernelMass T B d ^ (2 * k) *
      ∫ x in {x | |candidateRowPowerFrequency id x - m| ≤ ε},
        candidateRowProduct (candidateEulerBandSquaredWeight Y ω) x
        ∂candidateRowPowerMeasure ((volume.restrict (Icc (-H) H)).restrict S) k := by
  let ν := ((volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H))).restrict
      (candidateRowPairDomain S d)
  let Q := candidateRowPowerMeasure ν k
  let A₁ : Set ((Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ)) :=
    {z | |candidateRowPowerFrequency Prod.fst z - m| ≤ ε}
  let A₂ : Set ((Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ)) :=
    {z | |candidateRowPowerFrequency Prod.snd z - m| ≤ ε}
  let f₁ := fun z : (Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ) =>
    candidateRowProduct (fun x : ℝ × ℝ => candidateEulerBandSquaredWeight Y ω x.1) z *
      candidateRowProduct (fun x : ℝ × ℝ => ‖candidateCovarianceWhiteKernel T B (x.1 - x.2)‖) z
  let f₂ := fun z : (Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ) =>
    candidateRowProduct (fun x : ℝ × ℝ => candidateEulerBandSquaredWeight Y ω x.2) z *
      candidateRowProduct (fun x : ℝ × ℝ => ‖candidateCovarianceWhiteKernel T B (x.1 - x.2)‖) z
  have hA₁ : MeasurableSet A₁ := by
    unfold A₁ candidateRowPowerFrequency
    exact measurableSet_le (by fun_prop) measurable_const
  have hA₂ : MeasurableSet A₂ := by
    unfold A₂ candidateRowPowerFrequency
    exact measurableSet_le (by fun_prop) measurable_const
  have he : (∫ z in A₂, f₂ z ∂Q) = ∫ z in A₁, f₁ z ∂Q := by
    rw [← integral_indicator hA₂, ← integral_indicator hA₁]
    have h := (rowSwap_preserving H d hS k).integral_comp' (A₁.indicator f₁)
    calc
      _ = ∫ z, A₁.indicator f₁ (rowSwap k z) ∂Q := by
        apply integral_congr_ae
        exact ae_of_all _ fun z => by
          change A₂.indicator f₂ z = A₁.indicator f₁ (rowSwap k z)
          have hs : rowSwap k z ∈ A₁ ↔ z ∈ A₂ := Iff.rfl
          by_cases hz : z ∈ A₂
          · rw [indicator_of_mem hz, indicator_of_mem (hs.mpr hz)]
            dsimp only [f₁, f₂, candidateRowProduct, rowSwap, MeasurableEquiv.coe_mk]
            congr 1
            have hn (a b : ℝ) : ‖candidateCovarianceWhiteKernel T B (b - a)‖ =
                ‖candidateCovarianceWhiteKernel T B (a - b)‖ := by
              rw [show b - a = -(a - b) by ring, whiteKernel_norm_neg]
            apply congrArg₂ (fun a b : ℝ => a * b)
            · apply Finset.prod_congr rfl
              intro i hi
              exact (hn (z.1 i).1 (z.1 i).2).symm
            · apply Finset.prod_congr rfl
              intro i hi
              exact (hn (z.2 i).1 (z.2 i).2).symm
          · rw [indicator_of_notMem hz, indicator_of_notMem (hs.not.mpr hz)]
      _ = _ := h
  exact he.trans_le (candidate_integral_resonant_euler_first_contraction Y ω H hT hTB hS k m ε)

/-- The literal `4k`-height paired Euler integral contracts to its `2k`-height
screened squared-density integral in the cell enlarged by `2k d`. -/
theorem candidate_integral_resonant_paired_euler_contraction (Y : ℕ) (ω : Omega) (H : ℝ)
    {T B d : ℝ} (hT : 0 < T) (hTB : T ≤ B) (hd : 0 ≤ d)
    {S : Set ℝ} (hS : MeasurableSet S) (k : ℕ) (m : ℤ) (ε : ℝ) :
    (∫ z in {z | |candidateRowPowerFrequency Prod.snd z - m| ≤ ε},
      candidateRowProduct (candidateEulerBandRowWeight Y ω T B) z
      ∂candidateRowPowerMeasure
        (((volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H))).restrict
          (candidateRowPairDomain S d)) k) ≤
    candidateCovarianceLocalKernelMass T B d ^ (2 * k) *
      ∫ x in {x | |candidateRowPowerFrequency id x - m| ≤ ε + 2 * k * d},
        candidateRowProduct (candidateEulerBandSquaredWeight Y ω) x
        ∂candidateRowPowerMeasure ((volume.restrict (Icc (-H) H)).restrict S) k := by
  have hp := candidate_integral_resonant_paired_euler_le Y ω H hT hTB hd hS k m ε
  have h₁ := candidate_integral_resonant_euler_first_contraction Y ω H hT hTB hS k m
    (ε + 2 * k * d) (d := d)
  have h₂ := candidate_integral_resonant_euler_second_contraction Y ω H hT hTB hS k m
    (ε + 2 * k * d) (d := d)
  dsimp only at hp
  linarith

/-- Explicit sharp local-mass version of the actual resonant contraction. -/
theorem candidate_integral_resonant_paired_euler_contraction_log (Y : ℕ) (ω : Omega) (H : ℝ)
    {T B d : ℝ} (hT : 0 < T) (hTB : T ≤ B) (hd : 0 ≤ d)
    {S : Set ℝ} (hS : MeasurableSet S) (k : ℕ) (m : ℤ) (ε : ℝ) :
    (∫ z in {z | |candidateRowPowerFrequency Prod.snd z - m| ≤ ε},
      candidateRowProduct (candidateEulerBandRowWeight Y ω T B) z
      ∂candidateRowPowerMeasure
        (((volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H))).restrict
          (candidateRowPairDomain S d)) k) ≤
    (2 * (Real.log (B / T) + 2) * Real.log (1 + T * d) / T) ^ (2 * k) *
      ∫ x in {x | |candidateRowPowerFrequency id x - m| ≤ ε + 2 * k * d},
        candidateRowProduct (candidateEulerBandSquaredWeight Y ω) x
        ∂candidateRowPowerMeasure ((volume.restrict (Icc (-H) H)).restrict S) k := by
  apply (candidate_integral_resonant_paired_euler_contraction Y ω H hT hTB hd hS k m ε).trans
  apply mul_le_mul_of_nonneg_right
  · exact pow_le_pow_left₀ (candidateCovarianceLocalKernelMass_nonneg T B d)
      (candidate_local_whiteKernel_mass_le hT hTB hd) (2 * k)
  · apply integral_nonneg
    intro x
    apply rowProduct_nonneg _ x
    intro t
    rw [candidate_eulerBandSquaredWeight_eq_norm_sq]
    positivity

end
end Erdos.Problem1144
