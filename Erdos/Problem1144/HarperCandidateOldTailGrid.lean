import Erdos.Problem1144.HarperCandidateLogScreen
import Erdos.Problem1144.HarperCandidateNegativeTail
import Erdos.Problem1144.HarperCandidateGridAveraging

open MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

/-!
# The deterministic old-tail grid in the candidate

This module assembles the literal log-time negative-tail estimate, fresh-sign
reflection, and deterministic block/shift averaging. The remaining transform
hypothesis is required only almost surely on the upper-envelope event.
-/

/-- Equation (36) for the literal logarithmic process under a fixed cylinder
law. The cutoff contains every conditioned coordinate. -/
theorem candidateCylinderLaw_logOld_negative_le_twice_logProcess
    (s : Finset ℕ) (η : s → Bool) (X : ℕ)
    (hs : ∀ p ∈ s, p ≤ X) {t : ℝ} (ht : 0 ≤ t)
    (hcut : ⌊Real.exp t⌋₊ < X ^ 2) (b : ℝ) :
    (candidateCylinderLaw s η).real {ω | harperCandidateLogOld ω X t < -b} ≤
      2 * (candidateCylinderLaw s η).real {ω | harperCandidateLogProcess ω t < -b} := by
  let fresh := largePrimeInterval X ⌊Real.exp t⌋₊
  have habove : ∀ p ∈ fresh, X < p := fun p hp => (mem_largePrimeInterval.mp hp).2.1
  have hdisj : Disjoint s fresh := by
    apply Finset.disjoint_left.mpr
    intro p hp hf
    exact (not_lt_of_ge (hs p hp)) (habove p hf)
  have hflip := candidateCylinderLaw_freshSignFlip s fresh η hdisj
  have hA : ∀ ω, harperCandidateLogOld (freshSignFlip fresh ω) X t =
      harperCandidateLogOld ω X t := by
    intro ω
    unfold harperCandidateLogOld
    rw [smoothProcess_freshSignFlip_eq_of_above fresh ω X _ habove]
  have hZ : ∀ ω, harperCandidateLogFresh (freshSignFlip fresh ω) X t =
      -harperCandidateLogFresh ω X t := by
    intro ω
    unfold harperCandidateLogFresh
    rw [largePrimeProcess_freshSignFlip_superset_eq_neg fresh ω hcut habove (by rfl),
      neg_mul]
  have h := candidate_measureReal_old_negative_le_twice_full hflip
    (fun ω => harperCandidateLogOld ω X t) (fun ω => harperCandidateLogFresh ω X t)
    b hA hZ
  simpa only [harperCandidateLogProcess_eq_logOld_add_logFresh _ ht hcut] using h

/-- A deterministic block and shift satisfying candidate equation (37), with
its exact covered-length denominator and no additional block-count loss.
All retained grid points lie in the prescribed linear fresh-prime window. -/
theorem candidate_exists_log_grid_old_negative_average_le
    (M : ℕ) (s : Finset ℕ) (η : s → Bool) (X : ℕ)
    (hs : ∀ p ∈ s, p ≤ X)
    {T α β b h : ℝ} {m n : ℕ}
    (hT : 0 < T) (hα : 0 ≤ α) (hαβ : α ≤ β) (hb : 0 < b)
    (hm : 0 < m) (hn : 0 < n) (hh : 0 < h)
    (hcover : α * T + (n : ℝ) * ((m : ℝ) * h) ≤ β * T)
    (hcut : ∀ t ∈ Ioc (α * T) (β * T), ⌊Real.exp t⌋₊ < X ^ 2)
    (hpaths : ∀ᵐ ω ∂candidateCylinderLaw s η, ω ∈ candidateUpperEnvelope M →
      IntegrableOn (fun t => Real.exp (-t / T) * harperCandidateLogProcess ω t) (Ioi 0) ∧
      0 ≤ ∫ t in Ioi 0, Real.exp (-t / T) * harperCandidateLogProcess ω t) :
    ∃ k < n, ∃ shift ∈ Ioc (0 : ℝ) h,
      (∀ i < m, α * T + (k : ℝ) * ((m : ℝ) * h) + (i : ℝ) * h + shift ∈
        Ioc (α * T) (β * T)) ∧
      (∑ i ∈ Finset.range m, (candidateCylinderLaw s η).real
        {ω | harperCandidateLogOld ω X
          (α * T + (k : ℝ) * ((m : ℝ) * h) + (i : ℝ) * h + shift) < -b}) / (m : ℝ) ≤
        2 * ((1 - (candidateCylinderLaw s η).real (candidateUpperEnvelope M)) *
          (β - α) * T + Real.exp β * M * T / b) / ((n : ℝ) * (m : ℝ) * h) := by
  let Q := candidateCylinderLaw s η
  let F : ℝ → ℝ := fun t => Q.real {ω | harperCandidateLogOld ω X t < -b}
  let G : ℝ → ℝ := fun t => Q.real {ω | harperCandidateLogProcess ω t < -b}
  have hab : α * T ≤ β * T := mul_le_mul_of_nonneg_right hαβ hT.le
  have hFint : IntegrableOn F (Ioc (α * T) (β * T)) :=
    candidate_integrable_negativeTail_probability (Q := Q)
      (ν := volume.restrict (Ioc (α * T) (β * T)))
      (a := fun z => harperCandidateLogOld z.1 X z.2) (b := b)
      (measurable_harperCandidateLogOld_joint X)
  have hGint : IntegrableOn G (Ioc (α * T) (β * T)) :=
    candidate_integrable_negativeTail_probability (Q := Q)
      (ν := volume.restrict (Ioc (α * T) (β * T)))
      (a := fun z => harperCandidateLogProcess z.1 z.2) (b := b)
      measurable_harperCandidateLogProcess
  have hfull : (∫ t in Ioc (α * T) (β * T), G t) ≤
      (1 - Q.real (candidateUpperEnvelope M)) * (β - α) * T +
        Real.exp β * M * T / b := by
    have hpathFull : ∀ᵐ ω ∂Q, ω ∈ candidateUpperEnvelope M →
        IntegrableOn (fun t => Real.exp (-t / T) * harperCandidateLogProcess ω t) (Ioi 0) ∧
        (∀ᵐ t ∂volume.restrict (Ioi 0), harperCandidateLogProcess ω t ≤ M) ∧
        0 ≤ ∫ t in Ioi 0, Real.exp (-t / T) * harperCandidateLogProcess ω t := by
      filter_upwards [hpaths] with ω hω
      intro hE
      exact ⟨(hω hE).1, ae_of_all _ (fun t =>
        harperCandidateLogProcess_le_of_normSum_le ω (Nat.cast_nonneg M) hE t),
        (hω hE).2⟩
    have ht := candidate_integral_negativeTail_exp_window_le_of_ae
      (Q := Q) (a := fun z => harperCandidateLogProcess z.1 z.2)
      measurable_harperCandidateLogProcess (measurableSet_candidateUpperEnvelope M)
      (Nat.cast_nonneg M) hb hT hα hαβ hpathFull
    simpa only [probReal_compl_eq_one_sub (measurableSet_candidateUpperEnvelope M)] using ht
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioc (α * T) (β * T)), F t ≤ 2 * G t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 ≤ t := (mul_nonneg hα hT.le).trans ht.1.le
    exact candidateCylinderLaw_logOld_negative_le_twice_logProcess s η X hs ht0 (hcut t ht) b
  have hfold : (∫ t in Ioc (α * T) (β * T), F t) ≤
      2 * ((1 - Q.real (candidateUpperEnvelope M)) * (β - α) * T +
        Real.exp β * M * T / b) := by
    calc
      _ ≤ ∫ t in Ioc (α * T) (β * T), 2 * G t :=
        integral_mono_ae hFint (hGint.const_mul 2) hpoint
      _ = 2 * ∫ t in Ioc (α * T) (β * T), G t := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hfull (by norm_num)
  obtain ⟨k, hk, shift, hshift, havg⟩ := candidate_exists_block_shift_grid_average_le
    (F := F)
    hh hn hm hcover ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hFint)
    (ae_of_all _ fun t => measureReal_nonneg)
  refine ⟨k, hk, shift, hshift, ?_, havg.trans ?_⟩
  · intro i hi
    exact candidate_grid_point_mem_window hh.le hcover hk hi hshift
  · rw [intervalIntegral.integral_of_le hab]
    exact div_le_div_of_nonneg_right hfold (by positivity)

end Erdos.Problem1144

#print axioms Erdos.Problem1144.candidateCylinderLaw_logOld_negative_le_twice_logProcess
#print axioms Erdos.Problem1144.candidate_exists_log_grid_old_negative_average_le
