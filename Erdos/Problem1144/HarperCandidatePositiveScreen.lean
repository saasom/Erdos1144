import Erdos.Problem1144.HarperCandidateLogScreen

open MeasureTheory
open scoped BigOperators

namespace Erdos.Problem1144

/-!
# A fixed positive crossing probability suffices

The cylinder argument does not require crossing probability tending to one.
A uniform positive lower bound permits fixed losses in the covariance
transfers, including the elementary reflection substitute for Anderson.
-/

/-- General form of the envelope-deficit algebra, allowing fixed probability
losses in the analytic comparison steps. -/
theorem candidate_envelope_gap_of_approximate_screens_with_mass
    {q ρ p : ℝ} (hρ : ρ < 1)
    (h : ∀ ε : ℝ, 0 < ε →
      q ≤ 1 - (p - ε) / 2 + (2 * (1 - q) + ε) / (1 - ρ)) :
    q ≤ 1 - p * (1 - ρ) / (2 * (3 - ρ)) := by
  have hd : 0 < 1 - ρ := by linarith
  have he : 0 < 3 - ρ := by linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  have hs := h (2 * ε) (by positivity)
  have hs' : (q - 1 + (p - 2 * ε) / 2) * (1 - ρ) ≤
      2 * (1 - q) + 2 * ε := by
    apply (le_div_iff₀ hd).mp
    linarith
  have ht : (1 - p * (1 - ρ) / (2 * (3 - ρ)) + ε) * (3 - ρ) =
      (3 - ρ) - p * (1 - ρ) / 2 + ε * (3 - ρ) := by
    field_simp
  apply (mul_le_mul_iff_left₀ he).mp
  rw [ht]
  nlinarith

/-- The literal candidate screen with any uniform positive absolute-crossing
mass `p`, rather than requiring mass arbitrarily close to one. -/
def CandidateLogCylinderScreenStatementWithMass (ρ p : ℝ) : Prop :=
  ∀ (M : ℕ) (s : Finset ℕ) (η : s → Bool) (ε : ℝ), 0 < ε →
    ∃ (X m : ℕ) (t : Fin m → ℝ) (b : ℝ),
      0 < m ∧ (∀ q ∈ s, q ≤ X) ∧
      (∀ i, 0 ≤ t i ∧ ⌊Real.exp (t i)⌋₊ < X ^ 2) ∧
      (∑ i, (candidateCylinderLaw s η).real
          {ω | harperCandidateLogOld ω X (t i) < -b}) ≤
        (2 * (1 - (candidateCylinderLaw s η).real (candidateUpperEnvelope M)) + ε) * m ∧
      p - ε ≤ (candidateCylinderLaw s η).real
        {ω | ∃ i ∈ candidateRetainedIndices
            (fun ω i => harperCandidateLogOld ω X (t i)) b ρ ω,
          (M : ℝ) + b < |harperCandidateLogFresh ω X (t i)|}

/-- The high-probability interface is the special case `p = 1`. -/
theorem candidateLogCylinderScreenStatementWithMass_one (ρ : ℝ) :
    CandidateLogCylinderScreenStatementWithMass ρ 1 ↔
      CandidateLogCylinderScreenStatement ρ := Iff.rfl

/-- The cylinder deficit scales linearly with the universal crossing mass. -/
theorem candidate_conditionalEnvelope_gap_of_logScreens_with_mass
    {ρ p : ℝ} (hρ : ρ < 1) (h : CandidateLogCylinderScreenStatementWithMass ρ p)
    (M : ℕ) (s : Finset ℕ) (η : s → Bool) :
    (candidateCylinderLaw s η).real (candidateUpperEnvelope M) ≤
      1 - p * (1 - ρ) / (2 * (3 - ρ)) := by
  apply candidate_envelope_gap_of_approximate_screens_with_mass hρ
  intro ε hε
  obtain ⟨X, m, t, b, hm, hs, ht, hbudget, hcross⟩ := h M s η ε hε
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact candidate_measureReal_log_envelope_le_of_absolute_crossing
    X t (fun i => (ht i).1) (fun i => (ht i).2)
    (candidateCylinderLaw_gridFreshFlip s η X (fun i => ⌊Real.exp (t i)⌋₊) hs)
    M b ρ (p - ε)
    (2 * (1 - (candidateCylinderLaw s η).real (candidateUpperEnvelope M)) + ε)
    hρ (by simpa only [Fintype.card_fin] using hbudget) hcross

/-- Any uniform positive crossing mass closes the candidate probability
argument. No success-probability upper bound is needed as an extra premise. -/
theorem erdos1144_of_candidateLogCylinderScreenStatementWithMass
    {ρ p : ℝ} (hρ : ρ < 1) (hp : 0 < p)
    (h : CandidateLogCylinderScreenStatementWithMass ρ p) : Erdos1144 := by
  apply erdos1144_of_candidateConditionalEnvelopeGap
  intro M
  have hd : 0 < 1 - ρ := by linarith
  have he : 0 < 3 - ρ := by linarith
  let δ := p * (1 - ρ) / (2 * (3 - ρ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨min (1 / 2) δ, lt_min (by norm_num) hδ, ?_, ?_⟩
  · exact (min_le_left _ _).trans_lt (by norm_num)
  · intro s η
    have hg := candidate_conditionalEnvelope_gap_of_logScreens_with_mass hρ h M s η
    exact hg.trans (sub_le_sub_left (min_le_right _ _) 1)

end Erdos.Problem1144
