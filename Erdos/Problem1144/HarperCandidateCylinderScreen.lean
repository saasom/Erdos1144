import Erdos.Problem1144.HarperCandidateEnvelope
import Erdos.Problem1144.HarperCandidateScreen

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace Erdos.Problem1144

/-- A fixed assignment is unchanged by flips outside its coordinate set. -/
theorem candidateCylinder_freshSignFlip_preimage
    (s t : Finset ℕ) (η : s → Bool) (hst : Disjoint s t) :
    freshSignFlip t ⁻¹' candidateCylinder s η = candidateCylinder s η := by
  have hrestrict (ω : Omega) : s.restrict (freshSignFlip t ω) = s.restrict ω := by
    funext p
    have hp : (p : ℕ) ∉ t := fun ht => Finset.disjoint_left.mp hst p.property ht
    simp only [Finset.restrict_def, freshSignFlip, if_neg hp]
  ext ω
  change s.restrict (freshSignFlip t ω) ∈ ({η} : Set (s → Bool)) ↔
    s.restrict ω ∈ ({η} : Set (s → Bool))
  rw [hrestrict]

/-- Fresh flips preserve the normalized law of every disjoint assignment. -/
theorem candidateCylinderLaw_freshSignFlip
    (s t : Finset ℕ) (η : s → Bool) (hst : Disjoint s t) :
    MeasurePreserving (freshSignFlip t) (candidateCylinderLaw s η)
      (candidateCylinderLaw s η) := by
  have h := candidate_measurePreserving_restrict_of_invariant
    (measurePreserving_freshSignFlip t) (measurableSet_candidateCylinder s η)
    (candidateCylinder_freshSignFlip_preimage s t η hst)
  refine ⟨measurable_freshSignFlip t, ?_⟩
  unfold candidateCylinderLaw ProbabilityTheory.cond
  rw [Measure.map_smul, h.map_eq]

/-- Once the old cutoff contains a fixed assignment, the common grid flip
preserves its conditional law. No fresh coordinate is included in conditioning. -/
theorem candidateCylinderLaw_gridFreshFlip
    {ι : Type*} [Fintype ι] (s : Finset ℕ) (η : s → Bool)
    (X : ℕ) (N : ι → ℕ) (hs : ∀ p ∈ s, p ≤ X) :
    MeasurePreserving (freshSignFlip (candidateGridFreshPrimes X N))
      (candidateCylinderLaw s η) (candidateCylinderLaw s η) := by
  apply candidateCylinderLaw_freshSignFlip
  apply Finset.disjoint_left.mpr
  intro p hp ht
  exact (not_lt_of_ge (hs p hp)) (candidateGridFreshPrimes_above X N p ht)

theorem candidateUpperEnvelope_cutoff_le
    {ω : Omega} {M : ℝ} (hω : ω ∈ candidateUpperEnvelope M)
    {N : ℕ} (hN : 0 < N) : cutoffNormSum ω N ≤ M := by
  have h := hω (N - 1)
  rw [normSum_eq_cutoffNormSum_succ, Nat.sub_add_cancel hN] at h
  exact h

/-- The candidate's probability algebra, with arbitrary approximation error.
The deficit is derived from the reflection factor and the old-tail factor 2. -/
theorem candidate_envelope_gap_of_approximate_screens
    {q ρ : ℝ} (hρ : ρ < 1)
    (h : ∀ ε : ℝ, 0 < ε →
      q ≤ 1 - (1 - ε) / 2 + (2 * (1 - q) + ε) / (1 - ρ)) :
    q ≤ 1 - (1 - ρ) / (2 * (3 - ρ)) := by
  have hd : 0 < 1 - ρ := by linarith
  have he : 0 < 3 - ρ := by linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  have hs := h (2 * ε) (by positivity)
  have hs' : (q - 1 + (1 - 2 * ε) / 2) * (1 - ρ) ≤
      2 * (1 - q) + 2 * ε := by
    apply (le_div_iff₀ hd).mp
    linarith
  have ht : (1 - (1 - ρ) / (2 * (3 - ρ)) + ε) * (3 - ρ) =
      (5 - ρ) / 2 + ε * (3 - ρ) := by
    field_simp
    ring
  apply (mul_le_mul_iff_left₀ he).mp
  rw [ht]
  nlinarith

/-- The two finite-scale inputs left by the candidate's analytic argument.
Each fixed cylinder and upper-envelope height may choose its own grids. The
old-negative average is controlled by twice the envelope-failure probability,
and the selected absolute fresh crossing has probability arbitrarily close
to one. All constants and errors are visible in the statement. -/
def CandidateFiniteCylinderScreenStatement (ρ : ℝ) : Prop :=
  ∀ (M : ℕ) (s : Finset ℕ) (η : s → Bool) (ε : ℝ), 0 < ε →
    ∃ (X m : ℕ) (N : Fin m → ℕ) (b : ℝ),
      0 < m ∧ (∀ p ∈ s, p ≤ X) ∧
      (∀ i, 0 < N i ∧ N i < X ^ 2) ∧
      (∑ i, (candidateCylinderLaw s η).real
          {ω | smoothProcess ω X (N i) < -b}) ≤
        (2 * (1 - (candidateCylinderLaw s η).real (candidateUpperEnvelope M)) + ε) * m ∧
      1 - ε ≤ (candidateCylinderLaw s η).real
        {ω | ∃ i ∈ candidateRetainedIndices
            (fun ω i => smoothProcess ω X (N i)) b ρ ω,
          (M : ℝ) + b < |largePrimeProcess ω X (N i)|}

/-- The full fixed-cylinder probability conclusion of the candidate, with
the analytic crossing and averaged old-tail inputs still explicit. -/
theorem candidate_conditionalEnvelope_gap_of_finiteScreens
    {ρ : ℝ} (hρ : ρ < 1) (h : CandidateFiniteCylinderScreenStatement ρ)
    (M : ℕ) (s : Finset ℕ) (η : s → Bool) :
    (candidateCylinderLaw s η).real (candidateUpperEnvelope M) ≤
      1 - (1 - ρ) / (2 * (3 - ρ)) := by
  apply candidate_envelope_gap_of_approximate_screens hρ
  intro ε hε
  obtain ⟨X, m, N, b, hm, hs, hN, hbudget, hcross⟩ := h M s η ε hε
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  apply candidate_measureReal_complete_envelope_le_of_absolute_crossing
    X N (fun i => (hN i).2) (candidateCylinderLaw_gridFreshFlip s η X N hs)
    M b ρ (1 - ε)
    (2 * (1 - (candidateCylinderLaw s η).real (candidateUpperEnvelope M)) + ε)
    hρ (by simpa only [Fintype.card_fin] using hbudget) hcross
    (measurableSet_candidateUpperEnvelope M)
  intro ω hω i
  exact candidateUpperEnvelope_cutoff_le hω (hN i).1

/-- Faithful one-sided #1144 closure from the candidate's finite-scale
analytic inputs. There is no analytic axiom in this theorem: the unresolved
statement is an explicit argument. -/
theorem erdos1144_of_candidateFiniteCylinderScreenStatement
    {ρ : ℝ} (hρ : ρ < 1) (h : CandidateFiniteCylinderScreenStatement ρ) :
    Erdos1144 := by
  apply erdos1144_of_candidateConditionalEnvelopeGap
  intro M
  have hd : 0 < 1 - ρ := by linarith
  have he : 0 < 3 - ρ := by linarith
  refine ⟨(1 - ρ) / (2 * (3 - ρ)), by positivity, ?_, ?_⟩
  · apply (div_lt_one (by positivity : 0 < 2 * (3 - ρ))).mpr
    linarith
  · intro s η
    exact candidate_conditionalEnvelope_gap_of_finiteScreens hρ h M s η

end Erdos.Problem1144
