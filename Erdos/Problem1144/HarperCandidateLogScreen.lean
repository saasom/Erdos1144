import Erdos.Problem1144.HarperCandidateCylinderScreen
import Erdos.Problem1144.HarperCandidateLogProcess

open MeasureTheory
open scoped BigOperators

namespace Erdos.Problem1144

/-!
# The candidate's literal log-time cylinder screen

Both the old selector and the fresh crossing use `exp(t / 2)` normalization.
The deterministic floor correction is retained in every finite-grid field;
no comparison at a randomly selected endpoint is needed.
-/

/-- The old contribution with the candidate's literal logarithmic normalization. -/
noncomputable def harperCandidateLogOld (ω : Omega) (X : ℕ) (t : ℝ) : ℝ :=
  smoothProcess ω X ⌊Real.exp t⌋₊ * harperCandidateLogNormalization t

/-- The fresh contribution with the candidate's literal logarithmic normalization. -/
noncomputable def harperCandidateLogFresh (ω : Omega) (X : ℕ) (t : ℝ) : ℝ :=
  largePrimeProcess ω X ⌊Real.exp t⌋₊ * harperCandidateLogNormalization t

/-- The finite-grid fields split the candidate's exact real-time process. -/
theorem harperCandidateLogProcess_eq_logOld_add_logFresh
    (ω : Omega) {X : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcut : ⌊Real.exp t⌋₊ < X ^ 2) :
    harperCandidateLogProcess ω t =
      harperCandidateLogOld ω X t + harperCandidateLogFresh ω X t := by
  rw [harperCandidateLogProcess_eq_cutoffNormSum_mul ω ht,
    cutoffNormSum_eq_smoothProcess_add_largePrimeProcess ω hcut, add_mul]
  rfl

theorem measurable_harperCandidateLogOld (X : ℕ) (t : ℝ) :
    Measurable fun ω => harperCandidateLogOld ω X t :=
  (measurable_smoothProcess X ⌊Real.exp t⌋₊).mul_const _

theorem measurable_harperCandidateLogFresh (X : ℕ) (t : ℝ) :
    Measurable fun ω => harperCandidateLogFresh ω X t :=
  (measurable_largePrimeProcess X ⌊Real.exp t⌋₊).mul_const _

/-- Joint measurability permits averaging old-negative probabilities over
deterministic blocks and shifts. -/
theorem measurable_harperCandidateLogOld_joint (X : ℕ) :
    Measurable fun z : Omega × ℝ => harperCandidateLogOld z.1 X z.2 := by
  have hA : Measurable fun z : Omega × ℕ => smoothProcess z.1 X z.2 :=
    measurable_from_prod_countable_left (measurable_smoothProcess X)
  exact (hA.comp (measurable_fst.prodMk
    (Real.measurable_exp.comp measurable_snd).nat_floor)).mul
    (measurable_harperCandidateLogNormalization.comp measurable_snd)

/-- Joint measurability of the literal fresh field, including the changing
integer cutoff. -/
theorem measurable_harperCandidateLogFresh_joint (X : ℕ) :
    Measurable fun z : Omega × ℝ => harperCandidateLogFresh z.1 X z.2 := by
  have hZ : Measurable fun z : Omega × ℕ => largePrimeProcess z.1 X z.2 :=
    measurable_from_prod_countable_left (measurable_largePrimeProcess X)
  exact (hZ.comp (measurable_fst.prodMk
    (Real.measurable_exp.comp measurable_snd).nat_floor)).mul
    (measurable_harperCandidateLogNormalization.comp measurable_snd)

/-- The deterministic normalization leaves the old field fixed by a common
fresh flip across all grid coordinates. -/
theorem harperCandidateLogOld_gridFreshFlip
    {ι : Type*} [Fintype ι] (X : ℕ) (t : ι → ℝ) (ω : Omega) (i : ι) :
    harperCandidateLogOld
      (freshSignFlip (candidateGridFreshPrimes X (fun i => ⌊Real.exp (t i)⌋₊)) ω) X (t i) =
      harperCandidateLogOld ω X (t i) := by
  unfold harperCandidateLogOld
  rw [smoothProcess_freshSignFlip_eq_of_above _ ω X _
    (candidateGridFreshPrimes_above X (fun i => ⌊Real.exp (t i)⌋₊))]

/-- The same common flip negates every literal log-time fresh coordinate. -/
theorem harperCandidateLogFresh_gridFreshFlip
    {ι : Type*} [Fintype ι] (X : ℕ) (t : ι → ℝ)
    (hcut : ∀ i, ⌊Real.exp (t i)⌋₊ < X ^ 2) (ω : Omega) (i : ι) :
    harperCandidateLogFresh
      (freshSignFlip (candidateGridFreshPrimes X (fun i => ⌊Real.exp (t i)⌋₊)) ω) X (t i) =
      -harperCandidateLogFresh ω X (t i) := by
  unfold harperCandidateLogFresh
  rw [largePrimeProcess_candidateGridFreshFlip_eq_neg X _ hcut ω i, neg_mul]

/-- Literal log-time finite-screen exclusion, under any probability law
preserved by the common fresh flip. A natural endpoint upper envelope bounds
all the real log-time endpoints because its height is nonnegative. -/
theorem candidate_measureReal_log_envelope_le_of_absolute_crossing
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {ν : Measure Omega} [IsProbabilityMeasure ν]
    (X : ℕ) (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i)
    (hcut : ∀ i, ⌊Real.exp (t i)⌋₊ < X ^ 2)
    (hν : MeasurePreserving
      (freshSignFlip (candidateGridFreshPrimes X (fun i => ⌊Real.exp (t i)⌋₊))) ν ν)
    (M : ℕ) (b ρ p B : ℝ) (hρ : ρ < 1)
    (hbudget : (∑ i, ν.real {ω | harperCandidateLogOld ω X (t i) < -b}) ≤
      B * Fintype.card ι)
    (hcross : p ≤ ν.real {ω | ∃ i ∈ candidateRetainedIndices
      (fun ω i => harperCandidateLogOld ω X (t i)) b ρ ω,
      (M : ℝ) + b < |harperCandidateLogFresh ω X (t i)|}) :
    ν.real (candidateUpperEnvelope M) ≤ 1 - p / 2 + B / (1 - ρ) := by
  apply candidate_measureReal_envelope_le_of_absolute_crossing
    (fun ω i => harperCandidateLogOld ω X (t i))
    (fun ω i => harperCandidateLogFresh ω X (t i))
    (fun i => measurable_harperCandidateLogOld X (t i))
    _ hν (harperCandidateLogOld_gridFreshFlip X t)
    (harperCandidateLogFresh_gridFreshFlip X t hcut)
    M b ρ p B hρ hbudget hcross (measurableSet_candidateUpperEnvelope M)
  intro ω hω i
  rw [← harperCandidateLogProcess_eq_logOld_add_logFresh ω (ht i) (hcut i)]
  exact harperCandidateLogProcess_le_of_normSum_le ω (Nat.cast_nonneg M) hω (t i)

/-- The two remaining finite-scale analytic inputs, stated directly on the
candidate's real log-time grids and exponential denominator. Each fixed
cylinder, envelope height and accuracy may choose its own grid and threshold. -/
def CandidateLogCylinderScreenStatement (ρ : ℝ) : Prop :=
  ∀ (M : ℕ) (s : Finset ℕ) (η : s → Bool) (ε : ℝ), 0 < ε →
    ∃ (X m : ℕ) (t : Fin m → ℝ) (b : ℝ),
      0 < m ∧ (∀ p ∈ s, p ≤ X) ∧
      (∀ i, 0 ≤ t i ∧ ⌊Real.exp (t i)⌋₊ < X ^ 2) ∧
      (∑ i, (candidateCylinderLaw s η).real
          {ω | harperCandidateLogOld ω X (t i) < -b}) ≤
        (2 * (1 - (candidateCylinderLaw s η).real (candidateUpperEnvelope M)) + ε) * m ∧
      1 - ε ≤ (candidateCylinderLaw s η).real
        {ω | ∃ i ∈ candidateRetainedIndices
            (fun ω i => harperCandidateLogOld ω X (t i)) b ρ ω,
          (M : ℝ) + b < |harperCandidateLogFresh ω X (t i)|}

/-- The literal log-time analytic statement gives the exact cylinder envelope
deficit, with no unproved floor or normalization adapter. -/
theorem candidate_conditionalEnvelope_gap_of_logScreens
    {ρ : ℝ} (hρ : ρ < 1) (h : CandidateLogCylinderScreenStatement ρ)
    (M : ℕ) (s : Finset ℕ) (η : s → Bool) :
    (candidateCylinderLaw s η).real (candidateUpperEnvelope M) ≤
      1 - (1 - ρ) / (2 * (3 - ρ)) := by
  apply candidate_envelope_gap_of_approximate_screens hρ
  intro ε hε
  obtain ⟨X, m, t, b, hm, hs, ht, hbudget, hcross⟩ := h M s η ε hε
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact candidate_measureReal_log_envelope_le_of_absolute_crossing
    X t (fun i => (ht i).1) (fun i => (ht i).2)
    (candidateCylinderLaw_gridFreshFlip s η X (fun i => ⌊Real.exp (t i)⌋₊) hs)
    M b ρ (1 - ε)
    (2 * (1 - (candidateCylinderLaw s η).real (candidateUpperEnvelope M)) + ε)
    hρ (by simpa only [Fintype.card_fin] using hbudget) hcross

/-- One-sided Erdős #1144 follows from the candidate's literal log-time
finite-scale analytic inputs. The unresolved analytic statement remains an
explicit argument, not an axiom or an instantiated final certificate. -/
theorem erdos1144_of_candidateLogCylinderScreenStatement
    {ρ : ℝ} (hρ : ρ < 1) (h : CandidateLogCylinderScreenStatement ρ) :
    Erdos1144 := by
  apply erdos1144_of_candidateConditionalEnvelopeGap
  intro M
  have hd : 0 < 1 - ρ := by linarith
  have he : 0 < 3 - ρ := by linarith
  refine ⟨(1 - ρ) / (2 * (3 - ρ)), by positivity, ?_, ?_⟩
  · apply (div_lt_one (by positivity : 0 < 2 * (3 - ρ))).mpr
    linarith
  · intro s η
    exact candidate_conditionalEnvelope_gap_of_logScreens hρ h M s η

end Erdos.Problem1144

#print axioms Erdos.Problem1144.harperCandidateLogProcess_eq_logOld_add_logFresh
#print axioms Erdos.Problem1144.measurable_harperCandidateLogOld_joint
#print axioms Erdos.Problem1144.measurable_harperCandidateLogFresh_joint
#print axioms Erdos.Problem1144.harperCandidateLogFresh_gridFreshFlip
#print axioms Erdos.Problem1144.candidate_measureReal_log_envelope_le_of_absolute_crossing
#print axioms Erdos.Problem1144.candidate_conditionalEnvelope_gap_of_logScreens
#print axioms Erdos.Problem1144.erdos1144_of_candidateLogCylinderScreenStatement
