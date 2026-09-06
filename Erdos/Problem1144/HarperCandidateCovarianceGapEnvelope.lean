import Erdos.Problem1144.HarperCandidateCovarianceMixedSurvivorMoment

open Finset Set MeasureTheory
open scoped BigOperators Classical

namespace Erdos.Problem1144

noncomputable section

/-- The first allowed prefix fitting the gap, stopped at the full Euler
cutoff. Microscopic gaps therefore remove the entire Euler factor. -/
def candidateCovarianceGapCutoff (start stop : ℕ) (g : ℝ) : ℕ :=
  start + Nat.find (show ∃ n : ℕ, stop ≤ start + n ∨
    Problem520.invLog (Problem520.harperBlockEndpoint (start + n)) ≤ g from
      ⟨stop, Or.inl (Nat.le_add_left stop start)⟩)

/-- A bounded reciprocal-gap envelope, clipped at both the initial and
full logarithmic Euler cutoffs. -/
def candidateCovarianceGapEnvelope (start stop : ℕ) (g : ℝ) : ℝ :=
  min (Real.log (Problem520.harperBlockEndpoint stop : ℝ))
    (max (Real.log (Problem520.harperBlockEndpoint start : ℝ))
      (2 / max g (Problem520.invLog (Problem520.harperBlockEndpoint stop))))

private theorem endpoint_invLog_antitone :
    Antitone (fun j => Problem520.invLog (Problem520.harperBlockEndpoint j)) := by
  intro a b hab
  apply inv_anti₀
  · exact Real.log_pos (by exact_mod_cast
      (show 1 < Problem520.harperBlockEndpoint a from
        lt_of_lt_of_le (by norm_num) (Problem520.harperBlockEndpoint_ge_sixteen a)))
  · exact Real.log_le_log (by exact_mod_cast Problem520.harperBlockEndpoint_pos a)
      (by exact_mod_cast Problem520.monotone_harperBlockEndpoint hab)

/-- Exact cutoff geometry. Only surviving prefixes require the gap to
dominate their inverse logarithm; rounding costs at most two away from
the initial clipping endpoint. -/
theorem candidate_covarianceGapCutoff_spec (start stop : ℕ) (hss : start ≤ stop) (g : ℝ) :
    let j := candidateCovarianceGapCutoff start stop g
    start ≤ j ∧ j ≤ stop ∧
      (j < stop → Problem520.invLog (Problem520.harperBlockEndpoint j) ≤ g) ∧
      (j = start ∨ g < 2 * Problem520.invLog (Problem520.harperBlockEndpoint j)) := by
  let h : ∃ n : ℕ, stop ≤ start + n ∨
      Problem520.invLog (Problem520.harperBlockEndpoint (start + n)) ≤ g :=
    ⟨stop, Or.inl (Nat.le_add_left stop start)⟩
  let n := Nat.find h
  change start ≤ start + n ∧ start + n ≤ stop ∧
    (start + n < stop → Problem520.invLog (Problem520.harperBlockEndpoint (start + n)) ≤ g) ∧
    (start + n = start ∨ g < 2 * Problem520.invLog (Problem520.harperBlockEndpoint (start + n)))
  have hn : n ≤ stop - start := Nat.find_min' h (Or.inl (by omega))
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro hj
    exact (Nat.find_spec h).resolve_left (by omega)
  · by_cases hn0 : n = 0
    · exact Or.inl (by omega)
    · right
      have hprev : ¬(stop ≤ start + (n - 1) ∨
          Problem520.invLog (Problem520.harperBlockEndpoint (start + (n - 1))) ≤ g) :=
        Nat.find_min h (by dsimp only [n]; omega)
      have heq : start + n = start + (n - 1) + 1 := by omega
      have hg : g < Problem520.invLog (Problem520.harperBlockEndpoint (start + (n - 1))) :=
        lt_of_not_ge (fun hle => hprev (Or.inr hle))
      rw [heq, Problem520.invLog_harperBlockEndpoint_eq, pow_succ]
      rw [Problem520.invLog_harperBlockEndpoint_eq] at hg
      nlinarith

/-- Every gap smaller than the top inverse logarithm selects the full
prefix, so it creates no residual interaction. -/
theorem candidate_covarianceGapCutoff_eq_stop_of_microscopic
    (start stop : ℕ) (hss : start ≤ stop) (g : ℝ)
    (hg : g < Problem520.invLog (Problem520.harperBlockEndpoint stop)) :
    candidateCovarianceGapCutoff start stop g = stop := by
  obtain ⟨_, hj, hfit, _⟩ := candidate_covarianceGapCutoff_spec start stop hss g
  by_contra hne
  have hs := hfit (lt_of_le_of_ne hj hne)
  have hm := endpoint_invLog_antitone hj
  linarith

/-- Rounding the selected endpoint gives the explicit bounded
reciprocal-gap envelope, including microscopic and initially clipped gaps. -/
theorem candidate_log_gapCutoff_le_envelope
    (start stop : ℕ) (hss : start ≤ stop) (g : ℝ) :
    Real.log (Problem520.harperBlockEndpoint (candidateCovarianceGapCutoff start stop g) : ℝ) ≤
      candidateCovarianceGapEnvelope start stop g := by
  let j := candidateCovarianceGapCutoff start stop g
  obtain ⟨hstart, hstop, _, hround⟩ := candidate_covarianceGapCutoff_spec start stop hss g
  have hlogj : 0 < Real.log (Problem520.harperBlockEndpoint j : ℝ) :=
    lt_of_lt_of_le zero_lt_one (Problem520.one_le_log_harperBlockEndpoint j)
  have hlogstop : 0 < Real.log (Problem520.harperBlockEndpoint stop : ℝ) :=
    lt_of_lt_of_le zero_lt_one (Problem520.one_le_log_harperBlockEndpoint stop)
  have htop : Real.log (Problem520.harperBlockEndpoint j : ℝ) ≤
      Real.log (Problem520.harperBlockEndpoint stop : ℝ) :=
    Real.log_le_log (by exact_mod_cast Problem520.harperBlockEndpoint_pos j)
      (by exact_mod_cast Problem520.monotone_harperBlockEndpoint hstop)
  apply le_min htop
  by_cases hg : g < Problem520.invLog (Problem520.harperBlockEndpoint stop)
  · have hmax : max g (Problem520.invLog (Problem520.harperBlockEndpoint stop)) =
        Problem520.invLog (Problem520.harperBlockEndpoint stop) := max_eq_right hg.le
    apply le_trans htop
    apply le_trans _ (le_max_right _ _)
    rw [hmax, Problem520.invLog, div_inv_eq_mul]
    linarith
  · have hgs : Problem520.invLog (Problem520.harperBlockEndpoint stop) ≤ g := le_of_not_gt hg
    have hgpos : 0 < g := (Problem520.invLog_harperBlockEndpoint_pos stop).trans_le hgs
    rw [max_eq_left hgs]
    rcases hround with hj | hr
    · simpa only [j, hj] using le_max_left
        (Real.log (Problem520.harperBlockEndpoint start : ℝ)) (2 / g)
    · apply le_trans _ (le_max_right _ _)
      apply (le_div_iff₀ hgpos).mpr
      have hr' : g * Real.log (Problem520.harperBlockEndpoint j : ℝ) < 2 := by
        dsimp only [Problem520.invLog] at hr
        have hh := (lt_div_iff₀ hlogj).mp (show g < 2 /
          Real.log (Problem520.harperBlockEndpoint j : ℝ) by simpa only [div_eq_mul_inv] using hr)
        exact hh
      nlinarith

/-- A gap below the preceding inverse logarithm selects a prefix at or
above the prescribed strong-barrier start. -/
theorem candidate_covarianceGapCutoff_ge_of_gap_lt
    (start stop a : ℕ) (hsa : start < a) (has : a ≤ stop) (g : ℝ)
    (hg : g < Problem520.invLog (Problem520.harperBlockEndpoint (a - 1))) :
    a ≤ candidateCovarianceGapCutoff start stop g := by
  obtain ⟨_, hjstop, hfit, _⟩ := candidate_covarianceGapCutoff_spec start stop (by omega) g
  by_contra h
  have hj : candidateCovarianceGapCutoff start stop g ≤ a - 1 := by omega
  have hfit' := hfit (by omega)
  have hmono := endpoint_invLog_antitone hj
  linarith

/-- The gap envelope is a continuous nonnegative function; its reciprocal
has been cut off before zero, as required for the later gap integrals. -/
theorem candidate_continuous_gapEnvelope (start stop : ℕ) :
    Continuous (candidateCovarianceGapEnvelope start stop) := by
  apply continuous_const.min
  apply continuous_const.max
  apply continuous_const.div (continuous_id.max continuous_const)
  intro g
  exact ne_of_gt ((Problem520.invLog_harperBlockEndpoint_pos stop).trans_le (le_max_right _ _))

theorem candidate_gapEnvelope_nonneg (start stop : ℕ) (g : ℝ) :
    0 ≤ candidateCovarianceGapEnvelope start stop g := by
  apply le_min
  · exact (Problem520.one_le_log_harperBlockEndpoint stop).trans' (by norm_num)
  · exact (Problem520.one_le_log_harperBlockEndpoint start).trans' (by norm_num) |>.trans
      (le_max_left _ _)

/-- The envelope fits the `A+B/g` hypothesis of the weighted affine
resonance-slice theorem on every positive gap interval. -/
theorem candidate_gapEnvelope_le_initial_add_inv (start stop : ℕ) (g : ℝ) (hg : 0 < g) :
    candidateCovarianceGapEnvelope start stop g ≤
      Real.log (Problem520.harperBlockEndpoint start : ℝ) + 2 / g := by
  apply (min_le_right _ _).trans
  apply max_le
  · have hdiv : 0 ≤ (2 : ℝ) / g := by positivity
    linarith
  · have hdiv : (2 : ℝ) / max g (Problem520.invLog (Problem520.harperBlockEndpoint stop)) ≤
        2 / g := div_le_div_of_nonneg_left (by norm_num) hg (le_max_left _ _)
    have hlog : 0 ≤ Real.log (Problem520.harperBlockEndpoint start : ℝ) :=
      (Problem520.one_le_log_harperBlockEndpoint start).trans' (by norm_num)
    linarith

theorem candidate_gapEnvelope_le_top (start stop : ℕ) (g : ℝ) :
    candidateCovarianceGapEnvelope start stop g ≤ Real.log (Problem520.harperBlockEndpoint stop : ℝ) :=
  min_le_left _ _

end

end Erdos.Problem1144
