import Erdos.Problem1144.HarperCandidateCovarianceMixedExponent
import Erdos.Problem1144.HarperCandidateCovariancePrimeTail

open Finset Set MeasureTheory
open scoped BigOperators

namespace Erdos.Problem1144

noncomputable section

/-- The actual removed prime prefixes, with the full root indexed by `none`. -/
def candidateMixedRootedCutoff {ι : Type*} (j : ι → ℕ) : Option ι → ℕ :=
  fun i => i.elim 0 (fun i => Problem520.harperBlockEndpoint (j i))

/-- Inverse logarithms of the removed prefixes. The root has weight one;
every pair containing it takes the weight of the other coordinate. -/
def candidateMixedRootedScale {ι : Type*} (j : ι → ℕ) : Option ι → ℝ :=
  fun i => i.elim 1 (fun i => Problem520.invLog (Problem520.harperBlockEndpoint (j i)))

private theorem endpoint_invLog_antitone :
    Antitone (fun j => Problem520.invLog (Problem520.harperBlockEndpoint j)) := by
  intro a b hab
  apply inv_anti₀
  · exact Real.log_pos (by exact_mod_cast
      (show 1 < Problem520.harperBlockEndpoint a from
        lt_of_lt_of_le (by norm_num) (Problem520.harperBlockEndpoint_ge_sixteen a)))
  · exact Real.log_le_log (by exact_mod_cast Problem520.harperBlockEndpoint_pos a)
      (by exact_mod_cast Problem520.monotone_harperBlockEndpoint hab)

private theorem rooted_pair_cutoff {ι : Type*} (j : ι → ℕ) (start : ℕ)
    (hj : ∀ i, start ≤ j i) (a b : Option ι) (hab : a ≠ b) :
    ∃ k : ℕ, start ≤ k ∧
      max 3 (max (candidateMixedRootedCutoff j a) (candidateMixedRootedCutoff j b)) =
        Problem520.harperBlockEndpoint k ∧
      Problem520.invLog (Problem520.harperBlockEndpoint k) =
        min (candidateMixedRootedScale j a) (candidateMixedRootedScale j b) := by
  cases a with
  | none =>
    cases b with
    | none => exact (hab rfl).elim
    | some b =>
      refine ⟨j b, hj b, ?_, ?_⟩
      · simp only [candidateMixedRootedCutoff, Option.elim_none, Option.elim_some,
          Nat.zero_max]
        exact max_eq_right (by have := Problem520.harperBlockEndpoint_ge_sixteen (j b); omega)
      · simp only [candidateMixedRootedScale, Option.elim_none, Option.elim_some]
        exact (min_eq_right (Problem520.invLog_harperBlockEndpoint_le_one (j b))).symm
  | some a =>
    cases b with
    | none =>
      refine ⟨j a, hj a, ?_, ?_⟩
      · simp only [candidateMixedRootedCutoff, Option.elim_none, Option.elim_some,
          Nat.max_zero]
        exact max_eq_right (by have := Problem520.harperBlockEndpoint_ge_sixteen (j a); omega)
      · simp only [candidateMixedRootedScale, Option.elim_none, Option.elim_some]
        exact (min_eq_left (Problem520.invLog_harperBlockEndpoint_le_one (j a))).symm
    | some b =>
      refine ⟨max (j a) (j b), (hj a).trans (le_max_left _ _), ?_, ?_⟩
      · simp only [candidateMixedRootedCutoff, Option.elim_some]
        rw [← Problem520.monotone_harperBlockEndpoint.map_max]
        exact max_eq_right (by
          have := Problem520.harperBlockEndpoint_ge_sixteen (max (j a) (j b)); omega)
      · simp only [candidateMixedRootedScale, Option.elim_some]
        exact endpoint_invLog_antitone.map_max

/-- The total strong-PNT remainder is bounded by the square of the number
of coordinates times the inverse square of the initial logarithmic cutoff. -/
theorem candidate_sum_rooted_pair_square_scales_le
    {ι : Type*} [Fintype ι] (start : ℕ) (j : ι → ℕ) (hj : ∀ i, start ≤ j i) :
    (∑ ab ∈ (Finset.univ : Finset (Option ι)).offDiag,
      min (candidateMixedRootedScale j ab.1) (candidateMixedRootedScale j ab.2) ^ 2) ≤
        (Fintype.card (Option ι) : ℝ) ^ 2 *
          Problem520.invLog (Problem520.harperBlockEndpoint start) ^ 2 := by
  classical
  let E := (Finset.univ : Finset (Option ι)).offDiag
  have hpoint (ab : Option ι × Option ι) (hab : ab ∈ E) :
      min (candidateMixedRootedScale j ab.1) (candidateMixedRootedScale j ab.2) ^ 2 ≤
        Problem520.invLog (Problem520.harperBlockEndpoint start) ^ 2 := by
    obtain ⟨k, hk, _, he⟩ := rooted_pair_cutoff j start hj ab.1 ab.2
      (Finset.mem_offDiag.mp hab).2.2
    rw [← he]
    exact pow_le_pow_left₀ (Problem520.invLog_harperBlockEndpoint_pos k).le
      (endpoint_invLog_antitone hk) 2
  calc
    _ ≤ ∑ _ab ∈ E, Problem520.invLog (Problem520.harperBlockEndpoint start) ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = (E.card : ℝ) * Problem520.invLog (Problem520.harperBlockEndpoint start) ^ 2 := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hcard : E.card ≤ (Fintype.card (Option ι)) ^ 2 := by
        calc
          E.card ≤ Fintype.card (Option ι × Option ι) := Finset.card_le_univ _
          _ = _ := by rw [Fintype.card_prod]; ring
      exact_mod_cast hcard

/-- The explicit residual prime exponent is eliminated. Only deterministic
height interactions remain, with the sharp logarithmic diagonal scale and
a square-inverse-log error for each pair. Constants are absolute and the
upper prime cutoff is arbitrary. -/
theorem candidate_exists_rooted_mixedEuler_residual_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ J : ℕ,
    ∀ {ι : Type} [Fintype ι], ∀ y start : ℕ, 3 ≤ y → J ≤ start →
    ∀ j : ι → ℕ, (∀ i, start ≤ j i) →
      (∀ i, Problem520.harperBlockEndpoint (j i) ≤ y) →
    ∀ t : Option ι → ℝ,
      (∀ a b, a ≠ b → t a - t b ≠ 0 ∧ t a + t b ≠ 0 ∧
        |t a - t b| ≤ candidateCovarianceHeightWindow start ∧
        |t a + t b| ≤ candidateCovarianceHeightWindow start) →
    let c := candidateMixedRootedCutoff j
    let ell := candidateMixedRootedScale j
    Real.exp (∑ p : Problem520.HarperPrimeIndex y,
      if 4 ≤ p.1 then candidateEulerMixedExponent p.1
        (Finset.univ.filter (fun i => c i < p.1)) t
      else (Finset.univ.filter (fun i => c i < p.1)).card * Real.log 4) ≤
      D ^ Fintype.card (Option ι) * (Real.log (y : ℝ) / Real.log 3) *
      (∏ i, Real.log (y : ℝ) / Real.log (Problem520.harperBlockEndpoint (j i) : ℝ)) *
      Real.exp ((4 * Real.log 4 + 8 / 3) * Fintype.card (Option ι) +
        ∑ ab ∈ (Finset.univ : Finset (Option ι)).offDiag,
          (4 * (min (ell ab.1) (ell ab.2) / |t ab.1 - t ab.2| +
            min (ell ab.1) (ell ab.2) / |t ab.1 + t ab.2|) +
          2 * C * min (ell ab.1) (ell ab.2) ^ 2)) := by
  classical
  obtain ⟨C, hC, J, htail⟩ := candidate_exists_growingHeight_primeTail_bound
  obtain ⟨D, hD, hdiag⟩ := candidate_exists_exp_freshReciprocalSum_le_log_ratio
  refine ⟨C, D, hC, hD, J, ?_⟩
  intro ι _ y start hy hstart j hj hjy t ht
  dsimp only
  let c := candidateMixedRootedCutoff j
  let ell := candidateMixedRootedScale j
  let E := (Finset.univ : Finset (Option ι)).offDiag
  have hpairs :
      (∑ ab ∈ E,
        ∑ p ∈ (Finset.Ioc (max 3 (max (c ab.1) (c ab.2))) y).filter Nat.Prime,
          (Real.cos ((t ab.1 - t ab.2) * Real.log (p : ℝ)) +
            Real.cos ((t ab.1 + t ab.2) * Real.log (p : ℝ))) / p) ≤
      ∑ ab ∈ E, (4 * (min (ell ab.1) (ell ab.2) / |t ab.1 - t ab.2| +
        min (ell ab.1) (ell ab.2) / |t ab.1 + t ab.2|) +
          2 * C * min (ell ab.1) (ell ab.2) ^ 2) := by
    apply Finset.sum_le_sum
    intro ab hab
    have hne := (Finset.mem_offDiag.mp hab).2.2
    obtain ⟨k, hsk, hk, hell⟩ := rooted_pair_cutoff j start hj ab.1 ab.2 hne
    have hky : Problem520.harperBlockEndpoint k ≤ y := by
      rw [← hk]
      apply max_le hy
      apply max_le
      · cases ab.1 <;> simp [candidateMixedRootedCutoff, hjy]
      · cases ab.2 <;> simp [candidateMixedRootedCutoff, hjy]
    obtain ⟨hd, hs, hwd, hws⟩ := ht ab.1 ab.2 hne
    have hwindow := candidateCovarianceHeightWindow_monotone hsk
    have hd' := htail k y (hstart.trans hsk) hky (t ab.1 - t ab.2) hd (hwd.trans hwindow)
    have hs' := htail k y (hstart.trans hsk) hky (t ab.1 + t ab.2) hs (hws.trans hwindow)
    rw [hell] at hd' hs'
    dsimp only [c]
    rw [hk]
    simp only [add_div, Finset.sum_add_distrib]
    have hle := add_le_add (le_abs_self _ |>.trans hd') (le_abs_self _ |>.trans hs')
    dsimp only [ell]
    convert hle using 1 <;> ring
  have hmain := candidate_allPrime_mixedExponent_le_prime_tails y c t
  have hexp : Real.exp (∑ p : Problem520.HarperPrimeIndex y,
      if 4 ≤ p.1 then candidateEulerMixedExponent p.1 (univ.filter (fun i => c i < p.1)) t
      else (univ.filter (fun i => c i < p.1)).card * Real.log 4) ≤
      Real.exp ((∑ i, Problem520.freshReciprocalSum (max 3 (c i)) y) +
        ((4 * Real.log 4 + 8 / 3) * Fintype.card (Option ι) +
          ∑ ab ∈ E, (4 * (min (ell ab.1) (ell ab.2) / |t ab.1 - t ab.2| +
            min (ell ab.1) (ell ab.2) / |t ab.1 + t ab.2|) +
              2 * C * min (ell ab.1) (ell ab.2) ^ 2))) := by
    apply Real.exp_le_exp.mpr
    dsimp only [E] at hpairs
    linarith
  have hprod : (∏ i : Option ι, Real.exp (Problem520.freshReciprocalSum (max 3 (c i)) y)) ≤
      D ^ Fintype.card (Option ι) * (Real.log (y : ℝ) / Real.log 3) *
        ∏ i, Real.log (y : ℝ) / Real.log (Problem520.harperBlockEndpoint (j i) : ℝ) := by
    have h := Finset.prod_le_prod (s := (univ : Finset (Option ι)))
      (fun i _ => (Real.exp_pos _).le)
      (fun i _ => hdiag (max 3 (c i)) y (by omega) (by
        apply max_le hy
        cases i <;> simp [c, candidateMixedRootedCutoff, hjy]))
    have hrw : (∏ i : Option ι, D * (Real.log (y : ℝ) / Real.log (max 3 (c i) : ℕ))) =
        D ^ Fintype.card (Option ι) * (Real.log (y : ℝ) / Real.log 3) *
          ∏ i, Real.log (y : ℝ) / Real.log (Problem520.harperBlockEndpoint (j i) : ℝ) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.prod_option]
      simp only [c, candidateMixedRootedCutoff, Option.elim_none, Option.elim_some, Nat.max_zero]
      have hmax (i : ι) : max 3 (Problem520.harperBlockEndpoint (j i)) =
          Problem520.harperBlockEndpoint (j i) := max_eq_right (by
        have := Problem520.harperBlockEndpoint_ge_sixteen (j i); omega)
      simp only [hmax, Nat.cast_ofNat]
      ring
    exact h.trans_eq hrw
  rw [Real.exp_add] at hexp
  apply hexp.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rwa [Real.exp_sum]

/-- D-star and the selected strong screen give the two actual prefix caps.
Unselected cutoffs retain the ordinary `W^6` bound. -/
theorem candidate_DStar_strongScreen_mixed_prefix_caps
    {ι : Type*} (start N : ℕ) (W : ℝ) (s : Finset ℕ)
    (j : ι → ℕ) (hj : ∀ i, j i ≤ N) (t : ι → ℝ) (ω : Problem520.Omega)
    (hg : ∀ i, ω ∈ candidateCovarianceDStarEvent start N (t i) W ∩
      candidateCovarianceStrongScreenEvent start (t i) W s) :
    ∀ i, Problem520.harperEulerDensity (Problem520.harperBlockEndpoint (start + j i)) ω (t i) ≤
      (if j i ∈ s then
        Real.log (Problem520.harperBlockEndpoint (start + j i) : ℝ) / W ^ 1000
      else Real.log (Problem520.harperBlockEndpoint (start + j i) : ℝ) * W ^ 6) ^ 2 := by
  intro i
  have hsq := Real.sq_sqrt (Problem520.harperEulerDensity_nonneg
    (Problem520.harperBlockEndpoint (start + j i)) ω (t i))
  have h0 := Real.sqrt_nonneg (Problem520.harperEulerDensity
    (Problem520.harperBlockEndpoint (start + j i)) ω (t i))
  split_ifs with his
  · have h := (hg i).2 (j i) his
    nlinarith
  · have h := ((hg i).1 (⟨j i, by have := hj i; omega⟩ : Fin (N + 1))).2
    change Real.sqrt (Problem520.harperEulerDensity
      (Problem520.harperBlockEndpoint (start + j i)) ω (t i)) ≤ _ at h
    nlinarith

/-- The literal rooted mixed expectation with arbitrary nonnegative prefix
caps. All probabilistic and prime-sum inputs are proved: the remaining
right side contains only the deterministic height interactions. This
accepts both the D-star caps and the selected stronger caps. -/
theorem candidate_exists_rooted_prefixBarrier_mixedEuler_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ J : ℕ,
    ∀ {ι : Type} [Fintype ι], ∀ y start : ℕ, 3 ≤ y → J ≤ start →
    ∀ j : ι → ℕ, (∀ i, start ≤ j i) →
      (∀ i, Problem520.harperBlockEndpoint (j i) ≤ y) →
    ∀ t : Option ι → ℝ,
      (∀ a b, a ≠ b → t a - t b ≠ 0 ∧ t a + t b ≠ 0 ∧
        |t a - t b| ≤ candidateCovarianceHeightWindow start ∧
        |t a + t b| ≤ candidateCovarianceHeightWindow start) →
    ∀ A : ι → ℝ, (∀ i, 0 ≤ A i) →
    let ell := candidateMixedRootedScale j
    (∫ ω, {ω | ∀ i : ι, Problem520.harperEulerDensity
      (Problem520.harperBlockEndpoint (j i)) ω (t (some i)) ≤ A i}.indicator
        (fun ω => ∏ i : Option ι, Problem520.harperEulerDensity y ω (t i)) ω ∂Problem520.μ) ≤
      (∏ i, A i) * (D ^ Fintype.card (Option ι) * (Real.log (y : ℝ) / Real.log 3) *
      (∏ i, Real.log (y : ℝ) / Real.log (Problem520.harperBlockEndpoint (j i) : ℝ)) *
      Real.exp ((4 * Real.log 4 + 8 / 3) * Fintype.card (Option ι) +
        ∑ ab ∈ (Finset.univ : Finset (Option ι)).offDiag,
          (4 * (min (ell ab.1) (ell ab.2) / |t ab.1 - t ab.2| +
            min (ell ab.1) (ell ab.2) / |t ab.1 + t ab.2|) +
          2 * C * min (ell ab.1) (ell ab.2) ^ 2))) := by
  classical
  obtain ⟨C, D, hC, hD, J, hres⟩ := candidate_exists_rooted_mixedEuler_residual_bound
  refine ⟨C, D, hC, hD, J, ?_⟩
  intro ι _ y start hy hstart j hj hjy t ht A hA
  dsimp only
  let c := candidateMixedRootedCutoff j
  let B : Option ι → ℝ := fun i => i.elim 1 A
  have hcy : ∀ i, c i ≤ y := by
    intro i
    cases i <;> simp [c, candidateMixedRootedCutoff, hjy]
  have hB : ∀ i, 0 ≤ B i := by intro i; cases i <;> simp [B, hA]
  have hraw := candidate_integral_prefixBarrier_mixedEuler_le y c hcy t B hB
  have hprod : (∏ i : Option ι, B i) = ∏ i : ι, A i := by
    rw [Fintype.prod_option]
    simp [B]
  have hE : {ω | ∀ i : Option ι, Problem520.harperEulerDensity (c i) ω (t i) ≤ B i} =
      {ω | ∀ i : ι, Problem520.harperEulerDensity
        (Problem520.harperBlockEndpoint (j i)) ω (t (some i)) ≤ A i} := by
    ext ω
    constructor
    · intro h i
      exact h (some i)
    · intro h i
      cases i with
      | none =>
        have hp : Nat.primesBelow 1 = ∅ := by decide
        simp [c, B, candidateMixedRootedCutoff, Problem520.harperEulerDensity, hp]
      | some i => exact h i
  rw [hE, hprod] at hraw
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (hres y start hy hstart j hj hjy t ht) (Finset.prod_nonneg fun i _ => hA i))

end

end Erdos.Problem1144
