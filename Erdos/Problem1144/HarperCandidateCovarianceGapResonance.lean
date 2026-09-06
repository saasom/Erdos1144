import Erdos.Problem1144.HarperCandidateCovarianceGapCoordinates
import Erdos.Problem1144.HarperCandidateCovarianceResonanceGap
import Erdos.Problem1144.HarperCandidateCovarianceResonanceSliceCoordinate

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

private def finiteSignExtension {n : ℕ} (ε : Fin n → ℤ) (j : ℕ) : ℤ :=
  if h : j < n then ε ⟨j, h⟩ else 0

/-- Integer coefficients of the actual signed height sum in gap coordinates.
An internal gap receives minus its cumulative sign; the retained right
endpoint receives the total sign. No balance assumption is imposed. -/
def candidateGapCoefficients (n : ℕ) (ε : Fin (n + 1) → ℤ) (i : Fin (n + 1)) : ℤ :=
  if i = Fin.last n then ∑ j, ε j
  else -candidateSignedGapCoefficient (finiteSignExtension ε) i.val

theorem candidateGapCoefficients_apply_gap (n : ℕ) (ε : Fin (n + 1) → ℤ) (i : Fin n) :
    candidateGapCoefficients n ε i.castSucc =
      -candidateSignedGapCoefficient
        (fun j => if h : j < n + 1 then ε ⟨j, h⟩ else 0) i.val := by
  unfold candidateGapCoefficients
  rw [if_neg (Fin.castSucc_ne_last i)]
  rfl

theorem candidateGapCoefficients_apply_last (n : ℕ) (ε : Fin (n + 1) → ℤ) :
    candidateGapCoefficients n ε (Fin.last n) = ∑ j, ε j := by
  simp [candidateGapCoefficients]

/-- Exact finite-vector resonance formula after the measure-preserving gap
substitution. This connects reflected/permuted signs to the affine slices
of the actual product gap integral. -/
theorem candidate_signedHeights_eq_gapCoefficients (n : ℕ)
    (ε : Fin (n + 1) → ℤ) (t : Fin (n + 1) → ℝ) :
    (∑ i, (ε i : ℝ) * t i) =
      ∑ i, (candidateGapCoefficients n ε i : ℝ) * candidateGapCoordinates (n + 1) t i := by
  let E := finiteSignExtension ε
  let u : ℕ → ℝ := fun j => if h : j < n + 1 then t ⟨j, h⟩ else 0
  have hE (i : Fin (n + 1)) : E i.val = ε i := by
    dsimp only [E, finiteSignExtension]
    rw [dif_pos i.isLt]
  have hu (i : Fin (n + 1)) : u i.val = t i := by
    dsimp only [u]
    rw [dif_pos i.isLt]
  have hgap (j : Fin n) : u (j.val + 1) - u j.val = t j.succ - t j.castSucc := by
    change u j.succ.val - u j.castSucc.val = _
    rw [hu, hu]
  have h := candidate_signedHeights_eq_endpoint_sub_gaps (n + 1) E u
  simp only [Nat.add_sub_cancel] at h
  simp_rw [← Fin.sum_univ_eq_sum_range] at h
  have hmain : (∑ i, (ε i : ℝ) * t i) =
      ((∑ i, ε i : ℤ) : ℝ) * t (Fin.last n) -
        ∑ j : Fin n, (candidateSignedGapCoefficient E j.val : ℝ) *
          (t j.succ - t j.castSucc) := by
    simpa only [hgap, hE, hu, show u n = t (Fin.last n) from hu (Fin.last n)] using h
  rw [hmain]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp only [candidateGapCoefficients_apply_gap, candidateGapCoefficients_apply_last,
    candidateGapCoordinates_apply_gap, candidateGapCoordinates_apply_last,
    Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  change _ = -(∑ j : Fin n, (candidateSignedGapCoefficient E j.val : ℝ) *
    (t j.succ - t j.castSucc)) + ((∑ i, ε i : ℤ) : ℝ) * t (Fin.last n)
  ring

private theorem gapCoefficient_even_ne_zero (n : ℕ) (ε : Fin (n + 1) → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (r : ℕ) (hr : 2 * r < n) :
    candidateGapCoefficients n ε ⟨2 * r, by omega⟩ ≠ 0 := by
  have hi : (⟨2 * r, by omega⟩ : Fin (n + 1)) ≠ Fin.last n := by
    intro he
    have he' : 2 * r = n := congrArg Fin.val he
    omega
  unfold candidateGapCoefficients
  rw [if_neg hi]
  apply neg_ne_zero.mpr
  apply candidate_signedGapCoefficient_even_index_ne_zero
  intro i hi
  have hi' : i < n + 1 := by omega
  simpa only [finiteSignExtension, dif_pos hi'] using hε ⟨i, hi'⟩

/-- The actual finite gap coefficient vector has at least `k` nonzero
internal entries whenever there are at least `2k` signed heights. -/
theorem candidate_gapCoefficients_internal_nonzero_card_ge (n : ℕ)
    (ε : Fin (n + 1) → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (k : ℕ) (hk : 2 * k ≤ n + 1) :
    k ≤ (Finset.univ.filter (fun i : Fin (n + 1) =>
      i.val < n ∧ candidateGapCoefficients n ε i ≠ 0)).card := by
  let f : Fin k → Fin (n + 1) := fun r => ⟨2 * r.val, by have := r.isLt; omega⟩
  have hmap : Set.MapsTo f (↑(Finset.univ : Finset (Fin k)))
      (↑(Finset.univ.filter (fun i : Fin (n + 1) =>
        i.val < n ∧ candidateGapCoefficients n ε i ≠ 0))) := by
    intro r _
    have hr : 2 * r.val < n := by have := r.isLt; omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr, gapCoefficient_even_ne_zero n ε hε r.val hr⟩
  have hinj : Set.InjOn f (↑(Finset.univ : Finset (Fin k))) := by
    intro a _ b _ hab
    apply Fin.ext
    have he : 2 * a.val = 2 * b.val := congrArg Fin.val hab
    omega
  simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card_of_injOn f hmap hinj

/-- The literal gap coordinates admit the strict small-gap alternative
needed by the paid screen: either at least `k` gaps are below `δ`, or a
gap at least `δ` has a nonzero integer resonance coefficient. -/
theorem candidate_gapCoefficients_small_or_resonant_gap (n : ℕ)
    (ε : Fin (n + 1) → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (k : ℕ) (hk : 2 * k ≤ n + 1) (g : Fin (n + 1) → ℝ) (δ : ℝ) :
    k ≤ (Finset.univ.filter (fun i : Fin (n + 1) => i.val < n ∧ g i < δ)).card ∨
      ∃ i : Fin (n + 1), i.val < n ∧ δ ≤ g i ∧ 1 ≤ |candidateGapCoefficients n ε i| := by
  classical
  by_cases hs : k ≤ (Finset.univ.filter
      (fun i : Fin (n + 1) => i.val < n ∧ g i < δ)).card
  · exact Or.inl hs
  · right
    by_contra h
    have hsub : (Finset.univ.filter (fun i : Fin (n + 1) =>
        i.val < n ∧ candidateGapCoefficients n ε i ≠ 0)) ⊆
          Finset.univ.filter (fun i : Fin (n + 1) => i.val < n ∧ g i < δ) := by
      intro i hi
      obtain ⟨_, hi, hc⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, ?_⟩
      by_contra hg
      exact h ⟨i, hi, le_of_not_gt hg, Int.one_le_abs hc⟩
    exact hs ((candidate_gapCoefficients_internal_nonzero_card_ge n ε hε k hk).trans
      (Finset.card_le_card hsub))

/-- Weighted slice bound in the full integer linear-form notation furnished
by the actual gap transformation. The other gap and endpoint coordinates
retain their exact one-dimensional weighted integrals. -/
theorem candidate_integral_integerLinear_resonanceSlice_le
    {n : ℕ} (c : Fin (n + 1) → ℤ) (j : Fin (n + 1)) (hc : c j ≠ 0)
    {ε K : ℝ} (hε : 0 ≤ ε) (hK : 0 ≤ K) (m : ℤ)
    (lower upper : Fin (n + 1) → ℝ) (w : Fin (n + 1) → ℝ → ℝ)
    (hw : Measurable (w j))
    (hwi : ∀ i, IntegrableOn (w i) (Icc (lower i) (upper i)))
    (hwn : ∀ i x, x ∈ Icc (lower i) (upper i) → 0 ≤ w i x)
    (hwb : ∀ x ∈ Icc (lower j) (upper j), w j x ≤ K) :
    (∫ x, {x : Fin (n + 1) → ℝ | |(∑ i, (c i : ℝ) * x i) - (m : ℝ)| ≤ ε}.indicator
      (fun x => ∏ i, w i (x i)) x
        ∂Measure.pi (fun i => volume.restrict (Icc (lower i) (upper i)))) ≤
      ((2 * ε / |(c j : ℝ)|) * K) *
        ∏ i : Fin n, ∫ x in Icc (lower (j.succAbove i)) (upper (j.succAbove i)),
          w (j.succAbove i) x := by
  let b : (Fin n → ℝ) → ℝ := fun x => ∑ i, (c (j.succAbove i) : ℝ) * x i
  have hb : Measurable b := by unfold b; fun_prop
  have he (x : Fin (n + 1) → ℝ) :
      (∑ i, (c i : ℝ) * x i) = (c j : ℝ) * x j + b (j.removeNth x) := by
    rw [Fin.sum_univ_succAbove _ j]
    rfl
  have h := candidate_integral_coordinate_resonanceSlice_le j
    (by exact_mod_cast hc : (c j : ℝ) ≠ 0) hε hK b hb m lower upper w hw hwi hwn hwb
  simp_rw [← he] at h
  exact h

end Erdos.Problem1144
