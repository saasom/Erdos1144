import Mathlib.Algebra.BigOperators.Module
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

open Finset
open scoped BigOperators

namespace Erdos.Problem1144

/-- Integer coefficient of the gap between ordered positions `j` and
`j+1` in finite summation by parts. Only the first `j+1` signs occur. -/
def candidateSignedGapCoefficient (ε : ℕ → ℤ) (j : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (j + 1), ε i

/-- A sum of signs has the parity of its number of terms. No balance
assumption is needed, which also covers signs after reflecting heights. -/
theorem candidate_signedGapCoefficient_mod_two (ε : ℕ → ℤ) (j : ℕ)
    (hε : ∀ i < j + 1, ε i = 1 ∨ ε i = -1) :
    candidateSignedGapCoefficient ε j % 2 = ((j + 1 : ℕ) : ℤ) % 2 := by
  unfold candidateSignedGapCoefficient
  rw [Finset.sum_int_mod]
  have hsum : (∑ i ∈ Finset.range (j + 1), ε i % 2) =
      ∑ _i ∈ Finset.range (j + 1), (1 : ℤ) := by
    apply Finset.sum_congr rfl
    intro i hi
    rcases hε i (Finset.mem_range.mp hi) with h | h <;> norm_num [h]
  rw [hsum]
  simp

/-- Every odd-length sign prefix has a nonzero integer gap coefficient. -/
theorem candidate_signedGapCoefficient_even_index_ne_zero
    (ε : ℕ → ℤ) (r : ℕ) (hε : ∀ i < 2 * r + 1, ε i = 1 ∨ ε i = -1) :
    candidateSignedGapCoefficient ε (2 * r) ≠ 0 := by
  have h := candidate_signedGapCoefficient_mod_two ε (2 * r) hε
  intro hz
  rw [hz] at h
  norm_num [Int.add_emod, Int.mul_emod] at h

/-- Among the `2k-1` internal gaps of `2k` signs, at least `k` have
nonzero cumulative integer coefficient. The total sign may be nonzero. -/
theorem candidate_signedGapCoefficient_nonzero_card_ge
    (k : ℕ) (ε : ℕ → ℤ) (hε : ∀ i < 2 * k, ε i = 1 ∨ ε i = -1) :
    k ≤ ((Finset.range (2 * k - 1)).filter
      (fun j => candidateSignedGapCoefficient ε j ≠ 0)).card := by
  have hmap : Set.MapsTo (fun r : ℕ => 2 * r) (↑(Finset.range k))
      (↑((Finset.range (2 * k - 1)).filter
        (fun j => candidateSignedGapCoefficient ε j ≠ 0))) := by
    intro r hr
    have hrk := Finset.mem_range.mp hr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by change 2 * r < 2 * k - 1; omega), ?_⟩
    exact candidate_signedGapCoefficient_even_index_ne_zero ε r
      (fun i hi => hε i (by omega))
  have hcard := Finset.card_le_card_of_injOn (fun r : ℕ => 2 * r) hmap
    (by intro r hr s hs heq; change 2 * r = 2 * s at heq; omega)
  simpa only [Finset.card_range] using hcard

/-- At most `k-1` internal gaps have zero cumulative coefficient, including
the empty case `k=0`. This count is independent of total-sign balance. -/
theorem candidate_signedGapCoefficient_zero_card_le
    (k : ℕ) (ε : ℕ → ℤ) (hε : ∀ i < 2 * k, ε i = 1 ∨ ε i = -1) :
    ((Finset.range (2 * k - 1)).filter
      (fun j => candidateSignedGapCoefficient ε j = 0)).card ≤ k - 1 := by
  have hnonzero := candidate_signedGapCoefficient_nonzero_card_ge k ε hε
  have htotal := Finset.card_filter_add_card_filter_not
    (s := Finset.range (2 * k - 1)) (fun j => candidateSignedGapCoefficient ε j = 0)
  change ((Finset.range (2 * k - 1)).filter
      (fun j => candidateSignedGapCoefficient ε j = 0)).card +
    ((Finset.range (2 * k - 1)).filter
      (fun j => candidateSignedGapCoefficient ε j ≠ 0)).card = _ at htotal
  rw [Finset.card_range] at htotal
  omega

/-- For any chosen class of small/strong gaps, either it contains at least
`k` indices or some remaining internal gap has a nonzero integer resonance
coefficient. This is a proved counting dichotomy, not a hypothesis. -/
theorem candidate_signedGap_dichotomy
    (k : ℕ) (ε : ℕ → ℤ) (hε : ∀ i < 2 * k, ε i = 1 ∨ ε i = -1)
    (S : Finset ℕ) :
    k ≤ S.card ∨ ∃ j ∈ Finset.range (2 * k - 1), j ∉ S ∧
      candidateSignedGapCoefficient ε j ≠ 0 := by
  classical
  by_cases hS : k ≤ S.card
  · exact Or.inl hS
  · right
    by_contra h
    push_neg at h
    have hsub : ((Finset.range (2 * k - 1)).filter
        (fun j => candidateSignedGapCoefficient ε j ≠ 0)) ⊆ S := by
      intro j hj
      have hj' := Finset.mem_filter.mp hj
      by_contra hjS
      exact hj'.2 (h j hj'.1 hjS)
    have hcard := Finset.card_le_card hsub
    have hn := candidate_signedGapCoefficient_nonzero_card_ge k ε hε
    omega

/-- The literal ordered-height version: either at least `k` internal gaps
are at most `δ`, or a gap larger than `δ` has an integer coefficient of
absolute value at least one. Monotonicity of the heights is not required
for this algebraic dichotomy. -/
theorem candidate_signedGap_small_or_nonzero_large
    (k : ℕ) (ε : ℕ → ℤ) (hε : ∀ i < 2 * k, ε i = 1 ∨ ε i = -1)
    (t : ℕ → ℝ) (δ : ℝ) :
    k ≤ ((Finset.range (2 * k - 1)).filter
      (fun j => t (j + 1) - t j ≤ δ)).card ∨
    ∃ j ∈ Finset.range (2 * k - 1), δ < t (j + 1) - t j ∧
      (1 : ℤ) ≤ |candidateSignedGapCoefficient ε j| := by
  classical
  rcases candidate_signedGap_dichotomy k ε hε
      ((Finset.range (2 * k - 1)).filter (fun j => t (j + 1) - t j ≤ δ)) with h | h
  · exact Or.inl h
  · obtain ⟨j, hj, hjS, hc⟩ := h
    right
    exact ⟨j, hj, lt_of_not_ge (fun hgap => hjS (Finset.mem_filter.mpr ⟨hj, hgap⟩)),
      Int.one_le_abs hc⟩

/-- Exact finite summation by parts for signed heights. The total-sign
endpoint term is retained, so this identity remains valid after reflecting
negative heights and changing their effective signs. -/
theorem candidate_signedHeights_eq_endpoint_sub_gaps
    (n : ℕ) (ε : ℕ → ℤ) (t : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, (ε i : ℝ) * t i) =
      ((∑ i ∈ Finset.range n, ε i : ℤ) : ℝ) * t (n - 1) -
        ∑ j ∈ Finset.range (n - 1),
          (candidateSignedGapCoefficient ε j : ℝ) * (t (j + 1) - t j) := by
  have h := Finset.sum_range_by_parts t (fun i => (ε i : ℝ)) n
  simpa only [smul_eq_mul, ← Int.cast_sum, mul_comm, candidateSignedGapCoefficient] using h

/-- For balanced signs the endpoint term vanishes, leaving exactly the
integer linear combination of successive gaps used in the resonance cell. -/
theorem candidate_balanced_signedHeights_eq_neg_gaps
    (n : ℕ) (ε : ℕ → ℤ) (t : ℕ → ℝ)
    (hbalance : (∑ i ∈ Finset.range n, ε i) = 0) :
    (∑ i ∈ Finset.range n, (ε i : ℝ) * t i) =
      -∑ j ∈ Finset.range (n - 1),
        (candidateSignedGapCoefficient ε j : ℝ) * (t (j + 1) - t j) := by
  rw [candidate_signedHeights_eq_endpoint_sub_gaps, hbalance]
  simp

end Erdos.Problem1144
