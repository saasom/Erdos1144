import Erdos.Problem1144.HarperCandidateGaussianVariance

open Finset

namespace Erdos.Problem1144

open Classical in
/-- Greedy deletion works inside any retained finite set. A bound of `d`
on each bad degree loses at most the exact factor `d+1`; the retained set
need not be chosen independently of the relation. -/
theorem candidate_exists_large_pairwise_subset {ι : Type*}
    (s : Finset ι) (R : ι → ι → Prop) (hR : Symmetric R) (d : ℕ)
    (hdegree : ∀ i ∈ s, (s.filter fun j => j ≠ i ∧ R i j).card ≤ d) :
    ∃ J : Finset ι, J ⊆ s ∧ (J : Set ι).Pairwise (fun i j => ¬ R i j) ∧
      s.card ≤ (d + 1) * J.card := by
  classical
  revert hdegree
  refine Finset.strongInductionOn s ?_
  intro s ih hdegree
  by_cases hs : s = ∅
  · subst s
    exact ⟨∅, Subset.rfl, by simp, by simp⟩
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hs
  let B := insert a (s.filter fun j => j ≠ a ∧ R a j)
  let rest := s \ B
  have hrest : rest ⊆ s := Finset.sdiff_subset
  have haRest : a ∉ rest := by simp [rest, B]
  have hproper : rest ⊂ s := Finset.ssubset_iff_subset_ne.mpr
    ⟨hrest, fun h => haRest (h.symm ▸ ha)⟩
  have hrestDegree (i : ι) (hi : i ∈ rest) :
      (rest.filter fun j => j ≠ i ∧ R i j).card ≤ d :=
    (Finset.card_le_card (Finset.filter_subset_filter _ hrest)).trans (hdegree i (hrest hi))
  obtain ⟨J, hJ, hpair, hcard⟩ := ih rest hproper hrestDegree
  have hnot (b : ι) (hb : b ∈ J) : b ≠ a ∧ ¬ R a b := by
    have hbRest := Finset.mem_sdiff.mp (hJ hb)
    have hba : b ≠ a := by
      intro h
      subst b
      exact hbRest.2 (Finset.mem_insert_self _ _)
    refine ⟨hba, ?_⟩
    intro hbad
    exact hbRest.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨hbRest.1, hba, hbad⟩))
  have haJ : a ∉ J := fun h => haRest (hJ h)
  refine ⟨insert a J, ?_, ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ha
    · exact hrest (hJ hi)
  · intro i hi j hj hij
    by_cases hia : i = a
    · subst i
      have hjJ : j ∈ J := (Finset.mem_insert.mp hj).resolve_left (Ne.symm hij)
      exact (hnot j hjJ).2
    · have hiJ : i ∈ J := (Finset.mem_insert.mp hi).resolve_left hia
      by_cases hja : j = a
      · subst j
        exact fun h => (hnot i hiJ).2 (hR h)
      · have hjJ : j ∈ J := (Finset.mem_insert.mp hj).resolve_left hja
        exact hpair hiJ hjJ hij
  · have hB : B.card ≤ d + 1 :=
      (Finset.card_insert_le a _).trans (Nat.add_le_add_right (hdegree a ha) 1)
    have hsCard : s.card ≤ rest.card + B.card := Finset.card_le_card_sdiff_add_card
    rw [Finset.card_insert_of_notMem haJ]
    nlinarith

open Classical in
/-- Apply the exact thinning bound to a symmetric covariance matrix.
The only input is the literal count of off-diagonal entries above the
chosen absolute covariance cutoff. -/
theorem candidate_exists_large_weakly_correlated_subset {ι : Type*}
    (s : Finset ι) (C : ι → ι → ℝ) (hC : ∀ i j, C i j = C j i)
    (r : ℝ) (d : ℕ)
    (hdegree : ∀ i ∈ s, (s.filter fun j => j ≠ i ∧ r < |C i j|).card ≤ d) :
    ∃ J : Finset ι, J ⊆ s ∧ (J : Set ι).Pairwise (fun i j => |C i j| ≤ r) ∧
      s.card ≤ (d + 1) * J.card := by
  obtain ⟨J, hJ, hpair, hcard⟩ := candidate_exists_large_pairwise_subset
    s (fun i j => r < |C i j|) (by intro i j h; simpa only [hC j i] using h) d hdegree
  exact ⟨J, hJ, fun _ hi _ hj hij => le_of_not_gt (hpair hi hj hij), hcard⟩

end Erdos.Problem1144
