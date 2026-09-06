import Erdos.Problem1144.HarperCandidateCovarianceMixedSpacing
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Intervals

open Finset
open scoped BigOperators Classical

namespace Erdos.Problem1144

private theorem sum_offDiag_eq_two_sum_lt {α : Type*} [LinearOrder α]
    (s : Finset α) (f : α → α → ℝ)
    (hsym : ∀ a ∈ s, ∀ b ∈ s, f a b = f b a) :
    (∑ ab ∈ s.offDiag, f ab.1 ab.2) =
      2 * ∑ a ∈ s, ∑ b ∈ s.filter (fun b => a < b), f a b := by
  classical
  have hoff : s.offDiag = (s ×ˢ s).filter (fun ab => ab.1 ≠ ab.2) := by
    ext ab
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product]
    tauto
  have hp (a : α) (ha : a ∈ s) (b : α) (hb : b ∈ s) :
      (if a ≠ b then f a b else 0) =
        (if a < b then f a b else 0) + (if b < a then f b a else 0) := by
    rcases lt_trichotomy a b with hab | hab | hab
    · simp [hab, hab.ne, not_lt_of_ge hab.le]
    · subst b; simp
    · simp [hab, hab.ne', not_lt_of_ge hab.le, hsym a ha b hb]
  rw [hoff, Finset.sum_filter, Finset.sum_product]
  calc
    _ = (∑ a ∈ s, ∑ b ∈ s, if a < b then f a b else 0) +
        ∑ a ∈ s, ∑ b ∈ s, if b < a then f b a else 0 := by
      simp_rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact hp a ha b hb
    _ = (∑ a ∈ s, ∑ b ∈ s, if a < b then f a b else 0) +
        ∑ b ∈ s, ∑ a ∈ s, if b < a then f b a else 0 := by
      congr 1
      exact Finset.sum_comm
    _ = _ := by simp only [Finset.sum_filter]; ring

private theorem sum_offDiag_range_eq_two_triangular (m : ℕ) (f : ℕ → ℕ → ℝ)
    (hsym : ∀ a < m, ∀ b < m, f a b = f b a) :
    (∑ ab ∈ (Finset.range m).offDiag, f ab.1 ab.2) =
      2 * ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range (m - i - 1), f i (i + j + 1) := by
  rw [sum_offDiag_eq_two_sum_lt _ f (by
    intro a ha b hb
    exact hsym a (Finset.mem_range.mp ha) b (Finset.mem_range.mp hb))]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hset : (Finset.range m).filter (fun j => i < j) = Finset.Ico (i + 1) m := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.sub_sub]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  omega

/-- The full ordered-pair interaction, including both Rademacher
frequencies, costs at most `8 m log(m+1)` on a common positive band. -/
theorem candidate_sum_offDiag_rademacher_interactions_le
    (w t : ℕ → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (ht : ∀ i, i < m → 0 ≤ t i)
    (hgap : ∀ i, i + 1 < m → w i ≤ t (i + 1) - t i) :
    (∑ ab ∈ (Finset.range m).offDiag,
      (min (w ab.1) (w ab.2) / |t ab.1 - t ab.2| +
        min (w ab.1) (w ab.2) / |t ab.1 + t ab.2|)) ≤
      8 * (m : ℝ) * Real.log ((m : ℝ) + 1) := by
  have hmono : StrictMonoOn t (Set.Iio m) := by
    apply strictMonoOn_of_lt_succ Set.ordConnected_Iio
    intro i _ hi hisucc
    change t i < t (i + 1)
    linarith [hgap i hisucc, hw i]
  rw [sum_offDiag_range_eq_two_triangular m
    (fun a b => min (w a) (w b) / |t a - t b| + min (w a) (w b) / |t a + t b|) (by
    intro a ha b hb
    simp only [min_comm (w a), abs_sub_comm (t a), add_comm (t a)])]
  have heq : (∑ i ∈ range m, ∑ j ∈ range (m - i - 1),
      (min (w i) (w (i + j + 1)) / |t i - t (i + j + 1)| +
        min (w i) (w (i + j + 1)) / |t i + t (i + j + 1)|)) =
      ∑ i ∈ range m, ∑ j ∈ range (m - i - 1),
        (min (w i) (w (i + j + 1)) / (t (i + j + 1) - t i) +
          min (w i) (w (i + j + 1)) / |t (i + j + 1) + t i|) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have hij : i + j + 1 < m := by omega
    have hpos : 0 < t (i + j + 1) - t i :=
      sub_pos.mpr (hmono hi' hij (by omega))
    rw [abs_sub_comm, abs_of_pos hpos]
    rw [add_comm (t i)]
  rw [heq]
  have h := candidate_sum_rademacher_height_interactions_le w t hw m ht hgap
  linarith

/-- The same bound for any ordered survivor set. Separation is required
only from a survivor to a later survivor; deleted microscopic heights do
not occur in this hypothesis or in the sum. -/
theorem candidate_sum_survivor_rademacher_interactions_le
    {α : Type*} [LinearOrder α] [Inhabited α]
    (s : Finset α) (w t : α → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (ht : ∀ i ∈ s, 0 ≤ t i)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, i < j → w i ≤ t j - t i) :
    (∑ ab ∈ s.offDiag,
      (min (w ab.1) (w ab.2) / |t ab.1 - t ab.2| +
        min (w ab.1) (w ab.2) / |t ab.1 + t ab.2|)) ≤
      8 * (s.card : ℝ) * Real.log ((s.card : ℝ) + 1) := by
  classical
  let e := s.orderEmbOfFin rfl
  let v : ℕ → α := fun n => if h : n < s.card then e ⟨n, h⟩ else default
  let w' : ℕ → ℝ := fun n => if h : n < s.card then w (e ⟨n, h⟩) else 1
  let t' : ℕ → ℝ := fun n => t (v n)
  have hv (n : ℕ) (hn : n < s.card) : v n = e ⟨n, hn⟩ := by simp [v, hn]
  have hvmem (n : ℕ) (hn : n < s.card) : v n ∈ s := by
    rw [hv n hn]
    exact s.orderEmbOfFin_mem rfl _
  have hvstrict (a b : ℕ) (ha : a < s.card) (hb : b < s.card) (hab : a < b) :
      v a < v b := by
    rw [hv a ha, hv b hb]
    exact e.strictMono (by exact hab)
  have hw' : ∀ n, 0 < w' n := by
    intro n
    dsimp only [w']
    split_ifs with hn
    · exact hw _ (s.orderEmbOfFin_mem rfl _)
    · norm_num
  have ht' : ∀ n, n < s.card → 0 ≤ t' n := fun n hn => ht _ (hvmem n hn)
  have hgap' : ∀ n, n + 1 < s.card → w' n ≤ t' (n + 1) - t' n := by
    intro n hn
    have hn' : n < s.card := by omega
    have h := hgap _ (hvmem n hn') _ (hvmem (n + 1) hn)
      (hvstrict n (n + 1) hn' hn (by omega))
    simpa [w', t', hv n hn', hn'] using h
  have hsum :
      (∑ ab ∈ (range s.card).offDiag,
        (min (w' ab.1) (w' ab.2) / |t' ab.1 - t' ab.2| +
          min (w' ab.1) (w' ab.2) / |t' ab.1 + t' ab.2|)) =
      ∑ ab ∈ s.offDiag,
        (min (w ab.1) (w ab.2) / |t ab.1 - t ab.2| +
          min (w ab.1) (w ab.2) / |t ab.1 + t ab.2|) := by
    apply Finset.sum_bij (fun ab _ => (v ab.1, v ab.2))
    · intro ab hab
      obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
      have ha' := Finset.mem_range.mp ha
      have hb' := Finset.mem_range.mp hb
      refine Finset.mem_offDiag.mpr ⟨hvmem _ ha', hvmem _ hb', ?_⟩
      rw [hv _ ha', hv _ hb']
      intro he
      exact hne (congrArg Fin.val (e.injective he))
    · intro ab hab cd hcd he
      obtain ⟨ha, hb, _⟩ := Finset.mem_offDiag.mp hab
      obtain ⟨hc, hd, _⟩ := Finset.mem_offDiag.mp hcd
      have he₁ := congrArg Prod.fst he
      have he₂ := congrArg Prod.snd he
      simp only [Prod.fst, Prod.snd] at he₁ he₂
      rw [hv _ (mem_range.mp ha), hv _ (mem_range.mp hc)] at he₁
      rw [hv _ (mem_range.mp hb), hv _ (mem_range.mp hd)] at he₂
      exact Prod.ext (congrArg Fin.val (e.injective he₁)) (congrArg Fin.val (e.injective he₂))
    · intro ab hab
      obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
      let a := (s.orderIsoOfFin rfl).symm ⟨ab.1, ha⟩
      let b := (s.orderIsoOfFin rfl).symm ⟨ab.2, hb⟩
      have hae : v a.val = ab.1 := by
        rw [hv _ a.isLt]
        exact congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨ab.1, ha⟩)
      have hbe : v b.val = ab.2 := by
        rw [hv _ b.isLt]
        exact congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨ab.2, hb⟩)
      refine ⟨(a.val, b.val), Finset.mem_offDiag.mpr
        ⟨mem_range.mpr a.isLt, mem_range.mpr b.isLt, ?_⟩, ?_⟩
      · intro he
        exact hne (hae.symm.trans ((congrArg v he).trans hbe))
      · exact Prod.ext hae hbe
    · intro ab hab
      obtain ⟨ha, hb, _⟩ := Finset.mem_offDiag.mp hab
      simp [w', t', hv _ (mem_range.mp ha), hv _ (mem_range.mp hb),
        mem_range.mp ha, mem_range.mp hb]
  rw [← hsum]
  exact candidate_sum_offDiag_rademacher_interactions_le w' t' hw' s.card ht' hgap'

/-- Finite heights can be ordered by their actual values. This bound needs
only their literal positive-band and successive-survivor separation
conditions, without a chosen enumeration in its statement. -/
theorem candidate_sum_fintype_rademacher_interactions_le
    {α : Type*} [Fintype α] (w t : α → ℝ)
    (hw : ∀ i, 0 < w i) (ht : ∀ i, 0 ≤ t i) (hinj : Function.Injective t)
    (hgap : ∀ i j, t i < t j → w i ≤ t j - t i) :
    (∑ ab ∈ (Finset.univ : Finset α).offDiag,
      (min (w ab.1) (w ab.2) / |t ab.1 - t ab.2| +
        min (w ab.1) (w ab.2) / |t ab.1 + t ab.2|)) ≤
      8 * (Fintype.card α : ℝ) * Real.log ((Fintype.card α : ℝ) + 1) := by
  classical
  cases isEmpty_or_nonempty α with
  | inl h => simp
  | inr h =>
    letI : Inhabited α := Classical.inhabited_of_nonempty h
    letI : LinearOrder α := LinearOrder.lift' t hinj
    simpa only [Finset.card_univ] using
      candidate_sum_survivor_rademacher_interactions_le (Finset.univ : Finset α)
        w t (fun i _ => hw i) (fun i _ => ht i) (fun i _ j _ hij => hgap i j hij)

/-- An original immediate-gap bound at surviving indices automatically
passes to the next surviving height, even when deleted indices intervene. -/
theorem candidate_sum_survivor_interactions_le_of_original_gaps
    (m : ℕ) (s : Finset ℕ) (hs : s ⊆ range m) (w t : ℕ → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (ht : ∀ i ∈ s, 0 ≤ t i)
    (hmono : MonotoneOn t (Set.Iio m))
    (hgap : ∀ i ∈ s, i + 1 < m → w i ≤ t (i + 1) - t i) :
    (∑ ab ∈ s.offDiag,
      (min (w ab.1) (w ab.2) / |t ab.1 - t ab.2| +
        min (w ab.1) (w ab.2) / |t ab.1 + t ab.2|)) ≤
      8 * (s.card : ℝ) * Real.log ((s.card : ℝ) + 1) := by
  apply candidate_sum_survivor_rademacher_interactions_le s w t hw ht
  intro i hi j hj hij
  have hj' := Finset.mem_range.mp (hs hj)
  have hi' : i + 1 < m := by omega
  have h := hmono hi' hj' (by omega : i + 1 ≤ j)
  linarith [hgap i hi hi']

end Erdos.Problem1144
