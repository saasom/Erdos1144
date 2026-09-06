import Erdos.Problem1144.HarperTwoHeightCutoffSchedule

open Finset MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Closed-rectangle form of the two-height block comparison

Sections of a two-sided partial-sum barrier are closed rectangles.  The
Fourier unsmoothing endpoint is stated for half-open rectangles.  We pass
between them by decreasing the two lower endpoints by `1/(m+1)` and using
continuity from above under the two finite probability measures.  This keeps
all atoms of the actual Rademacher law and removes a potential boundary gap
from the path replacement.
-/

/-- Decreasing half-open intervals with lower endpoint approaching `a` from
below intersect to the closed interval `Icc a b`. -/
theorem iInter_Ioc_sub_inv_succ_eq_Icc (a b : Real) :
    (⋂ m : Nat, Ioc (a - (((m + 1 : Nat) : Real))⁻¹) b) = Icc a b := by
  have hinv : Tendsto
      (fun m : Nat ↦ (((m + 1 : Nat) : Real))⁻¹) atTop (nhds 0) :=
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp
      (tendsto_add_atTop_nat 1)
  ext x
  simp only [Set.mem_iInter, Set.mem_Ioc, Set.mem_Icc]
  constructor
  · intro hx
    constructor
    · have hlower : Tendsto
          (fun m : Nat ↦ a - (((m + 1 : Nat) : Real))⁻¹)
          atTop (nhds a) := by
        convert tendsto_const_nhds.sub hinv using 1 <;> norm_num
      exact le_of_tendsto hlower
        (Eventually.of_forall fun m ↦ (hx m).1.le)
    · exact (hx 0).2
  · intro hx m
    have hinvPos : (0 : Real) < (((m + 1 : Nat) : Real))⁻¹ := by positivity
    constructor
    · linarith [hx.1]
    · exact hx.2

/-- Product version of `iInter_Ioc_sub_inv_succ_eq_Icc`. -/
theorem iInter_prod_Ioc_sub_inv_succ_eq_prod_Icc
    (a b c d : Real) :
    (⋂ m : Nat,
      Ioc (a - (((m + 1 : Nat) : Real))⁻¹) b ×ˢ
        Ioc (c - (((m + 1 : Nat) : Real))⁻¹) d) =
      Icc a b ×ˢ Icc c d := by
  ext x
  simp only [Set.mem_iInter, Set.mem_prod, Set.mem_Ioc, Set.mem_Icc]
  constructor
  · intro hx
    have hx1 : x.1 ∈ ⋂ m : Nat,
        Ioc (a - (((m + 1 : Nat) : Real))⁻¹) b := by
      exact Set.mem_iInter.mpr fun m ↦ (hx m).1
    have hx2 : x.2 ∈ ⋂ m : Nat,
        Ioc (c - (((m + 1 : Nat) : Real))⁻¹) d := by
      exact Set.mem_iInter.mpr fun m ↦ (hx m).2
    rw [iInter_Ioc_sub_inv_succ_eq_Icc] at hx1 hx2
    exact ⟨hx1, hx2⟩
  · intro hx m
    have hx1 : x.1 ∈ ⋂ m : Nat,
        Ioc (a - (((m + 1 : Nat) : Real))⁻¹) b := by
      rw [iInter_Ioc_sub_inv_succ_eq_Icc]
      exact hx.1
    have hx2 : x.2 ∈ ⋂ m : Nat,
        Ioc (c - (((m + 1 : Nat) : Real))⁻¹) d := by
      rw [iInter_Ioc_sub_inv_succ_eq_Icc]
      exact hx.2
    exact ⟨Set.mem_iInter.mp hx1 m, Set.mem_iInter.mp hx2 m⟩

set_option maxHeartbeats 800000 in
/-- The concrete cutoff comparison for the closed rectangles that arise as
sections of the pinched path event.  The input width `65n-1` leaves room for
the limiting lower-endpoint displacement while also accommodating the tiny
cumulative corridor enlargement during coordinate replacement. -/
theorem harperScheduledTwoHeightClosedCorridorRectangleMass_le_independentGaussian_cutoff
    (y j n : Nat) (t s : Real) {a b c d : Real}
    (hn : 4 ≤ n)
    (hab : a ≤ b) (hcd : c ≤ d)
    (habWidth : b - a ≤ 65 * (n : Real) - 1)
    (hcdWidth : d - c ≤ 65 * (n : Real) - 1)
    (hfrequency :
      4 * (n : Real) ^ (6 : Nat) ≤
        Real.sqrt (Problem520.harperBlockEndpoint j : Real))
    (hendpoint :
      1048576 * (n : Real) ^ (48 : Nat) ≤
        Real.sqrt (Problem520.harperBlockEndpoint j : Real))
    (hcovariance :
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y j) t s t s| ≤
        1 / (n : Real) ^ (40 : Nat)) :
    ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat) *
        (harperTwoHeightPrimeBlockVectorLaw y
          (Problem520.harperScheduledPrimeBlock y j) t s).real
            (Icc a b ×ˢ Icc c d) ≤
      (harperTwoHeightIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y j) t s).real
          (Icc (a - 4 * (1 / (n : Real) ^ (2 : Nat)))
              (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
            Icc (c - 4 * (1 / (n : Real) ^ (2 : Nat)))
              (d + 4 * (1 / (n : Real) ^ (2 : Nat)))) +
        6 / (n : Real) ^ (4 : Nat) := by
  let P := harperTwoHeightPrimeBlockVectorLaw y
    (Problem520.harperScheduledPrimeBlock y j) t s
  let Q := harperTwoHeightIndependentGaussianBlockLaw y
    (Problem520.harperScheduledPrimeBlock y j) t s
  let beta : Real :=
    ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
  let err : Real := 6 / (n : Real) ^ (4 : Nat)
  let e : Nat → Real := fun m ↦ (((m + 1 : Nat) : Real))⁻¹
  let A : Nat → Set (Real × Real) := fun m ↦
    Ioc (a - e m) b ×ˢ Ioc (c - e m) d
  let G : Nat → Set (Real × Real) := fun m ↦
    Ioc ((a - e m) - 4 * (1 / (n : Real) ^ (2 : Nat)))
        (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
      Ioc ((c - e m) - 4 * (1 / (n : Real) ^ (2 : Nat)))
        (d + 4 * (1 / (n : Real) ^ (2 : Nat)))
  have hePos (m : Nat) : 0 < e m := by
    dsimp only [e]
    positivity
  have heOne (m : Nat) : e m ≤ 1 := by
    dsimp only [e]
    apply inv_le_one_of_one_le₀
    exact_mod_cast (show 1 ≤ m + 1 by omega)
  have hAanti : Antitone A := by
    intro m k hmk x hx
    have hmkCast : ((m + 1 : Nat) : Real) ≤ (k + 1 : Nat) := by
      exact_mod_cast (show m + 1 ≤ k + 1 by omega)
    have he : e k ≤ e m := by
      dsimp only [e]
      exact inv_anti₀ (by positivity) hmkCast
    rcases hx with ⟨⟨hxa, hxb⟩, hxc, hxd⟩
    exact ⟨⟨by dsimp only [e] at he ⊢; linarith, hxb⟩,
      by dsimp only [e] at he ⊢; linarith, hxd⟩
  have hGanti : Antitone G := by
    intro m k hmk x hx
    have hmkCast : ((m + 1 : Nat) : Real) ≤ (k + 1 : Nat) := by
      exact_mod_cast (show m + 1 ≤ k + 1 by omega)
    have he : e k ≤ e m := by
      dsimp only [e]
      exact inv_anti₀ (by positivity) hmkCast
    rcases hx with ⟨⟨hxa, hxb⟩, hxc, hxd⟩
    exact ⟨⟨by dsimp only [e] at he ⊢; linarith, hxb⟩,
      by dsimp only [e] at he ⊢; linarith, hxd⟩
  have hAmeas (m : Nat) : MeasurableSet (A m) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have hGmeas (m : Nat) : MeasurableSet (G m) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have hAinter : (⋂ m, A m) = Icc a b ×ˢ Icc c d := by
    simpa only [A, e] using
      iInter_prod_Ioc_sub_inv_succ_eq_prod_Icc a b c d
  have hGinter : (⋂ m, G m) =
      Icc (a - 4 * (1 / (n : Real) ^ (2 : Nat)))
          (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
        Icc (c - 4 * (1 / (n : Real) ^ (2 : Nat)))
          (d + 4 * (1 / (n : Real) ^ (2 : Nat))) := by
    have hGeq (m : Nat) : G m =
        Ioc ((a - 4 * (1 / (n : Real) ^ (2 : Nat))) - e m)
            (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
          Ioc ((c - 4 * (1 / (n : Real) ^ (2 : Nat))) - e m)
            (d + 4 * (1 / (n : Real) ^ (2 : Nat))) := by
      dsimp only [G]
      congr 1 <;> ring
    calc
      (⋂ m, G m) =
          ⋂ m,
            Ioc ((a - 4 * (1 / (n : Real) ^ (2 : Nat))) - e m)
                (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
              Ioc ((c - 4 * (1 / (n : Real) ^ (2 : Nat))) - e m)
                (d + 4 * (1 / (n : Real) ^ (2 : Nat))) := by
            congr 1
            funext m
            exact hGeq m
      _ = _ := by
        simpa only [e] using
          iInter_prod_Ioc_sub_inv_succ_eq_prod_Icc
            (a - 4 * (1 / (n : Real) ^ (2 : Nat)))
            (b + 4 * (1 / (n : Real) ^ (2 : Nat)))
            (c - 4 * (1 / (n : Real) ^ (2 : Nat)))
            (d + 4 * (1 / (n : Real) ^ (2 : Nat)))
  have hlocal (m : Nat) : beta * P.real (A m) ≤ Q.real (G m) + err := by
    have habm : a - e m ≤ b := by linarith [hab, hePos m]
    have hcdm : c - e m ≤ d := by linarith [hcd, hePos m]
    have hwidthA : b - (a - e m) ≤ 65 * (n : Real) := by
      have hnR : (4 : Real) ≤ n := by exact_mod_cast hn
      nlinarith [habWidth, heOne m]
    have hwidthC : d - (c - e m) ≤ 65 * (n : Real) := by
      have hnR : (4 : Real) ≤ n := by exact_mod_cast hn
      nlinarith [hcdWidth, heOne m]
    simpa only [P, Q, beta, err, A, G, e] using
      harperScheduledTwoHeightCorridorRectangleMass_le_independentGaussian_cutoff
        y j n t s hn habm hcdm hwidthA hwidthC hfrequency hendpoint
          hcovariance
  have hPmeasure : Tendsto (fun m ↦ P (A m)) atTop
      (nhds (P (Icc a b ×ˢ Icc c d))) := by
    simpa only [hAinter] using
      (tendsto_measure_iInter_atTop (μ := P)
        (fun m ↦ (hAmeas m).nullMeasurableSet) hAanti
          ⟨0, measure_ne_top P _⟩)
  have hQmeasure : Tendsto (fun m ↦ Q (G m)) atTop
      (nhds (Q
        (Icc (a - 4 * (1 / (n : Real) ^ (2 : Nat)))
            (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
          Icc (c - 4 * (1 / (n : Real) ^ (2 : Nat)))
            (d + 4 * (1 / (n : Real) ^ (2 : Nat)))))) := by
    simpa only [hGinter] using
      (tendsto_measure_iInter_atTop (μ := Q)
        (fun m ↦ (hGmeas m).nullMeasurableSet) hGanti
          ⟨0, measure_ne_top Q _⟩)
  have hPreal : Tendsto (fun m ↦ P.real (A m)) atTop
      (nhds (P.real (Icc a b ×ˢ Icc c d))) :=
    (ENNReal.tendsto_toReal (measure_ne_top P _)).comp hPmeasure
  have hQreal : Tendsto (fun m ↦ Q.real (G m)) atTop
      (nhds (Q.real
        (Icc (a - 4 * (1 / (n : Real) ^ (2 : Nat)))
            (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
          Icc (c - 4 * (1 / (n : Real) ^ (2 : Nat)))
            (d + 4 * (1 / (n : Real) ^ (2 : Nat)))))) :=
    (ENNReal.tendsto_toReal (measure_ne_top Q _)).comp hQmeasure
  change beta * P.real (Icc a b ×ˢ Icc c d) ≤
    Q.real
      (Icc (a - 4 * (1 / (n : Real) ^ (2 : Nat)))
          (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
        Icc (c - 4 * (1 / (n : Real) ^ (2 : Nat)))
          (d + 4 * (1 / (n : Real) ^ (2 : Nat)))) + err
  exact le_of_tendsto_of_tendsto'
    (tendsto_const_nhds.mul hPreal)
    (hQreal.add tendsto_const_nhds)
    hlocal

#print axioms Erdos.Problem1144.iInter_Ioc_sub_inv_succ_eq_Icc
#print axioms Erdos.Problem1144.harperScheduledTwoHeightClosedCorridorRectangleMass_le_independentGaussian_cutoff

end

end Problem1144
end Erdos
