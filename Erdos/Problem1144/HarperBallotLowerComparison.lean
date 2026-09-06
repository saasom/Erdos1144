import Erdos.Problem520.HarperScheduledRelativeProduct
import Erdos.Problem520.HarperCentralBandBarrier

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace Erdos
namespace Problem1144

/-!
# Lower Gaussian comparison for Harper's scheduled blocks

The Problem 520 development only needed upper comparison, but its
doubly-exponential smoothing error is already smaller than a summable
fraction of every moderate Gaussian lattice cell.  The same absolute CDF
estimate therefore gives the reverse comparison needed for a ballot lower
bound.
-/

/-- On every sufficiently late moderate cell, the actual centered Harper
block law has at least `1 - (j+1)⁻²` times the corresponding variance-matched
Gaussian mass. -/
theorem
    exists_eventually_one_sub_width_mul_gaussian_le_harperScheduledIntervalProbability
    (M : Nat) :
    ∃ J : Nat, ∀ j : Nat, J <= j -> ∀ y : Nat,
      Problem520.harperBlockEndpoint (j + 1) <= y ->
        ∀ t : Real, 1 <= |t| -> |t| <= M ->
          ∀ a : Real,
            |a| + 1 <= (1 / 4 : Real) *
              Real.sqrt (((2 ^ j : Nat) : Real)) ->
            (1 - Problem520.harperScheduledRelativeIntervalWidth j) *
                (Problem520.harperGaussianBlockLaw y
                  (Problem520.harperScheduledPrimeBlock y j) t t).real
                    (Ioc a
                      (a + Problem520.harperScheduledRelativeIntervalWidth j)) <=
              (Problem520.harperCenteredLinearBlockLaw y
                (Problem520.harperScheduledPrimeBlock y j) t t).real
                  (Ioc a
                    (a + Problem520.harperScheduledRelativeIntervalWidth j)) := by
  obtain ⟨Jcdf, hJcdf⟩ :=
    Problem520.exists_eventually_harperScheduledDiagonalCDFDistance_le_strong_unconditional M
  obtain ⟨Jvar, hJvar⟩ :=
    Problem520.exists_eventually_harperScheduledDiagonalVariance_third_threeEighths M
  obtain ⟨Jbudget, hJbudget⟩ := eventually_atTop.1
    Problem520.eventually_harperScheduledStrongBudget_le_width_mul_relativeGaussianMass
  refine ⟨max (max Jcdf Jvar) Jbudget, ?_⟩
  intro j hj y hy t htLower htUpper a ha
  have hjcdf : Jcdf <= j :=
    (le_max_left Jcdf Jvar).trans (le_max_left _ Jbudget) |>.trans hj
  have hjvar : Jvar <= j :=
    (le_max_right Jcdf Jvar).trans (le_max_left _ Jbudget) |>.trans hj
  have hjbudget : Jbudget <= j := (le_max_right _ Jbudget).trans hj
  let rho := Problem520.harperCenteredLinearBlockLaw y
    (Problem520.harperScheduledPrimeBlock y j) t t
  let nu := Problem520.harperGaussianBlockLaw y
    (Problem520.harperScheduledPrimeBlock y j) t t
  let delta := Problem520.harperScheduledRelativeIntervalWidth j
  have hdist : Problem520.harperCDFDistance rho nu <=
      130 / Problem520.harperScheduledStrongComparisonFrequency j :=
    hJcdf j hjcdf y hy t htLower htUpper
  have habs : |rho.real (Ioc a (a + delta)) -
      nu.real (Ioc a (a + delta))| <=
        2 * Problem520.harperCDFDistance rho nu :=
    Problem520.abs_measureReal_Ioc_sub_le_two_mul_cdfDistance rho nu
      (by dsimp [delta]; linarith
        [Problem520.harperScheduledRelativeIntervalWidth_pos j])
  have hvar := hJvar j hjvar y hy t htLower htUpper
  have hgaussian :
      (delta / 2) * Real.exp (-2 * (|a| + 1) ^ 2) <=
        nu.real (Ioc a (a + delta)) := by
    dsimp only [nu, Problem520.harperGaussianBlockLaw]
    exact Problem520.gaussianReal_real_Ioc_ge_of_variance_mem
      (v := Problem520.harperLinearBlockVarianceNNReal y
        (Problem520.harperScheduledPrimeBlock y j) t t)
      (by simpa only [Problem520.coe_harperLinearBlockVarianceNNReal] using
        hvar.1.le)
      (by simpa only [Problem520.coe_harperLinearBlockVarianceNNReal] using
        hvar.2.le)
      (by simpa only [delta] using
        Problem520.harperScheduledRelativeIntervalWidth_pos j)
      (by simpa only [delta] using
        Problem520.harperScheduledRelativeIntervalWidth_le_one j)
  have hbudget := hJbudget j hjbudget a ha
  have herr : nu.real (Ioc a (a + delta)) -
      rho.real (Ioc a (a + delta)) <=
        delta * nu.real (Ioc a (a + delta)) := by
    calc
      nu.real (Ioc a (a + delta)) - rho.real (Ioc a (a + delta)) <=
          |rho.real (Ioc a (a + delta)) -
            nu.real (Ioc a (a + delta))| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      _ <= 2 * Problem520.harperCDFDistance rho nu := habs
      _ <= 2 * (130 /
          Problem520.harperScheduledStrongComparisonFrequency j) := by gcongr
      _ = 260 /
          Problem520.harperScheduledStrongComparisonFrequency j := by ring
      _ <= delta * ((delta / 2) *
          Real.exp (-2 * (|a| + 1) ^ 2)) := by
        simpa only [delta] using hbudget
      _ <= delta * nu.real (Ioc a (a + delta)) := by
        gcongr
        exact (Problem520.harperScheduledRelativeIntervalWidth_pos j).le
  dsimp only [rho, nu, delta] at herr ⊢
  linarith

/-- Central-band version of the reverse one-cell comparison.  The block
index is shifted by the dyadic band depth, exactly as in the unconditional
central-band local limit theorem from the Problem 520 development. -/
theorem
    exists_one_sub_width_mul_gaussian_le_harperScheduledCentralBandIntervalProbability :
    ∃ J : Nat, ∀ d j y : Nat, J + d <= j ->
      Problem520.harperBlockEndpoint (j + 1) <= y ->
        ∀ t : Real,
          (1 / 2 : Real) ^ (d + 1) < |t| ->
          |t| <= (1 / 2 : Real) ^ d ->
            ∀ a : Real,
              |a| + 1 <= (1 / 4 : Real) *
                Real.sqrt (((2 ^ j : Nat) : Real)) ->
              (1 - Problem520.harperScheduledRelativeIntervalWidth j) *
                  (Problem520.harperGaussianBlockLaw y
                    (Problem520.harperScheduledPrimeBlock y j) t t).real
                      (Ioc a
                        (a + Problem520.harperScheduledRelativeIntervalWidth j)) <=
                (Problem520.harperCenteredLinearBlockLaw y
                  (Problem520.harperScheduledPrimeBlock y j) t t).real
                    (Ioc a
                      (a + Problem520.harperScheduledRelativeIntervalWidth j)) := by
  obtain ⟨Jcdf, hJcdf⟩ :=
    Problem520.exists_harperScheduledCentralBandCDFDistance_le_strong
  obtain ⟨Jvar, hJvar⟩ :=
    Problem520.exists_harperScheduledCentralBandDiagonalVariance_third_threeEighths
  obtain ⟨Jbudget, hJbudget⟩ := eventually_atTop.1
    Problem520.eventually_harperScheduledStrongBudget_le_width_mul_relativeGaussianMass
  refine ⟨max (max Jcdf Jvar) Jbudget, ?_⟩
  intro d j y hj hy t htLower htUpper a ha
  have hjcdf : Jcdf + d <= j := by omega
  have hjvar : Jvar + d <= j := by omega
  have hjbudget : Jbudget <= j := by omega
  let rho := Problem520.harperCenteredLinearBlockLaw y
    (Problem520.harperScheduledPrimeBlock y j) t t
  let nu := Problem520.harperGaussianBlockLaw y
    (Problem520.harperScheduledPrimeBlock y j) t t
  let delta := Problem520.harperScheduledRelativeIntervalWidth j
  have hdist : Problem520.harperCDFDistance rho nu <=
      130 / Problem520.harperScheduledStrongComparisonFrequency j :=
    hJcdf d j y hjcdf hy t htLower htUpper t (by simp)
  have habs : |rho.real (Ioc a (a + delta)) -
      nu.real (Ioc a (a + delta))| <=
        2 * Problem520.harperCDFDistance rho nu :=
    Problem520.abs_measureReal_Ioc_sub_le_two_mul_cdfDistance rho nu
      (by dsimp [delta]; linarith
        [Problem520.harperScheduledRelativeIntervalWidth_pos j])
  have hvar := hJvar d j y hjvar hy t htLower htUpper
  have hgaussian :
      (delta / 2) * Real.exp (-2 * (|a| + 1) ^ 2) <=
        nu.real (Ioc a (a + delta)) := by
    dsimp only [nu, Problem520.harperGaussianBlockLaw]
    exact Problem520.gaussianReal_real_Ioc_ge_of_variance_mem
      (v := Problem520.harperLinearBlockVarianceNNReal y
        (Problem520.harperScheduledPrimeBlock y j) t t)
      (by simpa only [Problem520.coe_harperLinearBlockVarianceNNReal] using
        hvar.1.le)
      (by simpa only [Problem520.coe_harperLinearBlockVarianceNNReal] using
        hvar.2.le)
      (by simpa only [delta] using
        Problem520.harperScheduledRelativeIntervalWidth_pos j)
      (by simpa only [delta] using
        Problem520.harperScheduledRelativeIntervalWidth_le_one j)
  have hbudget := hJbudget j hjbudget a ha
  have herr : nu.real (Ioc a (a + delta)) -
      rho.real (Ioc a (a + delta)) <=
        delta * nu.real (Ioc a (a + delta)) := by
    calc
      nu.real (Ioc a (a + delta)) - rho.real (Ioc a (a + delta)) <=
          |rho.real (Ioc a (a + delta)) -
            nu.real (Ioc a (a + delta))| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      _ <= 2 * Problem520.harperCDFDistance rho nu := habs
      _ <= 2 * (130 /
          Problem520.harperScheduledStrongComparisonFrequency j) := by gcongr
      _ = 260 /
          Problem520.harperScheduledStrongComparisonFrequency j := by ring
      _ <= delta * ((delta / 2) *
          Real.exp (-2 * (|a| + 1) ^ 2)) := by
        simpa only [delta] using hbudget
      _ <= delta * nu.real (Ioc a (a + delta)) := by
        gcongr
        exact (Problem520.harperScheduledRelativeIntervalWidth_pos j).le
  dsimp only [rho, nu, delta] at herr ⊢
  linarith

/-! ## Uniform product-cell lower comparison -/

theorem harperScheduledRelativeIntervalWidth_le_reciprocalDifference
    {j : Nat} (hj : 0 < j) :
    Problem520.harperScheduledRelativeIntervalWidth j <=
      1 / (j : Real) - 1 / ((j + 1 : Nat) : Real) := by
  unfold Problem520.harperScheduledRelativeIntervalWidth
  have hjpos : (0 : Real) < j := by exact_mod_cast hj
  have hsuccpos : (0 : Real) < j + 1 := by positivity
  push_cast
  calc
    (((j : Real) + 1) ^ 2)⁻¹ <=
        ((j : Real) * ((j : Real) + 1))⁻¹ := by
      simpa only [one_div] using
        one_div_le_one_div_of_le (mul_pos hjpos hsuccpos) (by nlinarith)
    _ = 1 / (j : Real) - 1 / ((j : Real) + 1) := by
      field_simp
      ring

/-- The tail of the scheduled cell widths is at most `1/start`. -/
theorem sum_fin_harperScheduledRelativeIntervalWidth_le_inv
    (start n : Nat) (hstart : 0 < start) :
    (∑ i : Fin n,
      Problem520.harperScheduledRelativeIntervalWidth
        (start + (i : Nat))) <= 1 / (start : Real) := by
  have hstrong : ∀ m : Nat,
      (∑ i ∈ Finset.range m,
        Problem520.harperScheduledRelativeIntervalWidth (start + i)) <=
          1 / (start : Real) - 1 / ((start + m : Nat) : Real) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ]
        have hindex : 0 < start + m := by omega
        have hcell :=
          harperScheduledRelativeIntervalWidth_le_reciprocalDifference hindex
        calc
          (∑ i ∈ Finset.range m,
              Problem520.harperScheduledRelativeIntervalWidth (start + i)) +
                Problem520.harperScheduledRelativeIntervalWidth (start + m) <=
              (1 / (start : Real) -
                1 / ((start + m : Nat) : Real)) +
                (1 / ((start + m : Nat) : Real) -
                  1 / ((start + m + 1 : Nat) : Real)) :=
            add_le_add ih hcell
          _ = 1 / (start : Real) -
                1 / ((start + (m + 1) : Nat) : Real) := by ring
  calc
    (∑ i : Fin n,
        Problem520.harperScheduledRelativeIntervalWidth
          (start + (i : Nat))) =
        ∑ i ∈ Finset.range n,
          Problem520.harperScheduledRelativeIntervalWidth (start + i) :=
      Fin.sum_univ_eq_sum_range
        (fun i => Problem520.harperScheduledRelativeIntervalWidth
          (start + i)) n
    _ <= 1 / (start : Real) - 1 / ((start + n : Nat) : Real) :=
      hstrong n
    _ <= 1 / (start : Real) := sub_le_self _ (by positivity)

/-- Elementary finite product lower bound used to multiply the reverse local
comparisons. -/
theorem one_sub_sum_le_prod_one_sub
    {ι : Type*} (s : Finset ι) (a : ι -> Real)
    (ha0 : ∀ i ∈ s, 0 <= a i) (ha1 : ∀ i ∈ s, a i <= 1) :
    1 - ∑ i ∈ s, a i <= ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      have hai0 : 0 <= a i := ha0 i (Finset.mem_insert_self i s)
      have hai1 : a i <= 1 := ha1 i (Finset.mem_insert_self i s)
      have hsum0 : 0 <= ∑ j ∈ s, a j :=
        Finset.sum_nonneg fun j hj => ha0 j (Finset.mem_insert_of_mem hj)
      have hih : 1 - ∑ j ∈ s, a j <= ∏ j ∈ s, (1 - a j) :=
        ih (fun j hj => ha0 j (Finset.mem_insert_of_mem hj))
          (fun j hj => ha1 j (Finset.mem_insert_of_mem hj))
      calc
        1 - (a i + ∑ j ∈ s, a j) <=
            (1 - a i) * (1 - ∑ j ∈ s, a j) := by
          nlinarith [mul_nonneg hai0 hsum0]
        _ <= (1 - a i) * ∏ j ∈ s, (1 - a j) :=
          mul_le_mul_of_nonneg_left hih (by linarith)

/-- Starting at block `4`, multiplying every reverse local loss still keeps
at least three quarters of the Gaussian product mass. -/
theorem three_fourths_le_prod_one_sub_harperScheduledRelativeIntervalWidth
    (start n : Nat) (hstart : 4 <= start) :
    (3 / 4 : Real) <=
      ∏ i : Fin n, (1 -
        Problem520.harperScheduledRelativeIntervalWidth
          (start + (i : Nat))) := by
  let a : Fin n -> Real := fun i =>
    Problem520.harperScheduledRelativeIntervalWidth (start + (i : Nat))
  have hsum : (∑ i : Fin n, a i) <= 1 / (start : Real) := by
    simpa only [a] using
      sum_fin_harperScheduledRelativeIntervalWidth_le_inv start n (by omega)
  have hstartReal : (4 : Real) <= start := by exact_mod_cast hstart
  have hinv : 1 / (start : Real) <= 1 / 4 := by
    exact one_div_le_one_div_of_le (by norm_num) hstartReal
  have hprod := one_sub_sum_le_prod_one_sub Finset.univ a
    (fun i _hi =>
      (Problem520.harperScheduledRelativeIntervalWidth_pos _).le)
    (fun i _hi =>
      Problem520.harperScheduledRelativeIntervalWidth_le_one _)
  calc
    (3 / 4 : Real) <= 1 - ∑ i : Fin n, a i := by
      linarith [hsum.trans hinv]
    _ <= ∏ i : Fin n, (1 - a i) := by
      simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using hprod
    _ = _ := rfl

/-- Uniform reverse comparison for every moderate scheduled product lattice
cell.  Unlike the upper comparison, the retained constant is simply `3/4`. -/
theorem exists_eventually_three_fourths_mul_gaussian_le_harperScheduledModerateCoordinateCell
    (M : Nat) :
    ∃ J : Nat, ∀ start : Nat, J <= start -> ∀ n y : Nat,
      Problem520.harperBlockEndpoint (start + n) <= y ->
        ∀ t : Real, 1 <= |t| -> |t| <= M ->
          ∀ z : Fin n -> Int,
            (∀ i : Fin n,
              |(z i : Real) *
                  Problem520.harperScheduledRelativeIntervalWidth
                    (start + (i : Nat))| + 1 <=
                (1 / 4 : Real) *
                  Real.sqrt (((2 ^ (start + (i : Nat)) : Nat) : Real))) ->
            (3 / 4 : Real) *
                (Measure.pi (fun i : Fin n =>
                  Problem520.harperGaussianBlockLaw y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + (i : Nat))) t t)).real
                  (Problem520.harperLatticeIocCell
                    (fun i : Fin n =>
                      Problem520.harperScheduledRelativeIntervalWidth
                        (start + (i : Nat))) z) <=
              (Measure.pi (fun i : Fin n =>
                Problem520.harperCenteredLinearBlockLaw y
                  (Problem520.harperScheduledPrimeBlock y
                    (start + (i : Nat))) t t)).real
                (Problem520.harperLatticeIocCell
                  (fun i : Fin n =>
                    Problem520.harperScheduledRelativeIntervalWidth
                      (start + (i : Nat))) z) := by
  obtain ⟨Jlocal, hlocal⟩ :=
    exists_eventually_one_sub_width_mul_gaussian_le_harperScheduledIntervalProbability M
  refine ⟨max Jlocal 4, ?_⟩
  intro start hstart n y hy t htLower htUpper z hz
  have hstartLocal : Jlocal <= start := (le_max_left _ 4).trans hstart
  have hstartFour : 4 <= start := (le_max_right Jlocal 4).trans hstart
  let rho : Fin n -> Measure Real := fun i =>
    Problem520.harperCenteredLinearBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + (i : Nat))) t t
  let nu : Fin n -> Measure Real := fun i =>
    Problem520.harperGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + (i : Nat))) t t
  let delta : Fin n -> Real := fun i =>
    Problem520.harperScheduledRelativeIntervalWidth (start + (i : Nat))
  have hendpoint (i : Fin n) :
      Problem520.harperBlockEndpoint (start + (i : Nat) + 1) <= y :=
    (Problem520.monotone_harperBlockEndpoint (by omega)).trans hy
  have hcoord (i : Fin n) :
      (1 - delta i) *
          (nu i).real (Ioc ((z i : Real) * delta i)
            ((z i : Real) * delta i + delta i)) <=
        (rho i).real (Ioc ((z i : Real) * delta i)
          ((z i : Real) * delta i + delta i)) := by
    exact hlocal (start + (i : Nat)) (by omega) y (hendpoint i)
      t htLower htUpper ((z i : Real) * delta i)
      (by simpa only [delta] using hz i)
  rw [Problem520.harperLatticeIocCell,
    Problem520.measureReal_pi_harperCoordinateIocCell,
    Problem520.measureReal_pi_harperCoordinateIocCell]
  have hprodCoord :
      (∏ i : Fin n, (1 - delta i) *
        (nu i).real (Ioc ((z i : Real) * delta i)
          ((z i : Real) * delta i + delta i))) <=
        ∏ i : Fin n,
          (rho i).real (Ioc ((z i : Real) * delta i)
            ((z i : Real) * delta i + delta i)) := by
    exact Finset.prod_le_prod
      (fun i _hi => mul_nonneg
        (sub_nonneg.mpr
          (Problem520.harperScheduledRelativeIntervalWidth_le_one _))
        measureReal_nonneg)
      (fun i _hi => hcoord i)
  have hfactor : (3 / 4 : Real) <= ∏ i : Fin n, (1 - delta i) := by
    simpa only [delta] using
      three_fourths_le_prod_one_sub_harperScheduledRelativeIntervalWidth
        start n hstartFour
  have hnuNonneg : 0 <= ∏ i : Fin n,
      (nu i).real (Ioc ((z i : Real) * delta i)
        ((z i : Real) * delta i + delta i)) :=
    Finset.prod_nonneg fun i _hi => measureReal_nonneg
  calc
    (3 / 4 : Real) * ∏ i : Fin n,
        (nu i).real (Ioc ((z i : Real) * delta i)
          ((z i : Real) * delta i + delta i)) <=
        (∏ i : Fin n, (1 - delta i)) *
          ∏ i : Fin n, (nu i).real
            (Ioc ((z i : Real) * delta i)
              ((z i : Real) * delta i + delta i)) :=
      mul_le_mul_of_nonneg_right hfactor hnuNonneg
    _ = ∏ i : Fin n, (1 - delta i) *
        (nu i).real (Ioc ((z i : Real) * delta i)
          ((z i : Real) * delta i + delta i)) := by
      rw [Finset.prod_mul_distrib]
    _ <= _ := hprodCoord

/-- Central-band reverse comparison for every moderate product lattice cell.
The shift `J + d <= start` is the only extra cost of allowing frequencies
of size `2^-d`. -/
theorem
    exists_three_fourths_mul_gaussian_le_harperScheduledCentralBandModerateCoordinateCell :
    ∃ J : Nat, ∀ d start : Nat, J + d <= start -> ∀ n y : Nat,
      Problem520.harperBlockEndpoint (start + n) <= y ->
        ∀ t : Real,
          (1 / 2 : Real) ^ (d + 1) < |t| ->
          |t| <= (1 / 2 : Real) ^ d ->
            ∀ z : Fin n -> Int,
              (∀ i : Fin n,
                |(z i : Real) *
                    Problem520.harperScheduledRelativeIntervalWidth
                      (start + (i : Nat))| + 1 <=
                  (1 / 4 : Real) *
                    Real.sqrt (((2 ^ (start + (i : Nat)) : Nat) : Real))) ->
              (3 / 4 : Real) *
                  (Measure.pi (fun i : Fin n =>
                    Problem520.harperGaussianBlockLaw y
                      (Problem520.harperScheduledPrimeBlock y
                        (start + (i : Nat))) t t)).real
                    (Problem520.harperLatticeIocCell
                      (fun i : Fin n =>
                        Problem520.harperScheduledRelativeIntervalWidth
                          (start + (i : Nat))) z) <=
                (Measure.pi (fun i : Fin n =>
                  Problem520.harperCenteredLinearBlockLaw y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + (i : Nat))) t t)).real
                  (Problem520.harperLatticeIocCell
                    (fun i : Fin n =>
                      Problem520.harperScheduledRelativeIntervalWidth
                        (start + (i : Nat))) z) := by
  obtain ⟨Jlocal, hlocal⟩ :=
    exists_one_sub_width_mul_gaussian_le_harperScheduledCentralBandIntervalProbability
  refine ⟨max Jlocal 4, ?_⟩
  intro d start hstart n y hy t htLower htUpper z hz
  have hstartFour : 4 <= start := by omega
  let rho : Fin n -> Measure Real := fun i =>
    Problem520.harperCenteredLinearBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + (i : Nat))) t t
  let nu : Fin n -> Measure Real := fun i =>
    Problem520.harperGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + (i : Nat))) t t
  let delta : Fin n -> Real := fun i =>
    Problem520.harperScheduledRelativeIntervalWidth (start + (i : Nat))
  have hendpoint (i : Fin n) :
      Problem520.harperBlockEndpoint (start + (i : Nat) + 1) <= y :=
    (Problem520.monotone_harperBlockEndpoint (by omega)).trans hy
  have hcoord (i : Fin n) :
      (1 - delta i) *
          (nu i).real (Ioc ((z i : Real) * delta i)
            ((z i : Real) * delta i + delta i)) <=
        (rho i).real (Ioc ((z i : Real) * delta i)
          ((z i : Real) * delta i + delta i)) := by
    exact hlocal d (start + (i : Nat)) y (by omega) (hendpoint i)
      t htLower htUpper ((z i : Real) * delta i)
      (by simpa only [delta] using hz i)
  rw [Problem520.harperLatticeIocCell,
    Problem520.measureReal_pi_harperCoordinateIocCell,
    Problem520.measureReal_pi_harperCoordinateIocCell]
  have hprodCoord :
      (∏ i : Fin n, (1 - delta i) *
        (nu i).real (Ioc ((z i : Real) * delta i)
          ((z i : Real) * delta i + delta i))) <=
        ∏ i : Fin n,
          (rho i).real (Ioc ((z i : Real) * delta i)
            ((z i : Real) * delta i + delta i)) := by
    exact Finset.prod_le_prod
      (fun i _hi => mul_nonneg
        (sub_nonneg.mpr
          (Problem520.harperScheduledRelativeIntervalWidth_le_one _))
        measureReal_nonneg)
      (fun i _hi => hcoord i)
  have hfactor : (3 / 4 : Real) <= ∏ i : Fin n, (1 - delta i) := by
    simpa only [delta] using
      three_fourths_le_prod_one_sub_harperScheduledRelativeIntervalWidth
        start n hstartFour
  have hnuNonneg : 0 <= ∏ i : Fin n,
      (nu i).real (Ioc ((z i : Real) * delta i)
        ((z i : Real) * delta i + delta i)) :=
    Finset.prod_nonneg fun i _hi => measureReal_nonneg
  calc
    (3 / 4 : Real) * ∏ i : Fin n,
        (nu i).real (Ioc ((z i : Real) * delta i)
          ((z i : Real) * delta i + delta i)) <=
        (∏ i : Fin n, (1 - delta i)) *
          ∏ i : Fin n, (nu i).real
            (Ioc ((z i : Real) * delta i)
              ((z i : Real) * delta i + delta i)) :=
      mul_le_mul_of_nonneg_right hfactor hnuNonneg
    _ = ∏ i : Fin n, (1 - delta i) *
        (nu i).real (Ioc ((z i : Real) * delta i)
          ((z i : Real) * delta i + delta i)) := by
      rw [Finset.prod_mul_distrib]
    _ <= _ := hprodCoord

/-! ## Reverse finite slicing for path barriers -/

/-- A cellwise lower comparison passes exactly to a finite disjoint union. -/
theorem const_mul_measureReal_biUnion_finset_le_of_cellwise
    {Omega Iota : Type*} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (C : Real) (s : Finset Iota) (cell : Iota -> Set Omega)
    (hdisj : Set.PairwiseDisjoint (↑s : Set Iota) cell)
    (hmeas : ∀ i ∈ s, MeasurableSet (cell i))
    (hcell : ∀ i ∈ s, C * Q.real (cell i) <= P.real (cell i)) :
    C * Q.real (⋃ i ∈ s, cell i) <=
      P.real (⋃ i ∈ s, cell i) := by
  calc
    C * Q.real (⋃ i ∈ s, cell i) =
        C * ∑ i ∈ s, Q.real (cell i) := by
      rw [measureReal_biUnion_finset hdisj hmeas]
    _ = ∑ i ∈ s, C * Q.real (cell i) := by rw [Finset.mul_sum]
    _ <= ∑ i ∈ s, P.real (cell i) := Finset.sum_le_sum hcell
    _ = P.real (⋃ i ∈ s, cell i) := by
      rw [measureReal_biUnion_finset hdisj hmeas]

/-- Reverse finite slicing: Gaussian paths in the cumulatively contracted
barrier and moderate box are covered by cells lying wholly inside the target
barrier. -/
theorem const_mul_measureReal_inter_contractedBarrier_box_le_barrier
    {n : Nat} (P Q : Measure (Fin n -> Real))
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (C : Real) (hC : 0 <= C)
    {delta R lower upper : Fin n -> Real}
    (hdelta : ∀ i, 0 < delta i)
    (hcell : ∀ z ∈ Problem520.harperBarrierBoxLatticeSlice delta R
        (fun k => lower k + Problem520.harperCumulativeCellWidth delta k)
        (fun k => upper k - Problem520.harperCumulativeCellWidth delta k),
      C * Q.real (Problem520.harperLatticeIocCell delta z) <=
        P.real (Problem520.harperLatticeIocCell delta z)) :
    C * Q.real
        (Problem520.harperPartialSumBarrierSet
            (fun k => lower k +
              Problem520.harperCumulativeCellWidth delta k)
            (fun k => upper k -
              Problem520.harperCumulativeCellWidth delta k) ∩
          Problem520.harperCoordinateBox R) <=
      P.real (Problem520.harperPartialSumBarrierSet lower upper) := by
  let lower' : Fin n -> Real := fun k =>
    lower k + Problem520.harperCumulativeCellWidth delta k
  let upper' : Fin n -> Real := fun k =>
    upper k - Problem520.harperCumulativeCellWidth delta k
  let s : Finset (Fin n -> Int) :=
    Problem520.harperBarrierBoxLatticeSlice delta R lower' upper'
  let U : Set (Fin n -> Real) :=
    ⋃ z ∈ s, Problem520.harperLatticeIocCell delta z
  have hdisj : Set.PairwiseDisjoint (↑s : Set (Fin n -> Int))
      (Problem520.harperLatticeIocCell delta) := by
    intro z _hz w _hw hzw
    exact Problem520.pairwiseDisjoint_harperLatticeIocCell hdelta hzw
  have hmeas : ∀ z ∈ s,
      MeasurableSet (Problem520.harperLatticeIocCell delta z) :=
    fun z _hz => Problem520.measurableSet_harperLatticeIocCell delta z
  have hunion := const_mul_measureReal_biUnion_finset_le_of_cellwise
    P Q C s (Problem520.harperLatticeIocCell delta) hdisj hmeas (by
      intro z hz
      exact hcell z (by simpa only [s, lower', upper'] using hz))
  have hcover :
      Problem520.harperPartialSumBarrierSet lower' upper' ∩
          Problem520.harperCoordinateBox R ⊆ U := by
    simpa only [U, s] using
      (Problem520.inter_barrier_box_subset_biUnion_activeLatticeSlice
        (delta := delta) (R := R) (lower := lower') (upper := upper') hdelta)
  have hexpanded :
      Problem520.harperExpandedPartialSumBarrierSet lower' upper' delta =
        Problem520.harperPartialSumBarrierSet lower upper := by
    ext omega
    change
      (∀ k,
        lower' k - Problem520.harperCumulativeCellWidth delta k <=
            Problem520.harperPathPartialSum omega k ∧
          Problem520.harperPathPartialSum omega k <=
            upper' k + Problem520.harperCumulativeCellWidth delta k) ↔
      ∀ k, lower k <= Problem520.harperPathPartialSum omega k ∧
        Problem520.harperPathPartialSum omega k <= upper k
    simp only [lower', upper']
    constructor <;> intro h k
    · have hk := h k
      constructor <;> linarith
    · have hk := h k
      constructor <;> linarith
  have hinside : U ⊆
      Problem520.harperPartialSumBarrierSet lower upper := by
    rw [← hexpanded]
    simpa only [U, s] using
      (Problem520.biUnion_activeLatticeSlice_subset_expandedBarrier
        (delta := delta) (R := R) (lower := lower') (upper := upper'))
  calc
    C * Q.real
        (Problem520.harperPartialSumBarrierSet
            (fun k => lower k +
              Problem520.harperCumulativeCellWidth delta k)
            (fun k => upper k -
              Problem520.harperCumulativeCellWidth delta k) ∩
          Problem520.harperCoordinateBox R) =
        C * Q.real
          (Problem520.harperPartialSumBarrierSet lower' upper' ∩
            Problem520.harperCoordinateBox R) := by rfl
    _ <= C * Q.real U :=
      mul_le_mul_of_nonneg_left
        (measureReal_mono hcover (measure_ne_top Q _)) hC
    _ <= P.real U := by simpa only [U] using hunion
    _ <= P.real (Problem520.harperPartialSumBarrierSet lower upper) :=
      measureReal_mono hinside (measure_ne_top P _)

/-- Scheduled reverse ballot comparison.  Apart from contraction by the
summable lattice width and restriction to the standard moderate box, this
loses only the fixed factor `3/4`. -/
theorem exists_eventually_three_fourths_mul_gaussian_contractedBarrier_le_harperScheduledBarrier
    (M : Nat) :
    ∃ J : Nat, ∀ start : Nat, J <= start -> ∀ n y : Nat,
      Problem520.harperBlockEndpoint (start + n) <= y ->
        ∀ t : Real, 1 <= |t| -> |t| <= M ->
          ∀ lower upper : Fin n -> Real,
            (3 / 4 : Real) *
                (Measure.pi (fun i : Fin n =>
                  Problem520.harperGaussianBlockLaw y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + (i : Nat))) t t)).real
                  (Problem520.harperPartialSumBarrierSet
                      (fun k => lower k +
                        Problem520.harperCumulativeCellWidth
                          (Problem520.harperScheduledRelativeCellWidth
                            start n) k)
                      (fun k => upper k -
                        Problem520.harperCumulativeCellWidth
                          (Problem520.harperScheduledRelativeCellWidth
                            start n) k) ∩
                    Problem520.harperCoordinateBox
                      (Problem520.harperScheduledModerateRadius start n)) <=
              (Measure.pi (fun i : Fin n =>
                Problem520.harperCenteredLinearBlockLaw y
                  (Problem520.harperScheduledPrimeBlock y
                    (start + (i : Nat))) t t)).real
                (Problem520.harperPartialSumBarrierSet lower upper) := by
  obtain ⟨Jcell, hcell⟩ :=
    exists_eventually_three_fourths_mul_gaussian_le_harperScheduledModerateCoordinateCell M
  refine ⟨Jcell, ?_⟩
  intro start hstart n y hy t htLower htUpper lower upper
  let delta := Problem520.harperScheduledRelativeCellWidth start n
  let R := Problem520.harperScheduledModerateRadius start n
  let lower' : Fin n -> Real := fun k =>
    lower k + Problem520.harperCumulativeCellWidth delta k
  let upper' : Fin n -> Real := fun k =>
    upper k - Problem520.harperCumulativeCellWidth delta k
  apply const_mul_measureReal_inter_contractedBarrier_box_le_barrier
    (P := Measure.pi (fun i : Fin n =>
      Problem520.harperCenteredLinearBlockLaw y
        (Problem520.harperScheduledPrimeBlock y
          (start + (i : Nat))) t t))
    (Q := Measure.pi (fun i : Fin n =>
      Problem520.harperGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y
          (start + (i : Nat))) t t))
    (C := (3 / 4 : Real)) (delta := delta) (R := R)
    (lower := lower) (upper := upper) (by norm_num)
    (Problem520.harperScheduledRelativeCellWidth_pos start n)
  intro z hz
  apply hcell start hstart n y hy t htLower htUpper z
  intro i
  have hmoderate :=
    Problem520.abs_scheduledLatticeCell_lowerCorner_add_one_le_of_mem_activeSlice
      (start := start) (n := n) (lower := lower') (upper := upper')
      (by simpa only [delta, R, lower', upper'] using hz) i
  simpa only [Problem520.harperScheduledRelativeCellWidth,
    Problem520.harperScheduledModerateThreshold] using hmoderate

/-- The reverse ballot comparison on shrinking central bands.  In
particular, taking `d = 1` covers the nondegenerate Rademacher vertical band
`1/4 < |t| <= 1/2` used in the restricted-energy argument. -/
theorem
    exists_three_fourths_mul_gaussian_contractedBarrier_le_harperScheduledCentralBandBarrier :
    ∃ J : Nat, ∀ d start : Nat, J + d <= start -> ∀ n y : Nat,
      Problem520.harperBlockEndpoint (start + n) <= y ->
        ∀ t : Real,
          (1 / 2 : Real) ^ (d + 1) < |t| ->
          |t| <= (1 / 2 : Real) ^ d ->
            ∀ lower upper : Fin n -> Real,
              (3 / 4 : Real) *
                  (Measure.pi (fun i : Fin n =>
                    Problem520.harperGaussianBlockLaw y
                      (Problem520.harperScheduledPrimeBlock y
                        (start + (i : Nat))) t t)).real
                    (Problem520.harperPartialSumBarrierSet
                        (fun k => lower k +
                          Problem520.harperCumulativeCellWidth
                            (Problem520.harperScheduledRelativeCellWidth
                              start n) k)
                        (fun k => upper k -
                          Problem520.harperCumulativeCellWidth
                            (Problem520.harperScheduledRelativeCellWidth
                              start n) k) ∩
                      Problem520.harperCoordinateBox
                        (Problem520.harperScheduledModerateRadius start n)) <=
                (Measure.pi (fun i : Fin n =>
                  Problem520.harperCenteredLinearBlockLaw y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + (i : Nat))) t t)).real
                  (Problem520.harperPartialSumBarrierSet lower upper) := by
  obtain ⟨Jcell, hcell⟩ :=
    exists_three_fourths_mul_gaussian_le_harperScheduledCentralBandModerateCoordinateCell
  refine ⟨Jcell, ?_⟩
  intro d start hstart n y hy t htLower htUpper lower upper
  let delta := Problem520.harperScheduledRelativeCellWidth start n
  let R := Problem520.harperScheduledModerateRadius start n
  let lower' : Fin n -> Real := fun k =>
    lower k + Problem520.harperCumulativeCellWidth delta k
  let upper' : Fin n -> Real := fun k =>
    upper k - Problem520.harperCumulativeCellWidth delta k
  apply const_mul_measureReal_inter_contractedBarrier_box_le_barrier
    (P := Measure.pi (fun i : Fin n =>
      Problem520.harperCenteredLinearBlockLaw y
        (Problem520.harperScheduledPrimeBlock y
          (start + (i : Nat))) t t))
    (Q := Measure.pi (fun i : Fin n =>
      Problem520.harperGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y
          (start + (i : Nat))) t t))
    (C := (3 / 4 : Real)) (delta := delta) (R := R)
    (lower := lower) (upper := upper) (by norm_num)
    (Problem520.harperScheduledRelativeCellWidth_pos start n)
  intro z hz
  apply hcell d start hstart n y hy t htLower htUpper z
  intro i
  have hmoderate :=
    Problem520.abs_scheduledLatticeCell_lowerCorner_add_one_le_of_mem_activeSlice
      (start := start) (n := n) (lower := lower') (upper := upper')
      (by simpa only [delta, R, lower', upper'] using hz) i
  simpa only [Problem520.harperScheduledRelativeCellWidth,
    Problem520.harperScheduledModerateThreshold] using hmoderate

end Problem1144
end Erdos
