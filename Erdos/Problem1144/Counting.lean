import Erdos.Problem1144.MomentConcentration
import Erdos.Problem1144.Orthogonality

open MeasureTheory Filter
open scoped BigOperators

namespace Erdos
namespace Problem1144

/-- Weighted count of square-product pairs in `[1, X]^2`. -/
noncomputable def squarePairCount (X : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X,
    ∑ b ∈ Finset.Icc 1 X,
      squareIndicator (a * b)

/-- Weighted count of square-product triples in `[1, X]^3`. -/
noncomputable def squareTripleCount (X : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X,
    ∑ b ∈ Finset.Icc 1 X,
      ∑ c ∈ Finset.Icc 1 X,
        squareIndicator (a * b * c)

/-- Weighted count of square-product sextuples with three variables at each scale. -/
noncomputable def squareSextupleCount (X Y : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X,
    ∑ b ∈ Finset.Icc 1 X,
      ∑ c ∈ Finset.Icc 1 X,
        ∑ d ∈ Finset.Icc 1 Y,
          ∑ e ∈ Finset.Icc 1 Y,
            ∑ h ∈ Finset.Icc 1 Y,
              squareIndicator (a * b * c * d * e * h)

/-- Sextuple count after subtracting the independent square-triple contribution. -/
noncomputable def cubicCovarianceCount (r s : ℕ) : ℝ :=
  squareSextupleCount ((r + 1) ^ 2) ((s + 1) ^ 2) -
    squareTripleCount ((r + 1) ^ 2) * squareTripleCount ((s + 1) ^ 2)

axiom mean_Y_sq_counting_identity (r : ℕ) :
  ∫ omega, (Y omega r) ^ 2 ∂mu =
    squarePairCount ((r + 1) ^ 2) / ((((r + 1 : ℕ) : ℝ)) ^ 2)

axiom mean_Y_cub_counting_identity (r : ℕ) :
  ∫ omega, (Y omega r) ^ 3 ∂mu =
    squareTripleCount ((r + 1) ^ 2) / ((((r + 1 : ℕ) : ℝ)) ^ 3)

axiom mean_quad_counting_identity (R : ℕ) :
  ∫ omega, Quad omega R ∂mu =
    ∑ r ∈ Finset.range R,
      squarePairCount ((r + 1) ^ 2) / ((((r + 1 : ℕ) : ℝ)) ^ 3)

axiom mean_cub_counting_identity (R : ℕ) :
  ∫ omega, Cub omega R ∂mu =
    ∑ r ∈ Finset.range R,
      squareTripleCount ((r + 1) ^ 2) / ((((r + 1 : ℕ) : ℝ)) ^ 4)

axiom var_cub_counting_identity (R : ℕ) :
  ∫ omega,
    (Cub omega R - ∫ omega', Cub omega' R ∂mu) ^ 2 ∂mu =
    ∑ r ∈ Finset.range R,
      ∑ s ∈ Finset.range R,
        cubicCovarianceCount r s /
          (((((r + 1 : ℕ) : ℝ)) ^ 4) * ((((s + 1 : ℕ) : ℝ)) ^ 4))

/-- Purely finite counting estimates sufficient for `MomentConcentration`. -/
structure CountingEstimates where
  c : ℝ
  C : ℝ
  c_pos : 0 < c
  C_nonneg : 0 ≤ C
  cub_lower :
    ∀ᶠ j in atTop,
      c * (Lseq j) ^ 4 ≤
        ∑ r ∈ Finset.range (Rseq j),
          squareTripleCount ((r + 1) ^ 2) / ((((r + 1 : ℕ) : ℝ)) ^ 4)
  cub_var_upper :
    ∀ᶠ j in atTop,
      ∑ r ∈ Finset.range (Rseq j),
        ∑ s ∈ Finset.range (Rseq j),
          cubicCovarianceCount r s /
            (((((r + 1 : ℕ) : ℝ)) ^ 4) * ((((s + 1 : ℕ) : ℝ)) ^ 4))
      ≤ C * (Lseq j) ^ 7
  quad_upper :
    ∀ᶠ j in atTop,
      ∑ r ∈ Finset.range (Rseq j),
        squarePairCount ((r + 1) ^ 2) / ((((r + 1 : ℕ) : ℝ)) ^ 3)
      ≤ C * (Lseq j) ^ 2

/-- Counting estimates imply the finite moment concentration certificate. -/
axiom momentConcentration_of_countingEstimates
  (h : CountingEstimates) :
  MomentConcentration

end Problem1144
end Erdos
