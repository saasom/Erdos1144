import Erdos.Problem1144.Deterministic

open MeasureTheory Filter

namespace Erdos
namespace Problem1144

/-- Finite moment concentration certificate for the cubic statistic. -/
structure MomentConcentration where
  c : ℝ
  C : ℝ
  c_pos : 0 < c
  C_nonneg : 0 ≤ C
  mean_cub :
    ∀ᶠ j in atTop,
      c * (Lseq j) ^ 4 ≤ ∫ omega, Cub omega (Rseq j) ∂mu
  var_cub :
    ∀ᶠ j in atTop,
      ∫ omega,
        (Cub omega (Rseq j) -
          ∫ omega', Cub omega' (Rseq j) ∂mu) ^ 2 ∂mu
      ≤ C * (Lseq j) ^ 7
  mean_quad :
    ∀ᶠ j in atTop,
      ∫ omega, Quad omega (Rseq j) ∂mu
      ≤ C * (Lseq j) ^ 2

/-- Chebyshev, Markov, summability of `2^{-j}`, and Borel-Cantelli.

No multiplicative number theory should enter this theorem.
-/
axiom cubicRatioCert_of_momentConcentration
  (h : MomentConcentration) :
  ∀ᵐ omega ∂mu, CubicRatioCert omega

end Problem1144
end Erdos
