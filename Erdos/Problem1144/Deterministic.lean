import Erdos.Problem1144.Targets

open MeasureTheory Filter

namespace Erdos
namespace Problem1144

/-- Cubic-over-quadratic certificate along the sparse scales. -/
def CubicRatioCert (omega : Omega) : Prop :=
  ∀ B : ℝ, ∃ᶠ j : ℕ in atTop,
    B ≤ Cub omega (Rseq j) / (1 + Quad omega (Rseq j))

/-- Pointwise deterministic reduction from the cubic certificate to positive limsup.

The intended proof is by contradiction: if `Y omega r <= A` eventually, set
`K = max A 1`; then eventually `Y^3 <= K * Y^2`, hence
`Cub R <= O_omega(1) + K * Quad R`, contradicting unbounded
`Cub / (1 + Quad)`.
-/
axiom squareTarget_pointwise_of_cubicRatioCert
  (omega : Omega) :
  CubicRatioCert omega →
    ∀ A : ℝ, ∃ᶠ r : ℕ in atTop, A ≤ Y omega r

/-- Almost-sure deterministic reduction. -/
theorem squareTarget_of_cubicRatioCert
    (h : ∀ᵐ omega ∂mu, CubicRatioCert omega) :
    SquareTarget :=
  h.mono fun omega homega => squareTarget_pointwise_of_cubicRatioCert omega homega

end Problem1144
end Erdos
