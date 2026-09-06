import Erdos.Shared.Basic

namespace Erdos
namespace Problem1144

/-!
Common namespace for Erdős problem #1144.

The problem-specific architecture is split across:

* `Model`: the coin space, infinite product measure, and random
  multiplicative function.
* `Statistics`: `S`, the square-subsequence normalization `Y`, and the
  logarithmic quadratic/cubic statistics.
* `Targets`: the final target and square-subsequence target.
* `PositiveBlockCertificate`: the active positive-block closure interface.
* `Deterministic`: the cubic-over-quadratic certificate.
* `MomentConcentration`: the finite moment concentration bridge.
* `Orthogonality` and `Counting`: the algebraic-probabilistic/counting layer.
* `SquareConvolution` and `Resonator`: research scaffolds for removing the
  active resonator block-estimate axiom.
* `Final`: the theorem wiring, currently using the resonator block-estimate
  axiom.
-/

end Problem1144
end Erdos
