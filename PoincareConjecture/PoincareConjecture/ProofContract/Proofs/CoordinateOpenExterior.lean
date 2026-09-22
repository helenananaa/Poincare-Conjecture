import PoincareConjecture.ProofContract.Proofs.CoordinateBallCellular
import PoincareConjecture.ProofContract.Proofs.NestedCellOpenExterior
import PoincareConjecture.ProofContract.Proofs.SqueezableCompactCollapse
import PoincareConjecture.ProofContract.Proofs.NestedCellSqueeze
import PoincareConjecture.ProofContract.Proofs.CollapseComplementHomeomorph
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
import Mathlib.Geometry.Manifold.Instances.Sphere
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Filter Topology
open scoped Topology Manifold ContDiff
/-- Open complement of an actual closed coordinate ball in a known sphere. -/
theorem coordinate_open_exterior_euclidean (M : ClosedThreeManifold.{u})
    (e : M ≃ₜ Sphere3) (a : CoordinateBall M) :
    Nonempty ({x : M // x ∉ a.parametrization '' Metric.closedBall (0:Euclidean3) 1} ≃ₜ Euclidean3) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨b, hn, hb⟩ := coordinate_closed_ball_cellular a
  rw [← hb]
  exact nested_cell_open_exterior_euclidean M e b hn
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
