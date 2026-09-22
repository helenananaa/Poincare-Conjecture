import PoincareConjecture.ProofContract.Proofs.PuncturedSphereEuclidean
import PoincareConjecture.ProofContract.Proofs.NestedCellsActualCollapse
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
/-- The open exterior of an actual nested cell intersection in a sphere is Euclidean. -/
theorem nested_cell_open_exterior_euclidean (M : ClosedThreeManifold.{u})
    (e : M ≃ₜ Sphere3) (b : ℕ → CoordinateBall M)
    (hn : ∀ n, (b (n+1)).parametrization '' Metric.closedBall (0:Euclidean3) 1 ⊆ (b n).removed) :
    Nonempty ({x : M // x ∉ (⋂ n, (b n).parametrization '' Metric.closedBall (0:Euclidean3) 1)} ≃ₜ Euclidean3) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨hK, q, hq, hqsurj, hqfib⟩ := nested_cells_actual_collapse M b hn
  obtain ⟨k, hk⟩ := hK
  obtain ⟨c, hc⟩ := collapse_complement_homeomorph
    (⋂ n, (b n).parametrization '' Metric.closedBall (0 : Euclidean3) 1)
    q hq hqsurj k hk hqfib
  have hpunct : ∀ x : M, x ≠ q k ↔ e x ≠ e (q k) := by
    intro x
    constructor
    · intro hx hxe
      apply hx
      exact e.injective hxe
    · intro hx hxe
      apply hx
      exact congrArg e hxe
  let er : {y : M // y ≠ q k} ≃ₜ {z : Sphere3 // z ≠ e (q k)} :=
    e.subtype hpunct
  obtain ⟨s⟩ := punctured_sphere3_euclidean (e (q k))
  exact ⟨c.trans (er.trans s)⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
