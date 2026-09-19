import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.NeckAdapter
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- A compact cross-section in an actual open neck has a closed embedded central slice. -/
theorem neck_central_slice_isClosedEmbedding
    {X N : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace N] [T2Space N]
    (F : OpenPartialHomeomorph (X × ℝ) N) (c : ℝ)
    (hcenter : ∀ x : X, (x,c) ∈ F.source) :
    Topology.IsClosedEmbedding (fun x : X => F (x,c)) :=
/- SWARM_PROOF_BEGIN -/
by
  have hcont : Continuous (fun x : X => F (x, c)) :=
    F.continuousOn.comp_continuous (Continuous.prodMk_left c) hcenter
  have hinj : Injective (fun x : X => F (x, c)) := by
    intro x y hxy
    exact congrArg Prod.fst (F.injOn (hcenter x) (hcenter y) hxy)
  exact hcont.isClosedEmbedding hinj
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.NeckAdapter
