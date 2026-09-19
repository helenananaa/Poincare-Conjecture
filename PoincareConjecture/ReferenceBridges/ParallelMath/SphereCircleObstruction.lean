import ReferenceBridges.ParallelMath.SphereCircleGroup
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Reference
open Set Function Filter
open scoped BigOperators Topology Manifold ContDiff Bundle RealInnerProductSpace

/-- A simply connected space cannot be homeomorphic to the product sphere bundle. -/
theorem no_homeomorph_to_sphere2_circle
    {N : Type*} [TopologicalSpace N] [SimplyConnectedSpace N] :
    ¬ Nonempty (N ≃ₜ
      (PoincareConjecture.Topology.FiberSaturation.Sphere2 × HatcherLib.UnitCircle)) :=
/- SWARM_PROOF_BEGIN -/
by
  rintro ⟨e⟩
  haveI : SimplyConnectedSpace
      (PoincareConjecture.Topology.FiberSaturation.Sphere2 × HatcherLib.UnitCircle) :=
    e.toHomotopyEquiv.simplyConnectedSpace_iff.mp inferInstance
  let x : PoincareConjecture.Topology.FiberSaturation.Sphere2 :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨φ⟩ := sphere2_circle_fundamentalGroup x
  have hsub : Subsingleton (Multiplicative ℤ) :=
    φ.toEquiv.subsingleton_congr.mp inferInstance
  exact not_subsingleton (Multiplicative ℤ) hsub
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Reference
