import PoincareConjecture.Topology.FiberSaturation.MappingTorus
import PoincareConjecture.Topology.FiberSaturation.Sphere
import HatcherLib.Ch1.Circle
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.TorusObstruction
open Set Function
open scoped Topology unitInterval
open PoincareConjecture.Topology.FiberSaturation

/-- The actual standard two-sphere admits its explicit antipodal homeomorphism. -/
theorem exists_sphere2_antipodal_homeomorph :
    ∃ a : Sphere2 ≃ₜ Sphere2, ∀ x : Sphere2,
      (a x : EuclideanSpace ℝ (Fin 3)) = -(x : EuclideanSpace ℝ (Fin 3)) :=
/- SWARM_PROOF_BEGIN -/
by
  let a : Sphere2 ≃ₜ Sphere2 :=
    (Homeomorph.neg (EuclideanSpace ℝ (Fin 3))).sets <| by
      ext x
      simp [norm_neg]
  refine ⟨a, ?_⟩
  intro x
  rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.TorusObstruction
