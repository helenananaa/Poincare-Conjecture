import ReferenceBridges.WidthTorus.NonSimplyConnected
import ReferenceBridges.WidthTorus.Antipodal
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

/-- The antipodal mapping torus of the actual two-sphere cannot be homeomorphic
to any simply connected space. This does not classify sphere diffeomorphisms. -/
theorem twisted_sphere_bundle_obstruction :
    ∃ a : Sphere2 ≃ₜ Sphere2,
      (∀ x : Sphere2, (a x : EuclideanSpace ℝ (Fin 3)) = -(x : EuclideanSpace ℝ (Fin 3))) ∧
      ∀ (N : Type*) [TopologicalSpace N] [SimplyConnectedSpace N],
        ¬ Nonempty (N ≃ₜ MappingTorus.Space a 1) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨a, ha⟩ := exists_sphere2_antipodal_homeomorph
  refine ⟨a, ha, ?_⟩
  intro N _ _ ⟨e⟩
  haveI : PathConnectedSpace Sphere2 := by
    apply isPathConnected_iff_pathConnectedSpace.mp
    apply isPathConnected_sphere ?_ _ (by norm_num)
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  haveI : Nonempty Sphere2 := PathConnectedSpace.nonempty
  exact mappingTorus_not_simplyConnected a
    (e.toHomotopyEquiv.simplyConnectedSpace_iff.mp inferInstance)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.TorusObstruction
