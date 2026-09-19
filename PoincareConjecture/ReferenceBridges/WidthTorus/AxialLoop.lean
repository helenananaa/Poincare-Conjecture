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

/-- A path from x to its monodromy image closes to a real loop in the quotient. -/
theorem mappingTorus_axial_loop {X : Type*} [TopologicalSpace X]
    (φ : X ≃ₜ X) (x : X) (γ : Path x (φ x)) :
    ∃ q : Path (MappingTorus.proj φ 1 (x,0)) (MappingTorus.proj φ 1 (x,0)),
      ∀ t : unitInterval, q t = MappingTorus.proj φ 1 (γ t,(t : ℝ)) :=
/- SWARM_PROOF_BEGIN -/
by
  -- The cylinder path `t ↦ (γ t, t)` runs from `(x,0)` to `(φ x,1)`.
  -- Its image under the continuous quotient projection is a loop because
  -- `(φ x,1)` is the `n = 1` deck translate of `(x,0)`, matching the
  -- stored convention `(x,t) ~ (φ x, t+1)`.
  refine ⟨{
    toFun := fun t => MappingTorus.proj φ 1 (γ t, (t : ℝ))
    continuous_toFun :=
      (MappingTorus.continuous_proj φ 1).comp
        (γ.continuous.prodMk continuous_subtype_val)
    source' := by simp [γ.source]
    target' := by
      have hdeck : MappingTorus.deck φ 1 1 (x, 0) = (φ x, (1 : ℝ)) := by
        simp [MappingTorus.deck]
      simpa [γ.target, hdeck] using MappingTorus.proj_deck φ 1 1 (x, 0)
  }, fun _ => rfl⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.TorusObstruction
