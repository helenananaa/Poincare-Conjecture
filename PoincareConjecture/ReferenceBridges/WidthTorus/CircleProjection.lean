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

/-- The actual mapping-torus quotient carries its canonical circle projection. -/
theorem mappingTorus_circle_projection {X : Type*} [TopologicalSpace X] (φ : X ≃ₜ X) :
    ∃ P : C(MappingTorus.Space φ 1, HatcherLib.UnitCircle),
      ∀ (x : X) (t : ℝ), P (MappingTorus.proj φ 1 (x,t)) = (t : HatcherLib.UnitCircle) :=
/- SWARM_PROOF_BEGIN -/
by
  have hinv : ∀ p r : X × ℝ, MappingTorus.orbitSetoid φ 1 p r →
      (p.2 : HatcherLib.UnitCircle) = (r.2 : HatcherLib.UnitCircle) := by
    rintro p r ⟨n, rfl⟩
    -- Deck iterate `n` (any integer, not only `±1`) shifts the height by `n * 1`.
    have ht : (MappingTorus.deck φ 1 n p).2 = p.2 + (n : ℝ) * (1 : ℝ) := rfl
    rw [ht]
    rw [← sub_eq_zero, ← AddCircle.coe_sub (1 : ℝ), AddCircle.coe_eq_zero_iff]
    refine ⟨-n, ?_⟩
    simp [zsmul_eq_mul]
  refine ⟨⟨Quotient.lift (fun p : X × ℝ => (p.2 : HatcherLib.UnitCircle)) hinv,
      Continuous.quotient_lift
        ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd) hinv⟩,
    fun _ _ => rfl⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.TorusObstruction
