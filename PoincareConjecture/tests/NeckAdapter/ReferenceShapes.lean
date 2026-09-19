import MorganTianLib.Ch02.EpsilonNeck
import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothNeck
/-- Definitional compatibility with the actual imported reference-source API. -/
theorem native_neck_reference_shapes :
    Sphere2 = MorganTianLib.EpsilonNeckSphere ∧
    NativeCylinderModel = MorganTianLib.EpsilonNeckCylinderModel ∧
    (∀ epsilon : ℝ, nativeNeckDomain epsilon = MorganTianLib.epsilonNeckDomain epsilon) := by
  exact ⟨rfl, rfl, fun _ => rfl⟩
end PoincareConjecture.Topology.FiberSaturation.SmoothNeck
