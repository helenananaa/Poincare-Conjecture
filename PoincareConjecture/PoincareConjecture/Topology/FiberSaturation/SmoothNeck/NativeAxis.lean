import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.Core
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothNeck
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Preserve the standard smooth sphere and convert only the one-dimensional
Euclidean axis, followed by the reference product-to-R3 model transport. -/
theorem exists_native_axis_diffeomorph :
    ∃ e : Diffeomorph ((𝓡 2).prod (𝓘(ℝ,ℝ))) NativeCylinderModel
        (Sphere2 × ℝ) NativeCylinder ∞,
      ∀ z, e z = (z.1, nativeAxis z.2) :=
/- SWARM_PROOF_BEGIN -/
by
  let eAxis : ℝ ≃L[ℝ] NativeAxis :=
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm
  let eSwap₁ := Diffeomorph.prodComm (𝓡 2) 𝓘(ℝ, ℝ) Sphere2 ℝ ∞
  let eProd :=
    eAxis.toDiffeomorph.prodCongr (Diffeomorph.refl (𝓡 2) Sphere2 ∞)
  let eSwap₂ := Diffeomorph.prodComm (𝓡 1) (𝓡 2) NativeAxis Sphere2 ∞
  let eId :=
    ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞)
      NativeProductModel NativeCylinder nativeModelEquiv
  refine ⟨eSwap₁.trans (eProd.trans (eSwap₂.trans eId)), ?_⟩
  intro z
  rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothNeck
