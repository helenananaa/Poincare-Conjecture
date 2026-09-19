import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.Core
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothNeck
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- A nondegenerate axial translation/scaling with its exact inverse. -/
theorem exists_affine_axis_diffeomorph (c a : ℝ) (ha : a ≠ 0) :
    ∃ e : ℝ ≃ₘ[ℝ] ℝ, (∀ t, e t = c + a*t) ∧
      (∀ t, e.symm t = (t-c)/a) :=
/- SWARM_PROOF_BEGIN -/
by
  let e₀ : ℝ ≃ ℝ :=
    { toFun := fun t => c + a * t
      invFun := fun t => (t - c) / a
      left_inv := by
        intro t
        field_simp [ha]
        ring
      right_inv := by
        intro t
        field_simp [ha]
        ring }
  refine ⟨{ toEquiv := e₀
            contMDiff_toFun := by
              change ContMDiff _ _ ∞ (fun t : ℝ => c + a * t)
              apply ContDiff.contMDiff
              fun_prop
            contMDiff_invFun := by
              change ContMDiff _ _ ∞ (fun t : ℝ => (t - c) / a)
              apply ContDiff.contMDiff
              fun_prop }, ?_, ?_⟩
  · intro t; rfl
  · intro t; rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothNeck
