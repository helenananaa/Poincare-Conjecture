import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.NeckAdapter
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Positive or negative axial affine normalization preserves the given smooth structures. -/
theorem exists_axial_affine_diffeomorph {V H X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (I : ModelWithCorners ℝ V H) [IsManifold I ∞ X]
    (c r : ℝ) (hr : r ≠ 0) :
    ∃ e : (X × ℝ) ≃ₘ⟮I.prod (𝓘(ℝ, ℝ)), I.prod (𝓘(ℝ, ℝ))⟯ (X × ℝ),
      (∀ z, e z = (z.1, c + r*z.2)) ∧
      (∀ z, e.symm z = (z.1, (z.2-c)/r)) :=
/- SWARM_PROOF_BEGIN -/
by
  let eR : ℝ ≃ₘ[ℝ] ℝ :=
    { toFun := fun t => c + r * t
      invFun := fun t => (t - c) / r
      left_inv := fun t => by
        change (c + r * t - c) / r = t
        rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hr]
      right_inv := fun t => by
        change c + r * ((t - c) / r) = t
        rw [mul_div_cancel₀ _ hr, add_sub_cancel]
      contMDiff_toFun :=
        (show ContDiff ℝ ∞ (fun t : ℝ => c + r * t) by fun_prop).contMDiff
      contMDiff_invFun :=
        (show ContDiff ℝ ∞ (fun t : ℝ => (t - c) / r) by fun_prop).contMDiff }
  refine ⟨(Diffeomorph.refl I X ∞).prodCongr eR, ?_, ?_⟩
  · intro z
    rfl
  · intro z
    rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.NeckAdapter
