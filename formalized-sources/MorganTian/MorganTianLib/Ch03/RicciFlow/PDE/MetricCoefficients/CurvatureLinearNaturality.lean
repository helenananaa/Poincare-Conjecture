import MorganTianLib.Ch01.CurvatureCommutation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** curvature linear naturality. -/
theorem curvature_linear_naturality (Γ Γ₂ : E3 → E3 →L[ℝ] E3 →L[ℝ] E3) (B : E3 ≃L[ℝ] E3)
    (x : E3) (hΓ : DifferentiableAt ℝ Γ x) (hΓ₂ : DifferentiableAt ℝ Γ₂ (B x))
    (hrel : ∀ᶠ y : E3 in 𝓝 x, ∀ U V : E3, B (Γ y U V) = Γ₂ (B y) (B U) (B V))
    (X Y Z : E3) :
    B (MorganTianLib.christoffelCurvature Γ x X Y Z) =
      MorganTianLib.christoffelCurvature Γ₂ (B x) (B X) (B Y) (B Z) :=
/- SWARM_PROOF_BEGIN -/
by
  have hBdiff (z : E3) : DifferentiableAt ℝ (fun y : E3 => B y) z := by
    exact B.toContinuousLinearMap.isBoundedLinearMap.differentiableAt
  have hBderiv (z : E3) :
      fderiv ℝ (fun y : E3 => B y) z = B.toContinuousLinearMap := by
    exact B.toContinuousLinearMap.isBoundedLinearMap.fderiv
  have hΓeval (U V W : E3) :
      DifferentiableAt ℝ (fun y : E3 => Γ y U V) x ∧
      fderiv ℝ (fun y : E3 => Γ y U V) x W = fderiv ℝ Γ x W U V := by
    have hU : DifferentiableAt ℝ (fun y : E3 => Γ y U) x :=
      hΓ.clm_apply (differentiableAt_const U)
    have hUV : DifferentiableAt ℝ (fun y : E3 => Γ y U V) x :=
      hU.clm_apply (differentiableAt_const V)
    refine ⟨hUV, ?_⟩
    rw [fderiv_clm_apply hU (differentiableAt_const V)]
    rw [fderiv_clm_apply hΓ (differentiableAt_const U)]
    simp
  have hΓ₂eval (U V W : E3) :
      DifferentiableAt ℝ (fun y : E3 => Γ₂ y U V) (B x) ∧
      fderiv ℝ (fun y : E3 => Γ₂ y U V) (B x) W =
        fderiv ℝ Γ₂ (B x) W U V := by
    have hU : DifferentiableAt ℝ (fun y : E3 => Γ₂ y U) (B x) :=
      hΓ₂.clm_apply (differentiableAt_const U)
    have hUV : DifferentiableAt ℝ (fun y : E3 => Γ₂ y U V) (B x) :=
      hU.clm_apply (differentiableAt_const V)
    refine ⟨hUV, ?_⟩
    rw [fderiv_clm_apply hU (differentiableAt_const V)]
    rw [fderiv_clm_apply hΓ₂ (differentiableAt_const U)]
    simp
  have hpoint := hrel.self_of_nhds
  have hderiv (U V W : E3) :
      B (fderiv ℝ Γ x W U V) = fderiv ℝ Γ₂ (B x) (B W) (B U) (B V) := by
    have hfun : (fun y : E3 => B (Γ y U V)) =ᶠ[𝓝 x]
        (fun y : E3 => Γ₂ (B y) (B U) (B V)) := by
      filter_upwards [hrel] with y hy
      exact hy U V
    have hleft :
        fderiv ℝ (fun y : E3 => B (Γ y U V)) x =
          (fderiv ℝ (fun z : E3 => B z) (Γ x U V)).comp
            (fderiv ℝ (fun y : E3 => Γ y U V) x) := by
      exact fderiv_comp (x := x) (f := fun y : E3 => Γ y U V)
        (g := fun z : E3 => B z) (hBdiff (Γ x U V)) (hΓeval U V W).1
    have hright :
        fderiv ℝ (fun y : E3 => Γ₂ (B y) (B U) (B V)) x =
          (fderiv ℝ (fun z : E3 => Γ₂ z (B U) (B V)) (B x)).comp
            (fderiv ℝ (fun y : E3 => B y) x) := by
      exact fderiv_comp (x := x) (f := fun y : E3 => B y)
        (g := fun z : E3 => Γ₂ z (B U) (B V))
        (hΓ₂eval (B U) (B V) (B W)).1 (hBdiff x)
    have hleftW :
        (fderiv ℝ (fun y : E3 => B (Γ y U V)) x) W =
          B (fderiv ℝ Γ x W U V) := by
      rw [hleft, ContinuousLinearMap.comp_apply, hBderiv (Γ x U V),
        (hΓeval U V W).2]
      rfl
    have hrightW :
        (fderiv ℝ (fun y : E3 => Γ₂ (B y) (B U) (B V)) x) W =
          fderiv ℝ Γ₂ (B x) (B W) (B U) (B V) := by
      rw [hright, ContinuousLinearMap.comp_apply, hBderiv x]
      change fderiv ℝ (fun z : E3 => Γ₂ z (B U) (B V)) (B x) (B W) = _
      exact (hΓ₂eval (B U) (B V) (B W)).2
    have heq := congrArg (fun D : E3 →L[ℝ] E3 => D W) hfun.fderiv_eq
    calc
      B (fderiv ℝ Γ x W U V) = (fderiv ℝ (fun y : E3 => B (Γ y U V)) x) W := hleftW.symm
      _ = (fderiv ℝ (fun y : E3 => Γ₂ (B y) (B U) (B V)) x) W := heq
      _ = fderiv ℝ Γ₂ (B x) (B W) (B U) (B V) := hrightW
  have hquad₁ : B (Γ x X (Γ x Y Z)) =
      Γ₂ (B x) (B X) (Γ₂ (B x) (B Y) (B Z)) := by
    calc
      B (Γ x X (Γ x Y Z)) = Γ₂ (B x) (B X) (B (Γ x Y Z)) := hpoint X (Γ x Y Z)
      _ = Γ₂ (B x) (B X) (Γ₂ (B x) (B Y) (B Z)) := by rw [hpoint Y Z]
  have hquad₂ : B (Γ x Y (Γ x X Z)) =
      Γ₂ (B x) (B Y) (Γ₂ (B x) (B X) (B Z)) := by
    calc
      B (Γ x Y (Γ x X Z)) = Γ₂ (B x) (B Y) (B (Γ x X Z)) := hpoint Y (Γ x X Z)
      _ = Γ₂ (B x) (B Y) (Γ₂ (B x) (B X) (B Z)) := by rw [hpoint X Z]
  simp only [MorganTianLib.christoffelCurvature, map_sub, map_add]
  rw [hderiv Y Z X, hderiv X Z Y, hquad₁, hquad₂]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
