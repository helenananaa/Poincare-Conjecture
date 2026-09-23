import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ConnectionDifferenceLocality
import MorganTianLib.Ch01.PointwiseCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** connection difference fiber bilinear. -/
theorem connection_difference_fiber_bilinear {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (nabla nabla0 : Riemannian.AffineConnection (𝓡 3) M) (p : M) :
    ∃ D : TangentSpace (𝓡 3) p →ₗ[ℝ] TangentSpace (𝓡 3) p →ₗ[ℝ] TangentSpace (𝓡 3) p,
      ∀ X Y : Riemannian.SmoothVectorField (𝓡 3) M,
        D (X p) (Y p) = connectionDifferenceField nabla nabla0 X Y p :=
/- SWARM_PROOF_BEGIN -/
by
  refine ⟨LinearMap.mk₂ ℝ
    (fun v w => connectionDifferenceField nabla nabla0
      (extendVector p v) (extendVector p w) p)
    ?_ ?_ ?_ ?_, ?_⟩
  · intro v₁ v₂ w
    have hv : (extendVector p (v₁ + v₂)) p =
        (extendVector p v₁ + extendVector p v₂) p := by
      simp only [extendVector_apply, Riemannian.SmoothVectorField.add_apply]
    calc
      connectionDifferenceField nabla nabla0 (extendVector p (v₁ + v₂))
          (extendVector p w) p =
          connectionDifferenceField nabla nabla0
            (extendVector p v₁ + extendVector p v₂) (extendVector p w) p :=
        connection_difference_pointwise nabla nabla0 _ _ _ _ p hv rfl
      _ = connectionDifferenceField nabla nabla0 (extendVector p v₁)
            (extendVector p w) p +
          connectionDifferenceField nabla nabla0 (extendVector p v₂)
            (extendVector p w) p := by
        rw [(connection_difference_field_linear nabla nabla0).1]
        simp only [Riemannian.SmoothVectorField.add_apply]
  · intro c v w
    let X' := Riemannian.SmoothVectorField.smul (fun _ => c) contMDiff_const
      (extendVector p v)
    have hv : (extendVector p (c • v)) p = X' p := by
      simp [X', extendVector_apply, Riemannian.SmoothVectorField.smul_apply]
    calc
      connectionDifferenceField nabla nabla0 (extendVector p (c • v))
          (extendVector p w) p =
          connectionDifferenceField nabla nabla0 X' (extendVector p w) p :=
        connection_difference_pointwise nabla nabla0 _ _ _ _ p hv rfl
      _ = c • connectionDifferenceField nabla nabla0
            (extendVector p v) (extendVector p w) p := by
        rw [(connection_difference_field_linear nabla nabla0).2.2.1]
        simp [Riemannian.SmoothVectorField.smul_apply]
  · intro v w₁ w₂
    have hw : (extendVector p (w₁ + w₂)) p =
        (extendVector p w₁ + extendVector p w₂) p := by
      simp only [extendVector_apply, Riemannian.SmoothVectorField.add_apply]
    calc
      connectionDifferenceField nabla nabla0 (extendVector p v)
          (extendVector p (w₁ + w₂)) p =
          connectionDifferenceField nabla nabla0 (extendVector p v)
            (extendVector p w₁ + extendVector p w₂) p :=
        connection_difference_pointwise nabla nabla0 _ _ _ _ p rfl hw
      _ = connectionDifferenceField nabla nabla0 (extendVector p v)
            (extendVector p w₁) p +
          connectionDifferenceField nabla nabla0 (extendVector p v)
            (extendVector p w₂) p := by
        rw [(connection_difference_field_linear nabla nabla0).2.1]
        simp only [Riemannian.SmoothVectorField.add_apply]
  · intro c v w
    let Y' := Riemannian.SmoothVectorField.smul (fun _ => c) contMDiff_const
      (extendVector p w)
    have hw : (extendVector p (c • w)) p = Y' p := by
      simp [Y', extendVector_apply, Riemannian.SmoothVectorField.smul_apply]
    calc
      connectionDifferenceField nabla nabla0 (extendVector p v)
          (extendVector p (c • w)) p =
          connectionDifferenceField nabla nabla0 (extendVector p v) Y' p :=
        connection_difference_pointwise nabla nabla0 _ _ _ _ p rfl hw
      _ = c • connectionDifferenceField nabla nabla0
            (extendVector p v) (extendVector p w) p := by
        rw [(connection_difference_field_linear nabla nabla0).2.2.2]
        simp [Riemannian.SmoothVectorField.smul_apply]
  · intro X Y
    change connectionDifferenceField nabla nabla0
      (extendVector p (X p)) (extendVector p (Y p)) p =
      connectionDifferenceField nabla nabla0 X Y p
    exact connection_difference_pointwise nabla nabla0 _ _ _ _ p
      (by simp) (by simp)
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
