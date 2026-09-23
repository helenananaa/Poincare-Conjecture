import DoCarmoLib.Riemannian.Manifold.DoCarmoCh6Locality
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
def connectionDifferenceField {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] (nabla nabla0 : Riemannian.AffineConnection (𝓡 3) M)
    (X Y : Riemannian.SmoothVectorField (𝓡 3) M) : Riemannian.SmoothVectorField (𝓡 3) M :=
  nabla.cov X Y - nabla0.cov X Y

/-- **Math.** connection difference field linear. -/
theorem connection_difference_field_linear {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (nabla nabla0 : Riemannian.AffineConnection (𝓡 3) M) :
    (∀ X Y Z, connectionDifferenceField nabla nabla0 (X+Y) Z =
      connectionDifferenceField nabla nabla0 X Z + connectionDifferenceField nabla nabla0 Y Z) ∧
    (∀ X Y Z, connectionDifferenceField nabla nabla0 X (Y+Z) =
      connectionDifferenceField nabla nabla0 X Y + connectionDifferenceField nabla nabla0 X Z) ∧
    (∀ (f : M → ℝ) (hf : ContMDiff (𝓡 3) 𝓘(ℝ) ∞ f) X Y,
      connectionDifferenceField nabla nabla0 (Riemannian.SmoothVectorField.smul f hf X) Y =
        Riemannian.SmoothVectorField.smul f hf (connectionDifferenceField nabla nabla0 X Y)) ∧
    (∀ (f : M → ℝ) (hf : ContMDiff (𝓡 3) 𝓘(ℝ) ∞ f) X Y,
      connectionDifferenceField nabla nabla0 X (Riemannian.SmoothVectorField.smul f hf Y) =
        Riemannian.SmoothVectorField.smul f hf (connectionDifferenceField nabla nabla0 X Y)) :=
/- SWARM_PROOF_BEGIN -/
by
  constructor
  · intro X Y Z
    ext p
    simp only [connectionDifferenceField, Riemannian.SmoothVectorField.sub_apply,
      Riemannian.SmoothVectorField.add_apply, nabla.add_left, nabla0.add_left]
    abel
  constructor
  · intro X Y Z
    ext p
    simp only [connectionDifferenceField, Riemannian.SmoothVectorField.sub_apply,
      Riemannian.SmoothVectorField.add_apply, nabla.add_right, nabla0.add_right]
    abel
  constructor
  · intro f hf X Y
    ext p
    simp only [connectionDifferenceField, Riemannian.SmoothVectorField.sub_apply,
      nabla.smul_left, nabla0.smul_left, Riemannian.SmoothVectorField.smul_apply,
      smul_sub]
  · intro f hf X Y
    ext p
    simp only [connectionDifferenceField, Riemannian.SmoothVectorField.sub_apply,
      nabla.cov_smul_right hf, nabla0.cov_smul_right hf,
      Riemannian.SmoothVectorField.add_apply, Riemannian.SmoothVectorField.smul_apply,
      smul_sub]
    abel
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
