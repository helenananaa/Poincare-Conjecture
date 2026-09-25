import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import MorganTianLib.Ch03.RicciFlow.Basic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.IntrinsicRicciEndomorphism
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem ricci_eq_curvature_trace
    (g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3) (x v w : E3) :

    ∃ A : E3 →ₗ[ℝ] E3,
      (∀ z : E3, A z = g.leviCivitaConnection.curvatureOperatorAt x v z w) ∧
      MorganTianLib.ricciTensorAt g x v w = LinearMap.trace ℝ E3 A :=
/- SWARM_PROOF_BEGIN -/
 open scoped Bundle in by
  letI : NormedAddCommGroup (TangentSpace (𝓘(ℝ, E3)) x) :=
    (g.toRiemannianMetric.toCore x).toNormedAddCommGroupOfTopology
      (g.toRiemannianMetric.continuousAt x) (g.toRiemannianMetric.isVonNBounded x)
  letI : InnerProductSpace ℝ (TangentSpace (𝓘(ℝ, E3)) x) :=
    InnerProductSpace.ofCoreOfTopology (g.toRiemannianMetric.toCore x)
      (g.toRiemannianMetric.continuousAt x) (g.toRiemannianMetric.isVonNBounded x)
  letI : Bundle.RiemannianBundle (TangentSpace (𝓘(ℝ, E3)) : E3 → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y Z q => g.koszulDualSection_dual X Y Z q)
  let hB : Riemannian.IsAlgCurvatureForm
      (g.leviCivitaConnection.curvatureFormAt g x) :=
    g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g hLC x
  let β : (TangentSpace (𝓘(ℝ, E3)) x) →ₗ[ℝ]
      (TangentSpace (𝓘(ℝ, E3)) x →ₗ[ℝ] ℝ) :=
    Riemannian.ricciBilinAux hB v w
  let A : E3 →ₗ[ℝ] E3 :=
    (Riemannian.rieszInvEquiv (TangentSpace (𝓘(ℝ, E3)) x)).toLinearMap ∘ₗ β
  have hA : ∀ z : TangentSpace (𝓘(ℝ, E3)) x,
      A z = g.leviCivitaConnection.curvatureOperatorAt x v z w := by
    intro z
    apply (g.metricInner_eq_iff_eq x _ _).mp
    intro u
    change inner ℝ (Riemannian.rieszInvEquiv (TangentSpace (𝓘(ℝ, E3)) x)
      (β z)) u = inner ℝ
        (g.leviCivitaConnection.curvatureOperatorAt x v z w) u
    rw [Riemannian.rieszInvEquiv_inner]
    rfl
  refine ⟨A, hA, ?_⟩
  change Riemannian.ricciBilin hB v w = LinearMap.trace ℝ E3 A
  rw [Riemannian.ricciBilin_apply]
  rw [Riemannian.ricciForm, Riemannian.bilinTrace]
  change LinearMap.trace ℝ E3
      ((Riemannian.rieszInvEquiv (TangentSpace (𝓘(ℝ, E3)) x)).toLinearMap ∘ₗ β) =
    LinearMap.trace ℝ E3 A
  congr 1
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.IntrinsicRicciEndomorphism
