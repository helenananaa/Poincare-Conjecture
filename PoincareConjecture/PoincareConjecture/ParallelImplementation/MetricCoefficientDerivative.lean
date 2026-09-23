import PoincareConjecture.ParallelImplementation.BilinearDerivativeLift
import MorganTianLib.Ch03.RicciFlow.MetricVariation
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Riemannian Bundle MorganTianLib
open scoped Manifold Topology ContDiff Bundle
namespace PoincareConjecture.ParallelImplementation.MetricCoefficientDerivative
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
/-- Construct the actual operator derivative, rather than assume its existence. -/
theorem metricCoefficient_hasDerivWithinAt_of_variation
    (g : ℝ → MorganTianLib.RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (J : Set ℝ) (hJ : ∀ t ∈ J, UniqueDiffWithinAt ℝ J t)
    (hvar : IsMetricVariationOn g h J) (t₀ : ℝ) (ht₀ : t₀ ∈ J) (p : M) :
    ∃ dh : TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ,
      (∀ x y, dh x y = h t₀ p x y) ∧
      HasDerivWithinAt (fun t => (g t).inner p) dh J t₀ :=
/- SWARM_PROOF_BEGIN -/
by
  let V := TangentSpace I p
  let D : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun x y => h t₀ p x y)
      (by
        intro x x' y
        exact isMetricVariationOn_add_left hJ hvar t₀ ht₀ p x x' y)
      (by
        intro c x y
        simpa only [smul_eq_mul] using
          isMetricVariationOn_smul_left hJ hvar t₀ ht₀ p c x y)
      (by
        intro x y y'
        exact isMetricVariationOn_add_right hJ hvar t₀ ht₀ p x y y')
      (by
        intro c x y
        simpa only [smul_eq_mul] using
          isMetricVariationOn_smul_right hJ hvar t₀ ht₀ p c x y)
  let D₁ : V →ₗ[ℝ] V →L[ℝ] ℝ :=
    { toFun := fun x => (D x).toContinuousLinearMap
      map_add' := by
        intro x x'
        ext y
        simp [D]
      map_smul' := by
        intro c x
        ext y
        simp [D] }
  let dh : V →L[ℝ] V →L[ℝ] ℝ := D₁.toContinuousLinearMap
  have hEval : ∀ x y, dh x y = h t₀ p x y := by
    intro x y
    simp [dh, D₁, D]
  refine ⟨dh, hEval, ?_⟩
  apply PoincareConjecture.ParallelImplementation.IndependentAlgebra.hasDerivWithinAt_bilinear_of_evaluations
  intro x y
  rw [hEval x y]
  exact hvar t₀ ht₀ p x y
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.MetricCoefficientDerivative
