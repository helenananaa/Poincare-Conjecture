import Mathlib
import DoCarmoLib.Riemannian.Connection.ChartChristoffelSmooth
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ChartInverseDifferentialEquivalence
open scoped Topology BigOperators ContDiff Manifold BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem chart_inverse_differential_equivalence
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
    (g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) M) (p : M)
    (y : E3) (hy : y ∈ (extChartAt 𝓘(ℝ, E3) p).target) :

    ∃ L : E3 ≃L[ℝ] TangentSpace 𝓘(ℝ, E3) ((extChartAt 𝓘(ℝ, E3) p).symm y),
      ∀ v : E3, L v=(mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm y) v :=
/- SWARM_PROOF_BEGIN -/
by
  have hA := isInvertible_mfderivWithin_extChartAt_symm
    (I := 𝓘(ℝ, E3)) (x := p) hy
  rcases hA with ⟨L, hL⟩
  let e : TangentSpace 𝓘(ℝ, E3) y ≃L[ℝ] E3 :=
    NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := E3) y
  let L' : E3 ≃L[ℝ] TangentSpace 𝓘(ℝ, E3) ((extChartAt 𝓘(ℝ, E3) p).symm y) :=
    e.symm.trans L
  refine ⟨L', ?_⟩
  intro v
  change L.toContinuousLinearMap (e.symm v) = _
  change L.toContinuousLinearMap = _ at hL
  have hp := congrArg (fun F => F (e.symm v)) hL
  have he : e.symm v = v := rfl
  have hder :
      (mfderivWithin 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm
        (Set.range (𝓘(ℝ, E3))) y) (e.symm v) =
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm y) v := by
    simpa only [modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ] using
      (show (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm y)
          (e.symm v) =
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm y) v by rw [he])
  exact hp.trans hder
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ChartInverseDifferentialEquivalence
