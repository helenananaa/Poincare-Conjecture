import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.FrameInverseCoordinate
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartCurvatureCoefficientSign
import MorganTianLib.Ch03.RicciFlow.CurvatureCoordinateVariation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** chart trace intrinsic ricci. -/
theorem chart_trace_intrinsic_ricci {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (B : E3 ≃L[ℝ] E3)
    (hB : ∀ r : Fin 3, B (EuclideanSpace.single r 1) = Module.finBasis ℝ E3 (e r)) (y : E3) (hy : y ∈ (extChartAt (𝓡 3) a).target) (i j : Fin 3) :
    (∑ k : Fin 3, (B.symm (MorganTianLib.chartCurvature g a y
      (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single j 1))
      (B (EuclideanSpace.single i 1)))) k) =
    MorganTianLib.ricciTensorAt g ((extChartAt (𝓡 3) a).symm y)
      (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) ((extChartAt (𝓡 3) a).symm y))
      (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) ((extChartAt (𝓡 3) a).symm y)) :=
/- SWARM_PROOF_BEGIN -/
by
  have hterm (k : Fin 3) :
      (B.symm (MorganTianLib.chartCurvature g a y
        (B (EuclideanSpace.single k 1))
        (B (EuclideanSpace.single j 1))
        (B (EuclideanSpace.single i 1)))) k =
        Riemannian.Jacobi.chartCurvatureCoef (I := 𝓡 3) g a
          (e j) (e k) (e i) (e k) y := by
    rw [frame_inverse_coordinate e B hB _ k, hB k, hB j, hB i]
    exact chart_curvature_coefficient_sign g a y hy (e k) (e j) (e i) (e k)
  calc
    (∑ k : Fin 3, (B.symm (MorganTianLib.chartCurvature g a y
        (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single j 1))
        (B (EuclideanSpace.single i 1)))) k) =
        ∑ k : Fin 3, Riemannian.Jacobi.chartCurvatureCoef (I := 𝓡 3) g a
          (e j) (e k) (e i) (e k) y := by
      exact Finset.sum_congr rfl fun k _ => hterm k
    _ = MorganTianLib.chartRicciCoefOnE (I := 𝓡 3) g a (e j) (e i) y := by
      rw [MorganTianLib.chartRicciCoefOnE, ← Equiv.sum_comp e]
    _ = MorganTianLib.ricciTensorAt g ((extChartAt (𝓡 3) a).symm y)
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j)
          ((extChartAt (𝓡 3) a).symm y))
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i)
          ((extChartAt (𝓡 3) a).symm y)) :=
      MorganTianLib.chartRicciCoefOnE_eq_ricciTensorAt_chartBasis
        g a (e j) (e i) hy
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
