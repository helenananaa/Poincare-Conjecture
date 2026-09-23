import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualChartRicci
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartTraceIntrinsicRicci
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** actual coordinate ricci eq intrinsic. -/
theorem actual_coordinate_ricci_eq_intrinsic {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (B : E3 ≃L[ℝ] E3)
    (hB : ∀ r : Fin 3, B (EuclideanSpace.single r 1) = Module.finBasis ℝ E3 (e r)) (x : E3) (hx : B x ∈ (extChartAt (𝓡 3) a).target) (i j : Fin 3) :
    let p := (extChartAt (𝓡 3) a).symm (B x);
    let G : E3 → (E3 →L[ℝ] E3) := fun z =>
      chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm (B z)) e;
    actualCoordinateRicci G x i j = MorganTianLib.ricciTensorAt g p
      (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p)
      (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p) :=
/- SWARM_PROOF_BEGIN -/
by
  change actualCoordinateRicci (fun z : E3 =>
      chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm (B z)) e) x i j =
    MorganTianLib.ricciTensorAt g ((extChartAt (𝓡 3) a).symm (B x))
      (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j)
        ((extChartAt (𝓡 3) a).symm (B x)))
      (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i)
        ((extChartAt (𝓡 3) a).symm (B x)))
  calc
    actualCoordinateRicci (fun z : E3 =>
        chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm (B z)) e) x i j =
        ∑ k : Fin 3, (B.symm (MorganTianLib.chartCurvature g a (B x)
          (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single j 1))
          (B (EuclideanSpace.single i 1)))) k :=
      actual_chart_ricci_contraction g a e B hB x hx i j
    _ = MorganTianLib.ricciTensorAt g ((extChartAt (𝓡 3) a).symm (B x))
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j)
          ((extChartAt (𝓡 3) a).symm (B x)))
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i)
          ((extChartAt (𝓡 3) a).symm (B x))) :=
      chart_trace_intrinsic_ricci g a e B hB (B x) hx i j
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
