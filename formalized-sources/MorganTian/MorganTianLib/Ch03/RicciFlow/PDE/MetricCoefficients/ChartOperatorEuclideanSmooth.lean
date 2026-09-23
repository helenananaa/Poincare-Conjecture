import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartCoefficientOperator
import DoCarmoLib.Riemannian.Connection.ChartChristoffelSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Smoothness of the actual coefficient operator in Euclidean chart coordinates. -/
theorem chart_operator_contDiffAt {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (y : E3)
    (hy : y ∈ (extChartAt (𝓡 3) a).target) :
    ContDiffAt ℝ ∞ (fun z : E3 => chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm z) e) y :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  letI : TopologicalSpace (Matrix (Fin 3) (Fin 3) ℝ) := Pi.topologicalSpace
  letI : NormedAddCommGroup (Matrix (Fin 3) (Fin 3) ℝ) := Pi.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin 3) (Fin 3) ℝ) := Pi.normedSpace
  let G : E3 → Matrix (Fin 3) (Fin 3) ℝ := fun z i j =>
    Riemannian.chartGramOnE (I := 𝓡 3) g a (e i) (e j) z
  have hG : ContDiffOn ℝ ∞ G (extChartAt (𝓡 3) a).target := by
    change ContDiffOn ℝ ∞
      (fun z i j => Riemannian.chartGramOnE (I := 𝓡 3) g a (e i) (e j) z)
      (extChartAt (𝓡 3) a).target
    rw [contDiffOn_pi]
    intro i
    rw [contDiffOn_pi]
    intro j
    exact Riemannian.chartGramOnE_contDiffOn (I := 𝓡 3) g a (e i) (e j)
  let L : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] (E3 →L[ℝ] E3) :=
    LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap
  have hL : ContDiff ℝ ∞ L := L.contDiff
  have hGat : ContDiffAt ℝ ∞ G y :=
    hG.contDiffAt ((isOpen_extChartAt_target (I := 𝓡 3) a).mem_nhds hy)
  have hcomp : ContDiffAt ℝ ∞ (fun z : E3 => L (G z)) y :=
    hL.contDiffAt.comp y hGat
  simpa [chartCoefficientOperator, G, L, Riemannian.chartGramOnE] using hcomp
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
