import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartPartialActualDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartChristoffelIdentification
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartOperatorEuclideanSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Actual PDE Christoffel coefficients agree with the geometric chart coefficients after a fixed frame reparametrization. -/
theorem reparametrized_actual_christoffel {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (B : E3 ≃L[ℝ] E3)
    (hB : ∀ r : Fin 3, B (EuclideanSpace.single r 1) = Module.finBasis ℝ E3 (e r))
    (x : E3) (hx : B x ∈ (extChartAt (𝓡 3) a).target) (k i j : Fin 3) :
    let G : E3 → (E3 →L[ℝ] E3) := fun z =>
      chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm (B z)) e;
    coordinateChristoffel (G x)
      (fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)) k i j =
      Riemannian.chartChristoffel g a (e i) (e j) (e k) (B x) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let F : E3 → (E3 →L[ℝ] E3) := fun z =>
    chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm z) e
  have hbase : (extChartAt (𝓡 3) a).symm (B x) ∈
      (trivializationAt E3 (TangentSpace (𝓡 3)) a).baseSet := by
    simpa [extChartAt_source] using (extChartAt (𝓡 3) a).map_target hx
  have hFdiff : DifferentiableAt ℝ F (B x) := by
    have h := chart_operator_contDiffAt g a e (B x) hx
    exact h.differentiableAt (by norm_num)
  have hchain : fderiv ℝ (F ∘ fun z : E3 => B z) x =
      (fderiv ℝ F (B x)).comp B.toContinuousLinearMap := by
    exact (hFdiff.hasFDerivAt.comp x B.toContinuousLinearMap.hasFDerivAt).fderiv
  have hpartial : (fun r : Fin 3 =>
      fderiv ℝ (fun z : E3 => chartCoefficientOperator g a
        ((extChartAt (𝓡 3) a).symm (B z)) e) x (EuclideanSpace.single r 1)) =
      chartCoefficientPartial g a (B x) e := by
    funext r
    change fderiv ℝ (F ∘ fun z : E3 => B z) x (EuclideanSpace.single r 1) = _
    rw [hchain]
    change fderiv ℝ F (B x) (B (EuclideanSpace.single r 1)) = _
    rw [hB r]
    exact (chart_partial_eq_actual_fderiv g a e (B x) hx r).symm
  change coordinateChristoffel
    (chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm (B x)) e)
    (fun r : Fin 3 => fderiv ℝ (fun z : E3 => chartCoefficientOperator g a
      ((extChartAt (𝓡 3) a).symm (B z)) e) x (EuclideanSpace.single r 1)) k i j = _
  rw [hpartial]
  exact coordinate_christoffel_eq_geometric_chart g a (B x) e hbase k i j
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
