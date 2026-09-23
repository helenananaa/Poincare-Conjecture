import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartChristoffelIdentification
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartOperatorEuclideanSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.MatrixOperatorDerivative
import DoCarmoLib.Riemannian.Connection.ChartChristoffelSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** The geometric chart jet is the genuine directional derivative of the coefficient operator. -/
theorem chart_partial_eq_actual_fderiv {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (y : E3)
    (hy : y ∈ (extChartAt (𝓡 3) a).target) (r : Fin 3) :
    chartCoefficientPartial g a y e r =
      fderiv ℝ (fun z : E3 => chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm z) e) y (Module.finBasis ℝ E3 (e r)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  letI : TopologicalSpace (Matrix (Fin 3) (Fin 3) ℝ) := Pi.topologicalSpace
  letI : NormedAddCommGroup (Matrix (Fin 3) (Fin 3) ℝ) := Pi.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin 3) (Fin 3) ℝ) := Pi.normedSpace
  let F : E3 → Matrix (Fin 3) (Fin 3) ℝ := fun z i j =>
    Riemannian.chartGramOnE (I := 𝓡 3) g a (e i) (e j) z
  have hFcont : ContDiffOn ℝ ∞ F (extChartAt (𝓡 3) a).target := by
    change ContDiffOn ℝ ∞
      (fun z i j => Riemannian.chartGramOnE (I := 𝓡 3) g a (e i) (e j) z)
      (extChartAt (𝓡 3) a).target
    rw [contDiffOn_pi]
    intro i
    rw [contDiffOn_pi]
    intro j
    exact Riemannian.chartGramOnE_contDiffOn (I := 𝓡 3) g a (e i) (e j)
  have hFat : ContDiffAt ℝ ∞ F y :=
    hFcont.contDiffAt ((isOpen_extChartAt_target (I := 𝓡 3) a).mem_nhds hy)
  have hF : DifferentiableAt ℝ F y := hFat.differentiableAt (by norm_num)
  have hoperator :
      (fun z : E3 => chartCoefficientOperator g a
        ((extChartAt (𝓡 3) a).symm z) e) =
        (fun z : E3 => Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (F z)) := by
    funext z
    apply congrArg (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ))
    ext i j
    simp [F, Riemannian.chartGramOnE]
  have hderiv :
      fderiv ℝ (fun z : E3 => chartCoefficientOperator g a
        ((extChartAt (𝓡 3) a).symm z) e) y (Module.finBasis ℝ E3 (e r)) =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
        (fun i j : Fin 3 =>
          fderiv ℝ (fun z : E3 => F z i j) y (Module.finBasis ℝ E3 (e r))) := by
    rw [hoperator]
    exact matrix_operator_fderiv F y (Module.finBasis ℝ E3 (e r)) hF
  have hpartial (i j : Fin 3) :
      fderiv ℝ (fun z : E3 => F z i j) y (Module.finBasis ℝ E3 (e r)) =
        Riemannian.partialDeriv (e r)
          (Riemannian.chartGramOnE (I := 𝓡 3) g a (e i) (e j)) y := by
    change fderiv ℝ
      (fun z : E3 => Riemannian.chartGramOnE (I := 𝓡 3) g a (e i) (e j) z) y
      (Module.finBasis ℝ E3 (e r)) = _
    unfold Riemannian.partialDeriv
    rfl
  unfold chartCoefficientPartial
  rw [hderiv]
  exact congrArg (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)) (by
    ext i j
    exact (hpartial i j).symm)
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
