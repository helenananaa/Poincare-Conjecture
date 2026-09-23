import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartConnectionGerm
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoefficientConnectionDifferentiable
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CurvatureLinearNaturality
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartOperatorEuclideanSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** actual chart curvature transport. -/
theorem actual_chart_curvature_transport {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (B : E3 ≃L[ℝ] E3)
    (hB : ∀ r : Fin 3, B (EuclideanSpace.single r 1) = Module.finBasis ℝ E3 (e r))
    (x : E3) (hx : B x ∈ (extChartAt (𝓡 3) a).target) (X Y Z : E3) :
    let G : E3 → (E3 →L[ℝ] E3) := fun z =>
      chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm (B z)) e;
    let Γ := fun y : E3 => coefficientConnectionBilin (G y)
      (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1));
    B (MorganTianLib.christoffelCurvature Γ x X Y Z) =
      MorganTianLib.chartCurvature g a (B x) (B X) (B Y) (B Z) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let F : E3 → (E3 →L[ℝ] E3) := fun z =>
    chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm z) e
  have hF : ContDiffAt ℝ ∞ F (B x) := by
    exact chart_operator_contDiffAt g a e (B x) hx
  have hBcont : ContDiffAt ℝ ∞ (fun z : E3 => B z) x :=
    B.toContinuousLinearMap.contDiff.contDiffAt
  have hG : ContDiffAt ℝ ∞ (F ∘ fun z : E3 => B z) x :=
    hF.comp x hBcont
  have hbase : (extChartAt (𝓡 3) a).symm (B x) ∈
      (trivializationAt E3 (TangentSpace (𝓡 3)) a).baseSet := by
    simpa [extChartAt_source] using (extChartAt (𝓡 3) a).map_target hx
  obtain ⟨c, hc, hcoercive, _⟩ :=
    chart_coefficient_coercivity g a
      ((extChartAt (𝓡 3) a).symm (B x)) e hbase
  let G : E3 → (E3 →L[ℝ] E3) := fun z => F (B z)
  let Γ : E3 → E3 →L[ℝ] E3 →L[ℝ] E3 := fun y =>
    coefficientConnectionBilin (G y)
      (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1))
  have hG' : ContDiffAt ℝ 2 G x := by
    change ContDiffAt ℝ 2 (F ∘ fun z : E3 => B z) x
    exact hG.of_le (WithTop.coe_le_coe.2
      (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hΓ : DifferentiableAt ℝ Γ x := by
    apply coefficient_connection_differentiable G x hG' c hc
    intro v
    exact hcoercive v
  letI : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
  have hΓ₂ : DifferentiableAt ℝ (MorganTianLib.chartChristoffelBilin g a) (B x) := by
    apply MorganTianLib.differentiableAt_chartChristoffelBilin (I := 𝓡 3) g a
    rw [(isOpen_extChartAt_target (I := 𝓡 3) a).interior_eq]
    exact hx
  have hrel := chart_connection_germ g a e B hB x hx
  change B (MorganTianLib.christoffelCurvature Γ x X Y Z) =
    MorganTianLib.christoffelCurvature
      (MorganTianLib.chartChristoffelBilin g a) (B x) (B X) (B Y) (B Z)
  exact curvature_linear_naturality Γ (MorganTianLib.chartChristoffelBilin g a)
    B x hΓ hΓ₂ hrel X Y Z
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
