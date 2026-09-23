import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualChartCurvature
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualRicciCurvatureTrace
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartOperatorSymmetry
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** actual chart ricci contraction. -/
theorem actual_chart_ricci_contraction {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (B : E3 ≃L[ℝ] E3)
    (hB : ∀ r : Fin 3, B (EuclideanSpace.single r 1) = Module.finBasis ℝ E3 (e r))
    (x : E3) (hx : B x ∈ (extChartAt (𝓡 3) a).target) (i j : Fin 3) :
    let G : E3 → (E3 →L[ℝ] E3) := fun z =>
      chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm (B z)) e;
    actualCoordinateRicci G x i j = ∑ k : Fin 3,
      (B.symm (MorganTianLib.chartCurvature g a (B x) (B (EuclideanSpace.single k 1))
        (B (EuclideanSpace.single j 1)) (B (EuclideanSpace.single i 1)))) k :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let F : E3 → (E3 →L[ℝ] E3) := fun z =>
    chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm z) e
  let G : E3 → (E3 →L[ℝ] E3) := fun z => F (B z)
  have hF : ContDiffAt ℝ ∞ F (B x) :=
    chart_operator_contDiffAt g a e (B x) hx
  have hBcont : ContDiffAt ℝ ∞ (fun z : E3 => B z) x :=
    B.toContinuousLinearMap.contDiff.contDiffAt
  have hGinf : ContDiffAt ℝ ∞ G x := by
    change ContDiffAt ℝ ∞ (F ∘ fun z : E3 => B z) x
    exact hF.comp x hBcont
  have hG : ContDiffAt ℝ 2 G x :=
    hGinf.of_le (WithTop.coe_le_coe.2 (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hbase : (extChartAt (𝓡 3) a).symm (B x) ∈
      (trivializationAt E3 (TangentSpace (𝓡 3)) a).baseSet := by
    simpa [extChartAt_source] using (extChartAt (𝓡 3) a).map_target hx
  obtain ⟨c, hc, hpos0, _⟩ := chart_coefficient_coercivity g a
    ((extChartAt (𝓡 3) a).symm (B x)) e hbase
  have hpos : ∀ v : E3, c * ‖v‖ ^ 2 ≤ inner ℝ (G x v) v := by
    intro v
    exact hpos0 v
  have hsym : ∀ᶠ y : E3 in 𝓝 x, ∀ v w : E3,
      inner ℝ (G y v) w = inner ℝ v (G y w) := by
    filter_upwards with y
    intro v w
    exact chart_operator_selfadjoint g a
      ((extChartAt (𝓡 3) a).symm (B y)) e v w
  let Γ : E3 → E3 →L[ℝ] E3 →L[ℝ] E3 := fun y =>
    coefficientConnectionBilin (G y)
      (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1))
  change actualCoordinateRicci G x i j = ∑ k : Fin 3,
    (B.symm (MorganTianLib.chartCurvature g a (B x)
      (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single j 1))
      (B (EuclideanSpace.single i 1)))) k
  have hricci : actualCoordinateRicci G x i j =
      ∑ k : Fin 3, (MorganTianLib.christoffelCurvature Γ x
        (EuclideanSpace.single k 1) (EuclideanSpace.single j 1)
        (EuclideanSpace.single i 1)) k := by
    exact actual_ricci_eq_curvature_trace G x hG hsym c hc hpos i j
  calc
    actualCoordinateRicci G x i j =
        ∑ k : Fin 3, (MorganTianLib.christoffelCurvature Γ x
          (EuclideanSpace.single k 1) (EuclideanSpace.single j 1)
          (EuclideanSpace.single i 1)) k := hricci
    _ = ∑ k : Fin 3, (B.symm (MorganTianLib.chartCurvature g a (B x)
          (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single j 1))
          (B (EuclideanSpace.single i 1)))) k := by
      apply Finset.sum_congr rfl
      intro k hk
      have htransport := actual_chart_curvature_transport g a e B hB x hx
        (EuclideanSpace.single k 1) (EuclideanSpace.single j 1)
        (EuclideanSpace.single i 1)
      have hvec := congrArg B.symm htransport
      simpa [Γ, G, F] using congrArg (fun v : E3 => v k) hvec
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
