import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalDeTurckEquationSplit
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualIntrinsicRicci
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartOperatorSymmetry
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartOperatorEuclideanSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "J3" => (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)
local notation "M3" => Fin 3 → Fin 3 → ℝ
local notation "E9" => EuclideanSpace ℝ (Fin 3 × Fin 3)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** local chart ricci deturck split. -/
theorem local_chart_ricci_deturck_split {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (B : E3 ≃L[ℝ] E3)
    (hB : ∀ r : Fin 3, B (EuclideanSpace.single r 1) = Module.finBasis ℝ E3 (e r))
    (x : E3) (hx : B x ∈ (extChartAt (𝓡 3) a).target) (i j : Fin 3) :
    let p := (extChartAt (𝓡 3) a).symm (B x);
    let G : E3 → (E3 →L[ℝ] E3) := fun z =>
      chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm (B z)) e;
    let P := fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1);
    let W : E3 → E3 := fun y => WithLp.toLp 2 (fun k : Fin 3 =>
      coordinateDeTurckGauge (G y) (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k);
    -2*MorganTianLib.ricciTensorAt g p
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p)
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p) +
      coordinateLieMetricExpr G W x i j =
      (∑ r : Fin 3, ∑ s : Fin 3, ((G x).inverse (EuclideanSpace.single s 1)) r *
        (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single s 1)) x
          (EuclideanSpace.single r 1) (EuclideanSpace.single j 1)) i) +
      (-2*ricciLowerOrder (G x) P i j+deturckLieLowerOrder (G x) P i j) :=
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
  obtain ⟨c, hc, hpos0, _hsym0⟩ := chart_coefficient_coercivity g a
    ((extChartAt (𝓡 3) a).symm (B x)) e hbase
  have hpos : ∀ v : E3, c * ‖v‖^2 ≤ inner ℝ (G x v) v := by
    intro v
    exact hpos0 v
  have hsym : ∀ᶠ y : E3 in 𝓝 x, ∀ v w : E3,
      inner ℝ (G y v) w = inner ℝ v (G y w) := by
    filter_upwards with y
    intro v w
    exact chart_operator_selfadjoint g a
      ((extChartAt (𝓡 3) a).symm (B y)) e v w
  have hsplit := local_deturck_equation_split G x hG hsym c hc hpos i j
  have hRicci := actual_coordinate_ricci_eq_intrinsic g a e B hB x hx i j
  have hRicci' : actualCoordinateRicci G x i j =
      MorganTianLib.ricciTensorAt g ((extChartAt (𝓡 3) a).symm (B x))
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j)
          ((extChartAt (𝓡 3) a).symm (B x)))
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i)
          ((extChartAt (𝓡 3) a).symm (B x))) := by
    simpa only [G, F] using hRicci
  dsimp only at hsplit ⊢
  rw [← hRicci']
  exact hsplit
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
