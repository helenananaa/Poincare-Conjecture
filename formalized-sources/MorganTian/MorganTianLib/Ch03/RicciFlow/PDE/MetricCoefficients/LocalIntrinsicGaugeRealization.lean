import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualGaugeSmoothOn
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartVectorFieldExtension
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.IntrinsicLieCoordinates
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartOperatorEuclideanSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** local intrinsic gauge realization. -/
theorem local_intrinsic_gauge_realization {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (B : E3 ≃L[ℝ] E3)
    (hB : ∀ r : Fin 3, B (EuclideanSpace.single r 1) = Module.finBasis ℝ E3 (e r))
    (x : E3) (hx : B x ∈ (extChartAt (𝓡 3) a).target) :
    let p := (extChartAt (𝓡 3) a).symm (B x);
    let G : E3 → (E3 →L[ℝ] E3) := fun z =>
      chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm (B z)) e;
    let W : E3 → E3 := fun y => WithLp.toLp 2 (fun k : Fin 3 =>
      coordinateDeTurckGauge (G y) (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k);
    ∃ V : Riemannian.SmoothVectorField (𝓡 3) M,
      (∀ᶠ q : M in 𝓝 p, V q = ∑ k : Fin 3,
        W (B.symm (extChartAt (𝓡 3) a q)) k •
          Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) q) ∧ ∀ i j : Fin 3,
        MorganTianLib.metricLieDerivativeAt g V p
          (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)
          (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p) =
          coordinateLieMetricExpr G W x i j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let φ := extChartAt (𝓡 3) a
  let p : M := φ.symm (B x)
  let G : E3 → (E3 →L[ℝ] E3) := fun z =>
    chartCoefficientOperator g a (φ.symm (B z)) e
  let W : E3 → E3 := fun y => WithLp.toLp 2 (fun k : Fin 3 =>
    coordinateDeTurckGauge (G y)
      (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k)
  let S : Set E3 := {z | B z ∈ φ.target}
  have hSopen : IsOpen S := by
    exact (isOpen_extChartAt_target (I := 𝓡 3) a).preimage B.continuous
  have hxS : x ∈ S := hx
  have hG : ContDiffOn ℝ ∞ G S := by
    apply hSopen.contDiffOn_iff.mpr
    intro y hy
    have hchart := chart_operator_contDiffAt g a e (B y) hy
    have hBcont : ContDiffAt ℝ ∞ (fun z : E3 => B z) y :=
      B.toContinuousLinearMap.contDiff.contDiffAt
    change ContDiffAt ℝ ∞
      ((fun z : E3 => chartCoefficientOperator g a (φ.symm (B z)) e)) y
    have hcomp : ContDiffAt ℝ ∞
        ((fun z : E3 => chartCoefficientOperator g a (φ.symm z) e) ∘
          fun z : E3 => B z) y := by
      exact hchart.comp y hBcont
    simpa [Function.comp_def] using hcomp
  have hpos : ∀ y ∈ S, ∃ c : ℝ, 0 < c ∧
      ∀ v : E3, c * ‖v‖ ^ 2 ≤ inner ℝ (G y v) v := by
    intro y hy
    have hbase : φ.symm (B y) ∈
        (trivializationAt E3 (TangentSpace (𝓡 3)) a).baseSet := by
      simpa [φ, extChartAt_source] using φ.map_target hy
    obtain ⟨c, hc, hcoercive, _⟩ :=
      chart_coefficient_coercivity g a (φ.symm (B y)) e hbase
    refine ⟨c, hc, ?_⟩
    intro v
    simpa [G, φ] using hcoercive v
  have hW : ContDiffOn ℝ ∞ W S :=
    actual_gauge_contDiffOn G S hSopen hG hpos
  obtain ⟨V, hV⟩ :=
    chart_vector_field_extension g a e B hB x hx W S hSopen hxS hW
  refine ⟨V, hV, ?_⟩
  intro i j
  exact intrinsic_lie_eq_coordinate g a e B hB x hx W S hSopen hxS hW V hV i j
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
