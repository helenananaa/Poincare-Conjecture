import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalIntrinsicGaugeRealization
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalChartDeTurckSplit
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** intrinsic local deturck equation. -/
theorem intrinsic_local_deturck_equation {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
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
    let P := fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1);
    ∃ V : Riemannian.SmoothVectorField (𝓡 3) M,
      (∀ᶠ q : M in 𝓝 p, V q = ∑ k : Fin 3,
        W (B.symm (extChartAt (𝓡 3) a q)) k •
          Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) q) ∧ ∀ i j : Fin 3,
      -2*MorganTianLib.ricciTensorAt g p
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p)
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p) +
      MorganTianLib.metricLieDerivativeAt g V p
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p) =
      (∑ r : Fin 3, ∑ s : Fin 3, ((G x).inverse (EuclideanSpace.single s 1)) r *
        (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single s 1)) x
          (EuclideanSpace.single r 1) (EuclideanSpace.single j 1)) i) +
      (-2*ricciLowerOrder (G x) P i j + deturckLieLowerOrder (G x) P i j) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨V, hV, hLie⟩ :=
    local_intrinsic_gauge_realization g a e B hB x hx
  refine ⟨V, hV, ?_⟩
  intro i j
  have hsplit := local_chart_ricci_deturck_split g a e B hB x hx i j
  rw [hLie i j]
  exact hsplit
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
