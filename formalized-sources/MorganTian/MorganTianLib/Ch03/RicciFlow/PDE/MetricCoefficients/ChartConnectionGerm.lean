import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualConnectionGeometricFrame
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoefficientConnectionBilin
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** chart connection germ. -/
theorem chart_connection_germ {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (B : E3 ≃L[ℝ] E3)
    (hB : ∀ r : Fin 3, B (EuclideanSpace.single r 1) = Module.finBasis ℝ E3 (e r))
    (x : E3) (hx : B x ∈ (extChartAt (𝓡 3) a).target) :
    let G : E3 → (E3 →L[ℝ] E3) := fun z =>
      chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm (B z)) e;
    let Γ := fun y : E3 => coefficientConnectionBilin (G y)
      (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1));
    ∀ᶠ y : E3 in 𝓝 x, ∀ U V : E3, B (Γ y U V) =
      MorganTianLib.chartChristoffelBilin g a (B y) (B U) (B V) :=
/- SWARM_PROOF_BEGIN -/
by
  have htarget : (extChartAt (𝓡 3) a).target ∈ 𝓝 (B x) :=
    (isOpen_extChartAt_target (I := 𝓡 3) a).mem_nhds hx
  have hnear : ∀ᶠ y : E3 in 𝓝 x,
      B y ∈ (extChartAt (𝓡 3) a).target :=
    B.continuous.continuousAt.preimage_mem_nhds htarget
  filter_upwards [hnear] with y hy
  intro U V
  rw [coefficient_connection_bilin_apply]
  exact actual_connection_geometric_frame g a e B hB y hy U V
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
