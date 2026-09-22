import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartCoefficientOperator
import DoCarmoLib.Riemannian.Connection.ChartChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CompactCoercivity
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter Bundle Manifold Riemannian Riemannian.Tensor
open scoped Topology Manifold ContDiff BigOperators RealInnerProductSpace Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
/-- The actual coefficient operator depends smoothly on the base point in its chart domain. -/
theorem chart_coefficient_smooth (g : RiemannianMetric (𝓡 3) M) (a : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) :
    ContMDiffOn (𝓡 3) 𝓘(ℝ, E3 →L[ℝ] E3) ∞
      (fun x : M => chartCoefficientOperator g a x e)
      (trivializationAt E3 (TangentSpace (𝓡 3)) a).baseSet :=
/- SWARM_PROOF_BEGIN -/
by
  letI : TopologicalSpace (Matrix (Fin 3) (Fin 3) ℝ) := Pi.topologicalSpace
  letI : NormedAddCommGroup (Matrix (Fin 3) (Fin 3) ℝ) := Pi.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin 3) (Fin 3) ℝ) := Pi.normedSpace
  let G : M → Matrix (Fin 3) (Fin 3) ℝ := fun x i j =>
    chartGramMatrix g a x (e i) (e j)
  have hG : ContMDiffOn (𝓡 3) 𝓘(ℝ, Matrix (Fin 3) (Fin 3) ℝ) ∞ G
      (trivializationAt E3 (TangentSpace (𝓡 3)) a).baseSet := by
    change ContMDiffOn (𝓡 3) 𝓘(ℝ, Fin 3 → Fin 3 → ℝ) ∞
      (fun x i j => chartGramMatrix g a x (e i) (e j))
      (trivializationAt E3 (TangentSpace (𝓡 3)) a).baseSet
    rw [contMDiffOn_pi_space]
    intro i
    rw [contMDiffOn_pi_space]
    intro j
    exact chartGramMatrix_entry_contMDiffOn (I := 𝓡 3) g a (e i) (e j)
  let L : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] (E3 →L[ℝ] E3) :=
    LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap
  have hL : ContMDiffOn 𝓘(ℝ, Matrix (Fin 3) (Fin 3) ℝ)
      𝓘(ℝ, E3 →L[ℝ] E3) ∞ L Set.univ := L.contMDiffOn
  have hcomp := hL.comp hG (by intro x hx; simp)
  exact hcomp.congr (fun x hx => by
    rfl)
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
