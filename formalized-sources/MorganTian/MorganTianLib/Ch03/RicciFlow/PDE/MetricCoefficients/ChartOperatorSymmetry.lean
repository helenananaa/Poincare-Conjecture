import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartCoefficientOperator
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** chart operator selfadjoint. -/
theorem chart_operator_selfadjoint {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a x : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (v w : E3) :
    inner ℝ (chartCoefficientOperator g a x e v) w =
      inner ℝ v (chartCoefficientOperator g a x e w) :=
/- SWARM_PROOF_BEGIN -/
by
  open Riemannian.Tensor in
    classical
    let G : Matrix (Fin (Module.finrank ℝ E3)) (Fin (Module.finrank ℝ E3)) ℝ :=
      chartGramMatrix g a x
    let Q : Matrix (Fin 3) (Fin 3) ℝ := G.reindex e.symm e.symm
    have hGherm : G.IsHermitian :=
      Riemannian.Tensor.chartGramMatrix_isHermitian (I := 𝓡 3) g a x
    have hQherm : Q.IsHermitian := by
      dsimp [Q]
      simpa [Matrix.reindex_apply] using hGherm.submatrix e
    have hQ_entries : Q = fun i j : Fin 3 =>
        Riemannian.Tensor.chartGramMatrix g a x (e i) (e j) := by
      ext i j
      rfl
    have hself : IsSelfAdjoint (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) Q) := by
      rw [isSelfAdjoint_iff]
      calc
        star (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) Q) =
            Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (star Q) :=
          (map_star (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)) Q).symm
        _ = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) Q := by
          rw [hQherm.star_eq]
    simpa [chartCoefficientOperator, hQ_entries] using hself.isSymmetric v w
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
