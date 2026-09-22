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
/-- Actual coefficient operator of the existing chart Gram matrix; e only reindexes the frame. -/
def chartCoefficientOperator (g : RiemannianMetric (𝓡 3) M) (a x : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) : E3 →L[ℝ] E3 :=
  Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (fun i j : Fin 3 => chartGramMatrix g a x (e i) (e j))
/-- Existing geometric positivity yields the actual operator bound needed by the PDE coefficients. -/
theorem chart_coefficient_coercivity (g : RiemannianMetric (𝓡 3) M) (a x : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3))
    (hx : x ∈ (trivializationAt E3 (TangentSpace (𝓡 3)) a).baseSet) :
    ∃ c : ℝ, 0<c ∧
      (∀ v : E3, c*‖v‖^2 ≤ inner ℝ (chartCoefficientOperator g a x e v) v) ∧
      (∀ v w : E3, inner ℝ (chartCoefficientOperator g a x e v) w =
        inner ℝ v (chartCoefficientOperator g a x e w)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let G : Matrix (Fin (Module.finrank ℝ E3)) (Fin (Module.finrank ℝ E3)) ℝ :=
    chartGramMatrix g a x
  let Q : Matrix (Fin 3) (Fin 3) ℝ := G.reindex e.symm e.symm
  have hGpos : G.PosDef := by
    exact Tensor.chartGramMatrix_posDef (I := 𝓡 3) g a hx
  have hGherm : G.IsHermitian :=
    Tensor.chartGramMatrix_isHermitian (I := 𝓡 3) g a x
  have hQpos : Q.PosDef := by
    dsimp [Q]
    simpa [Matrix.reindex_apply] using hGpos.submatrix e.injective
  have hQherm : Q.IsHermitian := by
    dsimp [Q]
    simpa [Matrix.reindex_apply] using hGherm.submatrix e
  have hQ_entries : Q = fun i j : Fin 3 =>
      chartGramMatrix g a x (e i) (e j) := by
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
  have hApos : ∀ v : E3, v ≠ 0 →
      0 < inner ℝ (chartCoefficientOperator g a x e v) v := by
    intro v hv
    have hv' : (v.ofLp : Fin 3 → ℝ) ≠ 0 := by
      simpa using hv
    have hq := hQpos.dotProduct_mulVec_pos hv'
    rw [hQ_entries] at hq
    simpa [chartCoefficientOperator, hQ_entries, real_inner_comm,
      Matrix.inner_toEuclideanCLM] using hq
  obtain ⟨c, hc, hcoercive⟩ :=
    compact_positive_operator_coercivity ({x} : Set M) isCompact_singleton
      ⟨x, rfl⟩ (fun _ : M => chartCoefficientOperator g a x e)
      (continuous_const.continuousOn) (by
        intro y hy v hv
        have hyx : y = x := mem_singleton_iff.mp hy
        subst y
        exact hApos v hv)
  refine ⟨c, hc, ?_, ?_⟩
  · intro v
    exact hcoercive x (by simp) v
  · intro v w
    exact hself.isSymmetric v w
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
