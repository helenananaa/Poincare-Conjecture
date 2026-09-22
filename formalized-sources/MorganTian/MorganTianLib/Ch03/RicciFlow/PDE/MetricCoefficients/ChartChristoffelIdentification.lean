import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartCoefficientOperator
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.OperatorMatrixInverse
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
/-- Actual first coefficient jets, expressed in the same chart frame as the old geometric library. -/
def chartCoefficientPartial (g : RiemannianMetric (𝓡 3) M) (a : M) (y : E3)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (r : Fin 3) : E3 →L[ℝ] E3 :=
  Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (fun i j : Fin 3 =>
    partialDeriv (e r) (chartGramOnE g a (e i) (e j)) y)
/-- The PDE coordinate formula is the existing geometric chart Christoffel symbol, not a new placeholder. -/
theorem coordinate_christoffel_eq_geometric_chart (g : RiemannianMetric (𝓡 3) M)
    (a : M) (y : E3) (e : Fin 3 ≃ Fin (Module.finrank ℝ E3))
    (hy : (extChartAt (𝓡 3) a).symm y ∈
      (trivializationAt E3 (TangentSpace (𝓡 3)) a).baseSet) (k i j : Fin 3) :
    coordinateChristoffel
      (chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm y) e)
      (chartCoefficientPartial g a y e) k i j =
    chartChristoffel g a (e i) (e j) (e k) y :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let x : M := (extChartAt (𝓡 3) a).symm y
  have hx : x ∈ (trivializationAt E3 (TangentSpace (𝓡 3)) a).baseSet := by
    simpa [x] using hy
  obtain ⟨c, hc, hcoercive, _⟩ :=
    chart_coefficient_coercivity g a x e hx
  let A : E3 →L[ℝ] E3 := chartCoefficientOperator g a x e
  let Q : Matrix (Fin 3) (Fin 3) ℝ :=
    fun r s => chartGramMatrix g a x (e r) (e s)
  have htoCLM (B : Matrix (Fin 3) (Fin 3) ℝ) :
      (fun r s : Fin 3 =>
        (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) B
          (EuclideanSpace.single s 1)) r) = B := by
    ext r s
    change ((Matrix.toLin (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis B)
        (EuclideanSpace.single s 1)).ofLp r = B r s
    rw [Matrix.toLin_apply]
    simp [EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct,
      Pi.single_apply]
  have hentries :
      (fun r s : Fin 3 => (A (EuclideanSpace.single s 1)) r) = Q := by
    simpa [A, chartCoefficientOperator, Q] using htoCLM Q
  have hpartial (r s t : Fin 3) :
      (chartCoefficientPartial g a y e r (EuclideanSpace.single s 1)) t =
        partialDeriv (e r) (chartGramOnE g a (e t) (e s)) y := by
    have h := congrFun (congrFun (htoCLM
      (fun p q : Fin 3 =>
        partialDeriv (e r) (chartGramOnE g a (e p) (e q)) y)) t) s
    exact h
  have hinv := operator_matrix_inverse A c hc hcoercive
  have hAinv :
      (fun r s : Fin 3 => (A.inverse (EuclideanSpace.single s 1)) r) = Q⁻¹ := by
    calc
      (fun r s : Fin 3 => (A.inverse (EuclideanSpace.single s 1)) r) =
          (@Inv.inv (Matrix (Fin 3) (Fin 3) ℝ) Matrix.inv
            (fun r s : Fin 3 => (A (EuclideanSpace.single s 1)) r)) := hinv
      _ = Q⁻¹ := by rw [hentries]
  have hQ : Q = (chartGramMatrix g a x).reindex e.symm e.symm := by
    ext r s
    rfl
  have hQinv : Q⁻¹ =
      (fun r s : Fin 3 => chartInvGramMatrix g a x (e r) (e s)) := by
    rw [hQ, Matrix.inv_reindex]
    ext r s
    rfl
  have hcoef (r s : Fin 3) :
      (A.inverse (EuclideanSpace.single s 1)) r =
        chartInvGramMatrix g a x (e r) (e s) := by
    have h := congrFun (congrFun hAinv r) s
    rw [hQinv] at h
    exact h
  rw [coordinateChristoffel, chartChristoffel_def]
  congr 1
  calc
    (∑ l : Fin 3,
        (A.inverse (EuclideanSpace.single l 1)) k *
          ((chartCoefficientPartial g a y e i (EuclideanSpace.single l 1)) j +
            (chartCoefficientPartial g a y e j (EuclideanSpace.single l 1)) i -
              (chartCoefficientPartial g a y e l (EuclideanSpace.single j 1)) i)) =
        ∑ l : Fin 3,
          chartInvGramMatrix g a x (e k) (e l) *
            (partialDeriv (e i) (chartGramOnE g a (e l) (e j)) y +
              partialDeriv (e j) (chartGramOnE g a (e l) (e i)) y -
                partialDeriv (e l) (chartGramOnE g a (e i) (e j)) y) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [hcoef k l]
      rw [hpartial i l j, hpartial j l i, hpartial l j i]
      rw [show chartGramOnE g a (e j) (e l) =
          chartGramOnE g a (e l) (e j) by
            funext z
            exact chartGramOnE_symm g a (e j) (e l) z]
      rw [show chartGramOnE g a (e i) (e l) =
          chartGramOnE g a (e l) (e i) by
            funext z
            exact chartGramOnE_symm g a (e i) (e l) z]
    _ = ∑ m : Fin (Module.finrank ℝ E3),
          chartInvGramMatrix g a x (e k) m *
            (partialDeriv (e i) (chartGramOnE g a m (e j)) y +
              partialDeriv (e j) (chartGramOnE g a m (e i)) y -
                partialDeriv m (chartGramOnE g a (e i) (e j)) y) := by
      rw [← Equiv.sum_comp e]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
