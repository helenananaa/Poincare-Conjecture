import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateFrameEquivalence
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateConnectionVector
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartChristoffelIdentification
import MorganTianLib.Ch01.ChartCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators Manifold Bundle RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The PDE connection vector is the existing geometric bilinear chart connection after explicit frame transport. -/
theorem connection_vector_geometric_frame {M : Type*} [TopologicalSpace M]
    [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a : M) (y : E3)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3))
    (hy : (extChartAt (𝓡 3) a).symm y ∈
      (trivializationAt E3 (TangentSpace (𝓡 3)) a).baseSet) :
    ∃ B : E3 ≃L[ℝ] E3,
      (∀ v : E3, B v=∑ i : Fin 3, v i • Module.finBasis ℝ E3 (e i)) ∧
      ∀ X Y : E3,
        B (connectionVector (chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm y) e)
          (chartCoefficientPartial g a y e) X Y) =
        MorganTianLib.chartChristoffelBilin g a y (B X) (B Y) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  letI : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
  obtain ⟨B, hB⟩ := coordinate_frame_equivalence e
  refine ⟨B, hB, ?_⟩
  intro X Y
  have hδ (i j : Fin (Module.finrank ℝ E3)) :
      (Riemannian.Geodesic.chartCoordFunctional (E := E3) i)
          (Module.finBasis ℝ E3 j) = if j = i then (1 : ℝ) else 0 := by
    rw [Riemannian.Geodesic.chartCoordFunctional_apply,
      Riemannian.Geodesic.chartCoord_def, Module.Basis.repr_self,
      Finsupp.single_apply]
  have hδc (i j : Fin (Module.finrank ℝ E3)) :
      Riemannian.Geodesic.chartCoord (E := E3) i
          (Module.finBasis ℝ E3 j) = if j = i then (1 : ℝ) else 0 := by
    rw [Riemannian.Geodesic.chartCoord_def, Module.Basis.repr_self,
      Finsupp.single_apply]
  have hbasis (i j : Fin (Module.finrank ℝ E3)) :
      MorganTianLib.chartChristoffelBilin g a y
          (Module.finBasis ℝ E3 i) (Module.finBasis ℝ E3 j) =
        ∑ k : Fin (Module.finrank ℝ E3),
          Riemannian.chartChristoffel g a i j k y • Module.finBasis ℝ E3 k := by
    rw [MorganTianLib.chartChristoffelBilin_apply (I := 𝓡 3) (E := E3),
      Riemannian.Geodesic.chartChristoffelContraction_def (I := 𝓡 3) (E := E3)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp only [hδc, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  rw [hB (connectionVector
    (chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm y) e)
    (chartCoefficientPartial g a y e) X Y), hB X, hB Y]
  simp only [map_sum, map_smul]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  simp_rw [hbasis]
  have hconn (k : Fin 3) :
      (connectionVector
          (chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm y) e)
          (chartCoefficientPartial g a y e) X Y).ofLp k =
        ∑ i : Fin 3, ∑ j : Fin 3,
          coordinateChristoffel
              (chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm y) e)
              (chartCoefficientPartial g a y e) k i j * X i * Y j := by
    rfl
  have hγ (k i j : Fin 3) :
      coordinateChristoffel
          (chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm y) e)
          (chartCoefficientPartial g a y e) k i j =
        Riemannian.chartChristoffel g a (e i) (e j) (e k) y :=
    coordinate_christoffel_eq_geometric_chart g a y e hy k i j
  have hreindex (i j : Fin 3) :
      (∑ k : Fin (Module.finrank ℝ E3),
        Riemannian.chartChristoffel g a (e i) (e j) k y •
          Module.finBasis ℝ E3 k) =
      ∑ k : Fin 3,
        Riemannian.chartChristoffel g a (e i) (e j) (e k) y •
          Module.finBasis ℝ E3 (e k) := by
    rw [← Equiv.sum_comp e]
  simp_rw [hconn, hγ, hreindex]
  simp only [Finset.smul_sum, smul_smul]
  have hperm (f : Fin 3 → Fin 3 → Fin 3 → E3) :
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, f i j k) =
        ∑ k : Fin 3, ∑ j : Fin 3, ∑ i : Fin 3, f i j k := by
    calc
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, f i j k) =
          ∑ i : Fin 3, ∑ k : Fin 3, ∑ j : Fin 3, f i j k := by
            apply Finset.sum_congr rfl
            intro i hi
            exact Finset.sum_comm
      _ = ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, f i j k := by
            exact Finset.sum_comm
      _ = ∑ k : Fin 3, ∑ j : Fin 3, ∑ i : Fin 3, f i j k := by
            apply Finset.sum_congr rfl
            intro k hk
            exact Finset.sum_comm
  calc
    _ = ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
        (Y j * (X i * Riemannian.chartChristoffel g a (e i) (e j) (e k) y)) •
          Module.finBasis ℝ E3 (e k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      ring
    _ = ∑ j : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3,
        (Y j * (X i * Riemannian.chartChristoffel g a (e i) (e j) (e k) y)) •
          Module.finBasis ℝ E3 (e k) :=
      hperm (fun k i j =>
        (Y j * (X i * Riemannian.chartChristoffel g a (e i) (e j) (e k) y)) •
          Module.finBasis ℝ E3 (e k))
    _ = _ := rfl
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
