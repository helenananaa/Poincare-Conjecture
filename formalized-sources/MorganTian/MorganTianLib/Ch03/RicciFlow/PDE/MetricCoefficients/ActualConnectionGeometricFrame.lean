import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ReparametrizedActualChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateConnectionVector
import MorganTianLib.Ch01.ChartCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Actual metric-derivative connection vectors match the geometric connection after frame transport. -/
theorem actual_connection_geometric_frame {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (B : E3 ≃L[ℝ] E3)
    (hB : ∀ r : Fin 3, B (EuclideanSpace.single r 1) = Module.finBasis ℝ E3 (e r))
    (x : E3) (hx : B x ∈ (extChartAt (𝓡 3) a).target) (X Y : E3) :
    let G : E3 → (E3 →L[ℝ] E3) := fun z =>
      chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm (B z)) e;
    B (connectionVector (G x)
      (fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)) X Y) =
      MorganTianLib.chartChristoffelBilin g a (B x) (B X) (B Y) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let G : E3 → (E3 →L[ℝ] E3) := fun z =>
    chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm (B z)) e
  have hBexp (v : E3) : B v =
      ∑ i : Fin 3, v i • Module.finBasis ℝ E3 (e i) := by
    calc
      B v = B (∑ i : Fin 3, v i • EuclideanSpace.single i 1) := by
        congr 1
        ext i
        simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single]
        simp [Pi.single_apply]
      _ = ∑ i : Fin 3, v i • B (EuclideanSpace.single i 1) := by
        simp only [map_sum, map_smul]
      _ = ∑ i : Fin 3, v i • Module.finBasis ℝ E3 (e i) := by
        simp_rw [hB]
  have hγ (k i j : Fin 3) :
      coordinateChristoffel (G x)
          (fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)) k i j =
        Riemannian.chartChristoffel g a (e i) (e j) (e k) (B x) := by
    exact reparametrized_actual_christoffel g a e B hB x hx k i j
  have hconn (k : Fin 3) :
      (connectionVector (G x)
        (fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)) X Y).ofLp k =
        ∑ i : Fin 3, ∑ j : Fin 3,
          coordinateChristoffel (G x)
            (fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)) k i j * X i * Y j := by
    rfl
  letI : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
  have hδc (i j : Fin (Module.finrank ℝ E3)) :
      Riemannian.Geodesic.chartCoord (E := E3) i
          (Module.finBasis ℝ E3 j) = if j = i then (1 : ℝ) else 0 := by
    rw [Riemannian.Geodesic.chartCoord_def, Module.Basis.repr_self,
      Finsupp.single_apply]
  have hbasis (i j : Fin (Module.finrank ℝ E3)) :
      MorganTianLib.chartChristoffelBilin g a (B x)
          (Module.finBasis ℝ E3 i) (Module.finBasis ℝ E3 j) =
        ∑ k : Fin (Module.finrank ℝ E3),
          Riemannian.chartChristoffel g a i j k (B x) • Module.finBasis ℝ E3 k := by
    rw [MorganTianLib.chartChristoffelBilin_apply (I := 𝓡 3) (E := E3),
      Riemannian.Geodesic.chartChristoffelContraction_def (I := 𝓡 3) (E := E3)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp only [hδc, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hreindex (i j : Fin 3) :
      (∑ k : Fin (Module.finrank ℝ E3),
        Riemannian.chartChristoffel g a (e i) (e j) k (B x) •
          Module.finBasis ℝ E3 k) =
      ∑ k : Fin 3,
        Riemannian.chartChristoffel g a (e i) (e j) (e k) (B x) •
          Module.finBasis ℝ E3 (e k) := by
    rw [← Equiv.sum_comp e]
  have hleft :
      B (connectionVector (G x)
        (fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)) X Y) =
        ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
          (coordinateChristoffel (G x)
            (fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)) k i j *
              X i * Y j) • Module.finBasis ℝ E3 (e k) := by
    rw [hBexp]
    simp_rw [hconn]
    simp only [Finset.sum_smul]
  have hright :
      MorganTianLib.chartChristoffelBilin g a (B x) (B X) (B Y) =
        ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          (X i * Y j * Riemannian.chartChristoffel g a
            (e i) (e j) (e k) (B x)) • Module.finBasis ℝ E3 (e k) := by
    rw [hBexp X, hBexp Y]
    simp only [map_sum, map_smul]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    simp_rw [hbasis]
    simp_rw [hreindex]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    ring
  have hperm (f : Fin 3 → Fin 3 → Fin 3 → E3) :
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, f i j k) =
        ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, f i j k := by
    calc
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, f i j k) =
          ∑ i : Fin 3, ∑ k : Fin 3, ∑ j : Fin 3, f i j k := by
            apply Finset.sum_congr rfl
            intro i hi
            exact Finset.sum_comm
      _ = ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, f i j k := by
            exact Finset.sum_comm
  let f : Fin 3 → Fin 3 → Fin 3 → E3 := fun i j k =>
    (Y j * (X i * Riemannian.chartChristoffel g a
      (e i) (e j) (e k) (B x))) • Module.finBasis ℝ E3 (e k)
  calc
    B (connectionVector (G x)
        (fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)) X Y) =
        ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
          (coordinateChristoffel (G x)
            (fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)) k i j *
              X i * Y j) • Module.finBasis ℝ E3 (e k) := hleft
    _ = ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, f i j k := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hγ]
      congr 1
      ring
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, f i j k := (hperm f).symm
    _ = MorganTianLib.chartChristoffelBilin g a (B x) (B X) (B Y) := by
      rw [hright]
      conv_lhs => rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      simp only [f]
      change (Y i * (X j * Riemannian.chartChristoffel g a
        (e j) (e i) (e k) (B x))) • Module.finBasis ℝ E3 (e k) =
        (X j * Y i * Riemannian.chartChristoffel g a
          (e j) (e i) (e k) (B x)) • Module.finBasis ℝ E3 (e k)
      congr 1
      ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
