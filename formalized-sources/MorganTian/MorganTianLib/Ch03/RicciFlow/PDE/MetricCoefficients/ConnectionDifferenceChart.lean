import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ConnectionDifferenceLocality
import MorganTianLib.Ch01.PointwiseCurvature
import DoCarmoLib.Riemannian.Connection.ChartCurvatureMovingPoint
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local notation "J3" => (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)
local notation "JBg" => J3 × (T3 × (Fin 3 → T3))
local notation "E9" => EuclideanSpace ℝ (Fin 3 × Fin 3)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** connection difference chart. -/
theorem connection_difference_chart {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [SigmaCompactSpace M] [T2Space M] (g g0 : Riemannian.RiemannianMetric (𝓡 3) M) (a p : M)
    (hp : p ∈ (chartAt E3 a).source) (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (i j : Fin 3) :
    let v := fun k : Fin 3 => Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p;
    connectionDifferenceField g.leviCivitaConnection g0.leviCivitaConnection
      (MorganTianLib.extendVector p (v i)) (MorganTianLib.extendVector p (v j)) p =
      ∑ k : Fin 3, (Riemannian.chartChristoffel g a (e i) (e j) (e k) (extChartAt (𝓡 3) a p)-
        Riemannian.chartChristoffel g0 a (e i) (e j) (e k) (extChartAt (𝓡 3) a p)) • v k :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let v := fun k : Fin 3 =>
    Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p
  have hbaseopen : IsOpen (trivializationAt E3 (TangentSpace (𝓡 3)) a).baseSet :=
    (trivializationAt E3 (TangentSpace (𝓡 3)) a).open_baseSet
  have hbase : p ∈ (trivializationAt E3 (TangentSpace (𝓡 3)) a).baseSet := hp
  choose Z hZ using fun m : Fin (Module.finrank ℝ E3) =>
    Riemannian.exists_smoothVectorField_eventuallyEq (I := 𝓡 3)
      (σ := fun q => Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a m q)
      (s := (trivializationAt E3 (TangentSpace (𝓡 3)) a).baseSet) hbaseopen
      (Riemannian.Tensor.chartBasisVec_contMDiffOn (I := 𝓡 3) a m) hbase
  have hZev : ∀ m : Fin (Module.finrank ℝ E3), ∀ᶠ q : M in 𝓝 p,
      Z m q = Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a m q := hZ
  have hXi : (MorganTianLib.extendVector p (v i)) p = Z (e i) p := by
    rw [MorganTianLib.extendVector_apply]
    exact (hZev (e i)).self_of_nhds.symm
  have hXj : (MorganTianLib.extendVector p (v j)) p = Z (e j) p := by
    rw [MorganTianLib.extendVector_apply]
    exact (hZev (e j)).self_of_nhds.symm
  have hlocal := connection_difference_pointwise
    g.leviCivitaConnection g0.leviCivitaConnection
    (MorganTianLib.extendVector p (v i)) (Z (e i))
    (MorganTianLib.extendVector p (v j)) (Z (e j)) p hXi hXj
  have hGerm : ∀ m : Fin (Module.finrank ℝ E3),
      (Z m).toFun =ᶠ[𝓝 p]
        (fun q => Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a m q) := by
    intro m
    exact hZev m
  have hGraw : (g.leviCivitaConnection.cov (Z (e i)) (Z (e j))) p =
      ∑ m : Fin (Module.finrank ℝ E3),
        Riemannian.chartChristoffel g a (e i) (e j) m
          (extChartAt (𝓡 3) a p) •
            Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a m p := by
    exact Riemannian.leviCivita_cov_frame_expansion
      (I := 𝓡 3) g a Z (e i) (e j) hp hGerm
  have hG0raw : (g0.leviCivitaConnection.cov (Z (e i)) (Z (e j))) p =
      ∑ m : Fin (Module.finrank ℝ E3),
        Riemannian.chartChristoffel g0 a (e i) (e j) m
          (extChartAt (𝓡 3) a p) •
            Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a m p := by
    exact Riemannian.leviCivita_cov_frame_expansion
      (I := 𝓡 3) g0 a Z (e i) (e j) hp hGerm
  have hG : (g.leviCivitaConnection.cov (Z (e i)) (Z (e j))) p =
      ∑ k : Fin 3,
        Riemannian.chartChristoffel g a (e i) (e j) (e k)
          (extChartAt (𝓡 3) a p) • v k := by
    calc
      _ = ∑ m : Fin (Module.finrank ℝ E3),
          Riemannian.chartChristoffel g a (e i) (e j) m
            (extChartAt (𝓡 3) a p) •
              Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a m p := hGraw
      _ = ∑ k : Fin 3,
          Riemannian.chartChristoffel g a (e i) (e j) (e k)
            (extChartAt (𝓡 3) a p) • v k := by
        rw [← Equiv.sum_comp e]
  have hG0 : (g0.leviCivitaConnection.cov (Z (e i)) (Z (e j))) p =
      ∑ k : Fin 3,
        Riemannian.chartChristoffel g0 a (e i) (e j) (e k)
          (extChartAt (𝓡 3) a p) • v k := by
    calc
      _ = ∑ m : Fin (Module.finrank ℝ E3),
          Riemannian.chartChristoffel g0 a (e i) (e j) m
            (extChartAt (𝓡 3) a p) •
              Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a m p := hG0raw
      _ = ∑ k : Fin 3,
          Riemannian.chartChristoffel g0 a (e i) (e j) (e k)
            (extChartAt (𝓡 3) a p) • v k := by
        rw [← Equiv.sum_comp e]
  dsimp only
  rw [hlocal]
  change (g.leviCivitaConnection.cov (Z (e i)) (Z (e j))) p -
      (g0.leviCivitaConnection.cov (Z (e i)) (Z (e j))) p = _
  rw [hG, hG0]
  calc
    _ = ∑ k : Fin 3,
        (Riemannian.chartChristoffel g a (e i) (e j) (e k)
            (extChartAt (𝓡 3) a p) • v k -
          Riemannian.chartChristoffel g0 a (e i) (e j) (e k)
            (extChartAt (𝓡 3) a p) • v k) := by
      rw [← Finset.sum_sub_distrib]
    _ = ∑ k : Fin 3,
        (Riemannian.chartChristoffel g a (e i) (e j) (e k)
            (extChartAt (𝓡 3) a p) -
          Riemannian.chartChristoffel g0 a (e i) (e j) (e k)
            (extChartAt (𝓡 3) a p)) • v k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [sub_smul]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
