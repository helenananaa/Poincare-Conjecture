import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.GlobalBackgroundGauge
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ConnectionDifferenceChart
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartMetricTrace
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartChristoffelIdentification
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BackgroundConnectionContraction
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DeTurckGaugeVector
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

/-- **Math.** exists global gauge coordinates. -/
theorem exists_global_gauge_coordinates {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [SigmaCompactSpace M] [T2Space M] (g g0 : Riemannian.RiemannianMetric (𝓡 3) M) :
    ∃ W : Riemannian.SmoothVectorField (𝓡 3) M, ∀ a p : M,
      p ∈ (chartAt E3 a).source → ∀ e : Fin 3 ≃ Fin (Module.finrank ℝ E3),
      let A := chartCoefficientOperator g a p e;
      let P := chartCoefficientPartial g a (extChartAt (𝓡 3) a p) e;
      let T := fun k i j : Fin 3 => Riemannian.chartChristoffel g0 a (e i) (e j) (e k) (extChartAt (𝓡 3) a p);
      W p = ∑ k : Fin 3, (coordinateDeTurckGauge A P k-backgroundConnectionContraction A T k) •
        Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨W, hW⟩ := exists_global_connection_difference_trace
    g g.leviCivitaConnection g0.leviCivitaConnection
  refine ⟨W, ?_⟩
  intro a p hp e
  let A : E3 →L[ℝ] E3 := chartCoefficientOperator g a p e
  let P : Fin 3 → E3 →L[ℝ] E3 :=
    chartCoefficientPartial g a (extChartAt (𝓡 3) a p) e
  let T : T3 := fun k i j =>
    Riemannian.chartChristoffel g0 a (e i) (e j) (e k)
      (extChartAt (𝓡 3) a p)
  change W p = ∑ k : Fin 3,
    (coordinateDeTurckGauge A P k - backgroundConnectionContraction A T k) •
      Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p
  let v : Fin 3 → TangentSpace (𝓡 3) p := fun k =>
    Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p
  obtain ⟨D, hD⟩ := connection_difference_fiber_bilinear
    g.leviCivitaConnection g0.leviCivitaConnection p
  have hWtrace : W p = ∑ i : Fin (Module.finrank ℝ E3),
      D (stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) p) i)
        (stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) p) i) := by
    rw [hW p]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [MorganTianLib.extendVector_apply] using
      (hD (MorganTianLib.extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) p) i))
        (MorganTianLib.extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) p) i))).symm
  have htrace := chart_metric_trace g a p hp e D
  have hWchart : W p = ∑ i : Fin 3, ∑ j : Fin 3,
      (A.inverse (EuclideanSpace.single j 1)) i • D (v i) (v j) := by
    rw [hWtrace]
    exact htrace
  let y : E3 := extChartAt (𝓡 3) a p
  have hsymm : (extChartAt (𝓡 3) a).symm y = p := by
    have hpExt : p ∈ (extChartAt (𝓡 3) a).source := by
      rw [Riemannian.extChartAt_source_eq_chartAt_source (I := 𝓡 3)]
      exact hp
    exact (extChartAt (𝓡 3) a).left_inv hpExt
  have hy : (extChartAt (𝓡 3) a).symm y ∈
      (trivializationAt E3 (TangentSpace (𝓡 3)) a).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := 𝓡 3) a,
      ← Riemannian.extChartAt_source_eq_chartAt_source (I := 𝓡 3), hsymm]
    have hpExt : p ∈ (extChartAt (𝓡 3) a).source := by
      rw [Riemannian.extChartAt_source_eq_chartAt_source (I := 𝓡 3)]
      exact hp
    exact hpExt
  have hgammaG (k i j : Fin 3) :
      coordinateChristoffel A P k i j =
        Riemannian.chartChristoffel g a (e i) (e j) (e k)
          y := by
    change coordinateChristoffel
        (chartCoefficientOperator g a p e)
        (chartCoefficientPartial g a y e) k i j = _
    rw [← hsymm]
    exact coordinate_christoffel_eq_geometric_chart g a
      y e hy k i j
  have hDchart (i j : Fin 3) :
      D (v i) (v j) = ∑ l : Fin 3,
        (Riemannian.chartChristoffel g a (e i) (e j) (e l)
            (extChartAt (𝓡 3) a p) -
          Riemannian.chartChristoffel g0 a (e i) (e j) (e l)
            (extChartAt (𝓡 3) a p)) • v l := by
    calc
      D (v i) (v j) = connectionDifferenceField
          g.leviCivitaConnection g0.leviCivitaConnection
          (MorganTianLib.extendVector p (v i))
          (MorganTianLib.extendVector p (v j)) p := by
        simpa only [v, MorganTianLib.extendVector_apply] using
          hD (MorganTianLib.extendVector p (v i))
            (MorganTianLib.extendVector p (v j))
      _ = ∑ l : Fin 3,
          (Riemannian.chartChristoffel g a (e i) (e j) (e l)
              (extChartAt (𝓡 3) a p) -
            Riemannian.chartChristoffel g0 a (e i) (e j) (e l)
              (extChartAt (𝓡 3) a p)) • v l := by
        simpa [v] using connection_difference_chart g g0 a p hp e i j
  let c : Fin 3 → Fin 3 → ℝ := fun i j =>
    (A.inverse (EuclideanSpace.single j 1)) i
  have hperm (f : Fin 3 → Fin 3 → Fin 3 → TangentSpace (𝓡 3) p) :
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, f i j l) =
        ∑ l : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, f i j l := by
    calc
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, f i j l) =
          ∑ i : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3, f i j l := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_comm
      _ = ∑ l : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, f i j l := by
        exact Finset.sum_comm
  have hWcoeff : W p = ∑ l : Fin 3,
      (∑ i : Fin 3, ∑ j : Fin 3, c i j *
        (Riemannian.chartChristoffel g a (e i) (e j) (e l)
            (extChartAt (𝓡 3) a p) -
          Riemannian.chartChristoffel g0 a (e i) (e j) (e l)
            (extChartAt (𝓡 3) a p))) • v l := by
    calc
      W p = ∑ i : Fin 3, ∑ j : Fin 3,
          (A.inverse (EuclideanSpace.single j 1)) i • D (v i) (v j) := hWchart
      _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
          (c i j *
            (Riemannian.chartChristoffel g a (e i) (e j) (e l)
                (extChartAt (𝓡 3) a p) -
              Riemannian.chartChristoffel g0 a (e i) (e j) (e l)
                (extChartAt (𝓡 3) a p))) • v l := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hDchart i j]
        simp only [Finset.smul_sum, smul_smul, c]
      _ = ∑ l : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
          (c i j *
            (Riemannian.chartChristoffel g a (e i) (e j) (e l)
                (extChartAt (𝓡 3) a p) -
              Riemannian.chartChristoffel g0 a (e i) (e j) (e l)
                (extChartAt (𝓡 3) a p))) • v l :=
        hperm (fun i j l =>
          (c i j *
            (Riemannian.chartChristoffel g a (e i) (e j) (e l)
                (extChartAt (𝓡 3) a p) -
              Riemannian.chartChristoffel g0 a (e i) (e j) (e l)
                (extChartAt (𝓡 3) a p))) • v l)
      _ = ∑ l : Fin 3,
          (∑ i : Fin 3, ∑ j : Fin 3, c i j *
            (Riemannian.chartChristoffel g a (e i) (e j) (e l)
                (extChartAt (𝓡 3) a p) -
              Riemannian.chartChristoffel g0 a (e i) (e j) (e l)
                (extChartAt (𝓡 3) a p))) • v l := by
        apply Finset.sum_congr rfl
        intro l hl
        simp_rw [← Finset.sum_smul]
  have hcoeff (k : Fin 3) :
      (∑ i : Fin 3, ∑ j : Fin 3, c i j *
        (Riemannian.chartChristoffel g a (e i) (e j) (e k)
            (extChartAt (𝓡 3) a p) -
          Riemannian.chartChristoffel g0 a (e i) (e j) (e k)
            (extChartAt (𝓡 3) a p))) =
        coordinateDeTurckGauge A P k - backgroundConnectionContraction A T k := by
    calc
      _ = (∑ i : Fin 3, ∑ j : Fin 3,
            c i j * coordinateChristoffel A P k i j) -
          (∑ i : Fin 3, ∑ j : Fin 3,
            c i j * Riemannian.chartChristoffel g0 a (e i) (e j) (e k)
              (extChartAt (𝓡 3) a p)) := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hgammaG k i j]
      _ = coordinateDeTurckGauge A P k - backgroundConnectionContraction A T k := by
        simp [coordinateDeTurckGauge, backgroundConnectionContraction, c, T]
  calc
    W p = ∑ l : Fin 3,
        (∑ i : Fin 3, ∑ j : Fin 3, c i j *
          (Riemannian.chartChristoffel g a (e i) (e j) (e l)
              (extChartAt (𝓡 3) a p) -
            Riemannian.chartChristoffel g0 a (e i) (e j) (e l)
              (extChartAt (𝓡 3) a p))) • v l := hWcoeff
    _ = ∑ k : Fin 3,
        (coordinateDeTurckGauge A P k - backgroundConnectionContraction A T k) •
          Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hcoeff k]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
