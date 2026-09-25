import Mathlib
import DoCarmoLib.Riemannian.Connection.ChartChristoffelSmooth
import PoincareConjecture.ParallelImplementation.EuclideanMetricOperatorRepresentation
import PoincareConjecture.ParallelImplementation.NormalizedSixMetricCoordinates
import PoincareConjecture.ParallelImplementation.ZeroTraceMetricPositivity
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import PoincareConjecture.ParallelImplementation.ChartMetricEuclideanExtension
import PoincareConjecture.ParallelImplementation.RadiusControlledClassicalDeTurck
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ManifoldChartClassicalInitialSolution
open scoped Topology BigOperators ContDiff Manifold BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
theorem exists_manifold_chart_classical_initial_solution
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
    (g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) M) (p : M)
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :

    ∃ E : E6 →L[ℝ] (E3 →L[ℝ] E3), Function.Injective E ∧ ‖E‖ ≤ 3 ∧
      (∀ (q : E6) (v : E3) (i : Fin 3), (E q v) i=∑ j : Fin 3, symmetricSixMatrix q i j*v j) ∧
    ∃ A : E3 ≃L[ℝ] E3, ∃ r T : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ hT : 0 < T, T ≤ 1 ∧
    ∃ U : E3 → E6, ContDiff ℝ 3 U ∧ HasCompactSupport U ∧
      (∀ x : E3, 2 ≤ ‖x‖ → U x=0) ∧
      (∀ x : E3, ‖x‖ ≤ 1 →
        let y : E3 := (extChartAt 𝓘(ℝ, E3) p) p+A (r • x)
        y ∈ (extChartAt 𝓘(ℝ, E3) p).target ∧ ∀ v w : E3,
          inner ℝ ((1+E (U x)) v) w=g.metricInner ((extChartAt 𝓘(ℝ, E3) p).symm y) ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm y) (A v)) ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm y) (A w))) ∧
      ∃ z : FullJet T, z.1.1 ∈ parabolicC2HolderSet T alpha ∧
        (z.1.1.1.1,z.1.2) ∈ slabTimeDerivativeGraph T ∧
        (∀ x : E3, z.1.1.1.1 (⟨0,le_rfl,hT.le⟩,x)=U x) ∧
        (∀ t : Set.Icc (0:ℝ) T, ContDiff ℝ 2 (fun x : E3 => z.1.1.1.1 (t,x))) ∧
        (∀ q : Slab T, IsUnit (metricOp E (fun y => z.1.1.1.1 (q.1,y)) q.2) ∧
          ∀ v : E3, (1/2:ℝ)*‖v‖^2 ≤ inner ℝ ((1+E (z.1.1.1.1 q)) v) v) ∧
        ∀ t : Set.Icc (0:ℝ) T, 0 < (t:ℝ) → (t:ℝ) < T → ∀ (x : E3) (i j : Fin 3),
          HasDerivAt (fun s : ℝ => (if i=j then 1 else 0)+symmetricSixMatrix (timeExtension z.1.1.1.1 x s) i j)
            (-2*actualRicci E (fun y => z.1.1.1.1 (t,y)) x i j+actualLie E (fun y => z.1.1.1.1 (t,y)) x i j) (t:ℝ) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨rho, hrho, hball, h, hext⟩ :=
    PoincareConjecture.ParallelImplementation.ChartMetricEuclideanExtension.exists_chart_metric_euclidean_extension
      g p
  obtain ⟨M, hMsmooth, hMrep, hMsym, hMpos⟩ :=
    PoincareConjecture.ParallelImplementation.EuclideanMetricOperatorRepresentation.exists_metric_operator_representation h
  obtain ⟨E0, hE0inj, hE0norm, hE0action, _hE0positive⟩ :=
    PoincareConjecture.ParallelImplementation.ZeroTraceMetricPositivity.zero_trace_metric_positivity
  let y0 : E3 := (extChartAt 𝓘(ℝ, E3) p) p
  have hM3 : ContDiff ℝ 3 M :=
    hMsmooth.of_le (by
      change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact_mod_cast (le_top : (3 : ℕ∞) ≤ ⊤))
  obtain ⟨A, u, hu, hu0, hnormalize⟩ :=
    PoincareConjecture.ParallelImplementation.NormalizedSixMetricCoordinates.exists_normalized_six_metric_coordinates
      E0 hE0action M hM3 hMsym y0 (fun v hv => hMpos y0 v hv)
  let rmax : ℝ := rho / (2 * (‖A.toContinuousLinearMap‖ + 1))
  have hrmax : 0 < rmax := by
    dsimp [rmax]
    positivity
  obtain ⟨E1, hE1inj, hE1norm, hE1action, r, T, hrpos, hrle, hrmax',
      hTpos, hTle, U, hU, hUcompact, hUinner, hUouter, z, hz,
      hzgraph, hzinitial, hzslices, hzmetric, hzequation⟩ :=
    PoincareConjecture.ParallelImplementation.RadiusControlledClassicalDeTurck.exists_radius_controlled_classical_deturck
      alpha ha ha1 u hu 0 hu0 rmax hrmax
  have hEeq : E1 = E0 := by
    apply ContinuousLinearMap.ext
    intro q
    apply ContinuousLinearMap.ext
    intro v
    ext i
    rw [hE1action, hE0action]
  subst E1
  refine ⟨E0, hE0inj, hE0norm, hE0action, A, r, T, hrpos, hrle,
    hTpos, hTle, U, hU, hUcompact, hUouter, ?_, z, hz, hzgraph,
    hzinitial, hzslices, hzmetric, ?_⟩
  · intro x hx
    let y : E3 := (extChartAt 𝓘(ℝ, E3) p) p + A (r • x)
    change y ∈ (extChartAt 𝓘(ℝ, E3) p).target ∧
      ∀ v w : E3,
        inner ℝ ((1 + E0 (U x)) v) w =
          g.metricInner ((extChartAt 𝓘(ℝ, E3) p).symm y)
            ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3)
              (extChartAt 𝓘(ℝ, E3) p).symm y) (A v))
            ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3)
              (extChartAt 𝓘(ℝ, E3) p).symm y) (A w))
    have hyball : y ∈ Metric.closedBall y0 rho := by
      change dist y y0 ≤ rho
      rw [dist_comm]
      change dist y0 (y0 + A (r • x)) ≤ rho
      rw [dist_eq_norm]
      have hdisplacement : y0 - (y0 + A (r • x)) = -(A (r • x)) := by abel
      rw [hdisplacement, norm_neg]
      calc
        ‖A (r • x)‖ ≤ ‖A.toContinuousLinearMap‖ * ‖r • x‖ :=
          A.toContinuousLinearMap.le_opNorm _
        _ = ‖A.toContinuousLinearMap‖ * (r * ‖x‖) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
        _ ≤ ‖A.toContinuousLinearMap‖ * r := by
          apply mul_le_mul_of_nonneg_left
          · have hrx : r * ‖x‖ ≤ r := by
              nlinarith [mul_nonneg (le_of_lt hrpos)
                (show 0 ≤ 1 - ‖x‖ by linarith)]
            exact hrx
          · exact norm_nonneg _
        _ ≤ ‖A.toContinuousLinearMap‖ * rmax :=
          mul_le_mul_of_nonneg_left hrmax' (norm_nonneg _)
        _ ≤ rho := by
          dsimp [rmax]
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith [mul_nonneg (norm_nonneg A.toContinuousLinearMap) hrho.le]
    refine ⟨hball hyball, ?_⟩
    intro v w
    have hUscaled : U x = u (r • x) := by
      simpa only [zero_add] using hUinner x hx
    calc
      inner ℝ ((1 + E0 (U x)) v) w =
          inner ℝ ((1 + E0 (u (r • x))) v) w := by rw [hUscaled]
      _ = inner ℝ (M (y0 + A (r • x)) (A v)) (A w) :=
        hnormalize (r • x) v w
      _ = h.metricInner y (A v) (A w) := (hMrep y (A v) (A w)).symm
      _ = g.metricInner ((extChartAt 𝓘(ℝ, E3) p).symm y)
            ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3)
              (extChartAt 𝓘(ℝ, E3) p).symm y) (A v))
            ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3)
              (extChartAt 𝓘(ℝ, E3) p).symm y) (A w)) := hext y hyball (A v) (A w)
  · intro t ht0 htT x i j
    simpa [zero_sub] using hzequation t ht0 htT x i j
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ManifoldChartClassicalInitialSolution
