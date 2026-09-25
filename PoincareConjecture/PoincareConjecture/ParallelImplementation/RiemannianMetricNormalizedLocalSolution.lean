import Mathlib
import PoincareConjecture.ParallelImplementation.SymmetricSixPacking
import PoincareConjecture.ParallelImplementation.NormalizedLocalClassicalDeTurck
import PoincareConjecture.ParallelImplementation.ZeroTraceMetricPositivity
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import PoincareConjecture.ParallelImplementation.EuclideanCoordinateFields
import PoincareConjecture.ParallelImplementation.EuclideanMetricOperatorRepresentation
import PoincareConjecture.ParallelImplementation.NormalizedSixMetricCoordinates
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.RiemannianMetricNormalizedLocalSolution
open scoped Topology BigOperators ContDiff Manifold BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
theorem exists_metric_normalized_local_solution
    (g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3) (p0 : E3)
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :

    ∃ E : E6 →L[ℝ] (E3 →L[ℝ] E3), Function.Injective E ∧ ‖E‖ ≤ 3 ∧
      (∀ (q : E6) (v : E3) (i : Fin 3), (E q v) i=∑ j : Fin 3, symmetricSixMatrix q i j*v j) ∧
    ∃ A : E3 ≃L[ℝ] E3, ∃ r T : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ hT : 0 < T, T ≤ 1 ∧
    ∃ U : E3 → E6, ContDiff ℝ 3 U ∧ HasCompactSupport U ∧
      (∀ x : E3, 2 ≤ ‖x‖ → U x=0) ∧
      (∀ v w : E3, g.metricInner p0 (A v) (A w)=inner ℝ v w) ∧
      (∀ x : E3, ‖x‖ ≤ 1 → ∀ v w : E3,
        inner ℝ ((1+E (U x)) v) w=g.metricInner (p0+A (r • x)) (A v) (A w)) ∧
    ∃ z : FullJet T, z.1.1 ∈ parabolicC2HolderSet T alpha ∧
      (z.1.1.1.1,z.1.2) ∈ slabTimeDerivativeGraph T ∧
      (∀ x : E3, z.1.1.1.1 (⟨0,le_rfl,hT.le⟩,x)=U x) ∧
      (∀ t : Set.Icc (0:ℝ) T, ContDiff ℝ 2 (fun x : E3 => z.1.1.1.1 (t,x))) ∧
      (∀ p : Slab T, IsUnit (metricOp E (fun y => z.1.1.1.1 (p.1,y)) p.2) ∧
        ∀ v : E3, (1/2:ℝ)*‖v‖^2 ≤ inner ℝ ((1+E (z.1.1.1.1 p)) v) v) ∧
      ∀ t : Set.Icc (0:ℝ) T, 0 < (t:ℝ) → (t:ℝ) < T → ∀ (x : E3) (i j : Fin 3),
        HasDerivAt (fun s : ℝ => (if i=j then 1 else 0)+symmetricSixMatrix (timeExtension z.1.1.1.1 x s) i j)
          (-2*actualRicci E (fun y => z.1.1.1.1 (t,y)) x i j+actualLie E (fun y => z.1.1.1.1 (t,y)) x i j) (t:ℝ) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨M, hMsmooth, hMrep, hMsym, hMpos⟩ :=
    PoincareConjecture.ParallelImplementation.EuclideanMetricOperatorRepresentation.exists_metric_operator_representation g
  obtain ⟨E0, hE0inj, hE0norm, hE0action, _hE0positive⟩ :=
    PoincareConjecture.ParallelImplementation.ZeroTraceMetricPositivity.zero_trace_metric_positivity
  have hM3 : ContDiff ℝ 3 M :=
    hMsmooth.of_le (by
      change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact_mod_cast (le_top : (3 : ℕ∞) ≤ ⊤))
  obtain ⟨A, u, hu, hu0, hnormalize⟩ :=
    PoincareConjecture.ParallelImplementation.NormalizedSixMetricCoordinates.exists_normalized_six_metric_coordinates
      E0 hE0action M hM3 hMsym p0 (fun v hv => hMpos p0 v hv)
  obtain ⟨E1, hE1inj, hE1norm, hE1action, r, T, hrpos, hrle,
      hTpos, hTle, U, hU, hUcompact, hUonball, hUzero, z, hz,
      hzgraph, hzinitial, hzslices, hzmetric, hzequation⟩ :=
    PoincareConjecture.ParallelImplementation.NormalizedLocalClassicalDeTurck.exists_normalized_local_classical_deturck
      alpha ha ha1 u hu 0 hu0
  have hEeq : E1 = E0 := by
    apply ContinuousLinearMap.ext
    intro q
    apply ContinuousLinearMap.ext
    intro v
    ext i
    rw [hE1action, hE0action]
  subst E1
  refine ⟨E0, hE0inj, hE0norm, hE0action, A, r, T, hrpos, hrle,
    hTpos, hTle, U, hU, hUcompact, hUzero, ?_, ?_, z, hz, hzgraph,
    hzinitial, hzslices, hzmetric, ?_⟩
  · intro v w
    have hzero := hnormalize 0 v w
    have hzero' : inner ℝ v w = inner ℝ (M p0 (A v)) (A w) := by
      simpa [hu0] using hzero
    calc
      g.metricInner p0 (A v) (A w) = inner ℝ (M p0 (A v)) (A w) :=
        hMrep p0 (A v) (A w)
      _ = inner ℝ v w := hzero'.symm
  · intro x hx v w
    have hUscaled : U x = u (r • x) := by
      simpa only [zero_add] using hUonball x hx
    have hnormalized := hnormalize (r • x) v w
    rw [← hUscaled, ← hMrep] at hnormalized
    exact hnormalized
  · intro t ht0 htT x i j
    simpa [zero_sub] using hzequation t ht0 htT x i j
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RiemannianMetricNormalizedLocalSolution
