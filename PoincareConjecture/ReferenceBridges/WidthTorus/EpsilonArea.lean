import ReferenceBridges.Quantitative.EpsilonMetricComparison
import PoincareConjecture.ParallelMath.Variational.PlaneAreaDistortion
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PoincareConjecture.ParallelMath.GeometricArea
open Set Function Riemannian
open scoped Manifold ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
/-- **Math.** Actual epsilon-close Riemannian metrics control the two-dimensional
area Jacobian on every reference-orthonormal tangent plane. -/
theorem epsilonClose_plane_area {epsilon : ℝ} (g0 g : RiemannianMetric I M)
    (h : MorganTianLib.EpsilonClose epsilon g0 g) (p : M)
    (v w : TangentSpace I p) (hv : g0.metricInner p v v = 1)
    (hw : g0.metricInner p w w = 1) (hvw : g0.metricInner p v w = 0) :
    1-epsilon ≤ Real.sqrt (g.metricInner p v v * g.metricInner p w w - (g.metricInner p v w)^2) ∧
    Real.sqrt (g.metricInner p v v * g.metricInner p w w - (g.metricInner p v w)^2) ≤ 1+epsilon :=
/- SWARM_PROOF_BEGIN -/
by
  have he0 : 0 < epsilon := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.1
  have hehalf : epsilon < 1 / 2 := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.2.1
  have hε0 : 0 ≤ epsilon := he0.le
  have hε1 : epsilon < 1 := hehalf.trans (by norm_num)
  apply PoincareConjecture.ParallelMath.Variational.plane_area_distortion
    (g.metricInner p v v) (g.metricInner p v w) (g.metricInner p w w) epsilon hε0 hε1
  intro s t
  have hcmp :=
    PoincareConjecture.ParallelMath.Quantitative.Reference.epsilonClose_metric_comparison
      g0 g h p (s • v + t • w)
  have hexpand (g' : RiemannianMetric I M) (x y : TangentSpace I p) :
      g'.metricInner p (s • x + t • y) (s • x + t • y)
        = s * (s * g'.metricInner p x x) + s * (t * g'.metricInner p x y)
          + (t * (s * g'.metricInner p y x) + t * (t * g'.metricInner p y y)) := by
    rw [g'.metricInner_add_left, g'.metricInner_add_right, g'.metricInner_add_right,
      g'.metricInner_smul_left, g'.metricInner_smul_left, g'.metricInner_smul_left,
      g'.metricInner_smul_left, g'.metricInner_smul_right, g'.metricInner_smul_right,
      g'.metricInner_smul_right, g'.metricInner_smul_right]
  have hg :
      g.metricInner p (s • v + t • w) (s • v + t • w)
        = g.metricInner p v v * s ^ 2 + 2 * g.metricInner p v w * s * t
          + g.metricInner p w w * t ^ 2 := by
    rw [hexpand g v w, g.metricInner_comm p w v]
    ring
  have hg0 :
      g0.metricInner p (s • v + t • w) (s • v + t • w) = s ^ 2 + t ^ 2 := by
    rw [hexpand g0 v w, g0.metricInner_comm p w v, hv, hw, hvw]
    ring
  rw [hg, hg0] at hcmp
  exact hcmp
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.GeometricArea
