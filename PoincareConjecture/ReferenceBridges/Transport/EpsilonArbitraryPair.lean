import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
import ReferenceBridges.Quantitative.EpsilonMetricComparison
import MorganTianLib.Ch02.EpsilonClose
import PoincareConjecture.ParallelMath.Transport.RelativeGramArea

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport.Reference
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The actual metric controls the area of arbitrary tangent pairs, including rank-deficient pairs. -/
theorem epsilonClose_arbitrary_pair_area {epsilon : ℝ}
    (g0 g : Riemannian.RiemannianMetric I M) (h : MorganTianLib.EpsilonClose epsilon g0 g)
    (p : M) (v w : TangentSpace I p) :
    (1-epsilon)*Real.sqrt (g0.metricInner p v v*g0.metricInner p w w-(g0.metricInner p v w)^2) ≤
      Real.sqrt (g.metricInner p v v*g.metricInner p w w-(g.metricInner p v w)^2) ∧
    Real.sqrt (g.metricInner p v v*g.metricInner p w w-(g.metricInner p v w)^2) ≤
      (1+epsilon)*Real.sqrt (g0.metricInner p v v*g0.metricInner p w w-(g0.metricInner p v w)^2) :=
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
  have hexpand (g' : Riemannian.RiemannianMetric I M) (s t : ℝ)
      (x y : TangentSpace I p) :
      g'.metricInner p (s • x + t • y) (s • x + t • y)
        = s * (s * g'.metricInner p x x) + s * (t * g'.metricInner p x y)
          + (t * (s * g'.metricInner p y x) + t * (t * g'.metricInner p y y)) := by
    rw [g'.metricInner_add_left, g'.metricInner_add_right, g'.metricInner_add_right,
      g'.metricInner_smul_left, g'.metricInner_smul_left, g'.metricInner_smul_left,
      g'.metricInner_smul_left, g'.metricInner_smul_right, g'.metricInner_smul_right,
      g'.metricInner_smul_right, g'.metricInner_smul_right]
  have hform (g' : Riemannian.RiemannianMetric I M) (s t : ℝ) :
      g'.metricInner p (s • v + t • w) (s • v + t • w)
        = g'.metricInner p v v * s ^ 2 + 2 * g'.metricInner p v w * s * t
          + g'.metricInner p w w * t ^ 2 := by
    rw [hexpand g' s t v w, g'.metricInner_comm p w v]
    ring
  apply PoincareConjecture.ParallelMath.Transport.relative_gram_area_distortion
    (g0.metricInner p v v) (g0.metricInner p v w) (g0.metricInner p w w)
    (g.metricInner p v v) (g.metricInner p v w) (g.metricInner p w w)
    epsilon hε0 hε1
  · intro s t
    rw [← hform g0 s t]
    exact g0.metricInner_self_nonneg p (s • v + t • w)
  · intro s t
    have hcmp :=
      PoincareConjecture.ParallelMath.Quantitative.Reference.epsilonClose_metric_comparison
        g0 g h p (s • v + t • w)
    rw [hform g s t, hform g0 s t] at hcmp
    exact hcmp
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport.Reference
