import PoincareConjecture.ParallelMath.Transfer.GramComparison
import ReferenceBridges.GlobalTransfer.Core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set Function Filter MeasureTheory Riemannian Manifold
open scoped Topology BigOperators Manifold ContDiff ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Actual epsilon-close metrics compare Gram areas of all tangent pairs, including rank-deficient ones. -/
theorem epsilonClose_all_pair_area {ε : ℝ} (g0 g : RiemannianMetric I M)
    (h : MorganTianLib.EpsilonClose ε g0 g) (p : M) (v w : TangentSpace I p) :
    (1-ε)*gramArea (metricForm g0 p) v w ≤ gramArea (metricForm g p) v w ∧
      gramArea (metricForm g p) v w ≤ (1+ε)*gramArea (metricForm g0 p) v w :=
/- SWARM_PROOF_BEGIN -/
by
  have he0 : 0 < ε := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.1
  have hehalf : ε < 1 / 2 := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.2.1
  have hε0 : 0 ≤ ε := he0.le
  have hε1 : ε < 1 := hehalf.trans (by norm_num)
  have h0s : ∀ v w : TangentSpace I p,
      metricForm g0 p v w = metricForm g0 p w v := by
    intro v w
    exact g0.metricInner_comm p v w
  have hs : ∀ v w : TangentSpace I p,
      metricForm g p v w = metricForm g p w v := by
    intro v w
    exact g.metricInner_comm p v w
  have h0p : ∀ v : TangentSpace I p, v ≠ 0 → 0 < metricForm g0 p v v := by
    intro v hv
    exact g0.metricInner_self_pos p v hv
  have hbound : ∀ v : TangentSpace I p,
      (1 - ε) * metricForm g0 p v v ≤ metricForm g p v v ∧
        metricForm g p v v ≤ (1 + ε) * metricForm g0 p v v := by
    intro v
    exact PoincareConjecture.ParallelMath.Quantitative.Reference.epsilonClose_metric_comparison
      g0 g h p v
  exact gramArea_metric_comparison (metricForm g0 p) (metricForm g p)
    h0s hs h0p ε hε0 hε1 hbound v w
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
