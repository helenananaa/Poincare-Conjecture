import ReferenceBridges.GlobalTransfer.DistanceReadback
import ReferenceBridges.GlobalTransfer.EpsilonLength
import ReferenceBridges.GlobalTransfer.Core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set Function Filter MeasureTheory Riemannian Manifold
open scoped Topology BigOperators Manifold ContDiff ENNReal Bundle
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Actual epsilon-close Riemannian metrics compare their original extended distances, not an assumed external distance. -/
theorem epsilonClose_riemannianEDist {ε : ℝ} (g0 g : RiemannianMetric I M)
    (h : MorganTianLib.EpsilonClose ε g0 g) (x y : M) :
    ENNReal.ofReal (Real.sqrt (1-ε))*metricEDist g0 x y ≤ metricEDist g x y ∧
    metricEDist g x y ≤ ENNReal.ofReal (Real.sqrt (1+ε))*metricEDist g0 x y :=
/- SWARM_PROOF_BEGIN -/
by
  have he0 : 0 < ε := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.1
  have he1 : ε < 1 / 2 := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.2.1
  have hsqrt0 : 0 < Real.sqrt (1 - ε) :=
    Real.sqrt_pos.mpr (by linarith)
  have hsqrt1 : 0 < Real.sqrt (1 + ε) :=
    Real.sqrt_pos.mpr (by linarith)
  have hl0 : ENNReal.ofReal (Real.sqrt (1 - ε)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hsqrt0).ne'
  have hlt : ENNReal.ofReal (Real.sqrt (1 - ε)) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hu0 : ENNReal.ofReal (Real.sqrt (1 + ε)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hsqrt1).ne'
  have hut : ENNReal.ofReal (Real.sqrt (1 + ε)) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  rw [metricEDist_eq_joining_inf g0 x y, metricEDist_eq_joining_inf g x y]
  constructor
  · rw [ENNReal.mul_iInf_of_ne hl0 hlt]
    exact iInf_mono fun γ => (epsilonClose_path_length g0 g h γ.1 0 1).1
  · rw [ENNReal.mul_iInf_of_ne hu0 hut]
    exact iInf_mono fun γ => (epsilonClose_path_length g0 g h γ.1 0 1).2
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
