import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
import MorganTianLib.Ch03.RicciFlow.DistanceVariation
import ReferenceBridges.Quantitative.EpsilonSpeedComparison
import PoincareConjecture.ParallelMath.Transport.ExtendedInfimum
import ReferenceBridges.Transport.EpsilonPathIntegrals

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport.Reference
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** Pointwise metric closeness controls the actual C1-path infimum, not an assumed distance comparison. -/
theorem epsilonClose_intrinsic_edist_twoSided {epsilon : ℝ}
    (g0 g : Riemannian.RiemannianMetric I M) (h : MorganTianLib.EpsilonClose epsilon g0 g)
    (x y : M) :
    ENNReal.ofReal (Real.sqrt (1-epsilon)) * MorganTianLib.metricIntrinsicEDist g0 x y ≤
      MorganTianLib.metricIntrinsicEDist g x y ∧
    MorganTianLib.metricIntrinsicEDist g x y ≤
      ENNReal.ofReal (Real.sqrt (1+epsilon)) * MorganTianLib.metricIntrinsicEDist g0 x y :=
/- SWARM_PROOF_BEGIN -/
by
  have he0 : 0 < epsilon := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.1
  have he1 : epsilon < 1 / 2 := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.2.1
  have hsqrt0 : 0 < Real.sqrt (1 - epsilon) :=
    Real.sqrt_pos.mpr (by linarith)
  have hsqrt1 : 0 < Real.sqrt (1 + epsilon) :=
    Real.sqrt_pos.mpr (by linarith)
  have hl0 : ENNReal.ofReal (Real.sqrt (1 - epsilon)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hsqrt0).ne'
  have hu0 : ENNReal.ofReal (Real.sqrt (1 + epsilon)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hsqrt1).ne'
  unfold MorganTianLib.metricIntrinsicEDist
  rw [iInf_psigma', iInf_psigma']
  exact PoincareConjecture.ParallelMath.Transport.ennreal_infimum_twoSided
    (fun p : Σ' γ : Path x y, CMDiff 1 γ =>
      MorganTianLib.metricPathIntegral g0 p.1)
    (fun p : Σ' γ : Path x y, CMDiff 1 γ =>
      MorganTianLib.metricPathIntegral g p.1)
    (ENNReal.ofReal (Real.sqrt (1 - epsilon)))
    (ENNReal.ofReal (Real.sqrt (1 + epsilon)))
    hl0 ENNReal.ofReal_ne_top hu0 ENNReal.ofReal_ne_top
    (fun p =>
      epsilonClose_path_integral_twoSided (epsilon := epsilon) g0 g h p.1)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport.Reference
