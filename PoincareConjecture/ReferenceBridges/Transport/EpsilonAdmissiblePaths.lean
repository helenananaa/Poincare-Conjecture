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

/-- **Math.** The same estimate holds for any fixed admissible path class, including an empty class. -/
theorem epsilonClose_admissible_path_infimum {epsilon : ℝ}
    (g0 g : Riemannian.RiemannianMetric I M) (h : MorganTianLib.EpsilonClose epsilon g0 g)
    {x y : M} (admissible : Path x y → Prop) :
    ENNReal.ofReal (Real.sqrt (1-epsilon)) *
        (⨅ gamma : {p : Path x y // admissible p}, MorganTianLib.metricPathIntegral g0 gamma.1) ≤
      (⨅ gamma : {p : Path x y // admissible p}, MorganTianLib.metricPathIntegral g gamma.1) ∧
    (⨅ gamma : {p : Path x y // admissible p}, MorganTianLib.metricPathIntegral g gamma.1) ≤
      ENNReal.ofReal (Real.sqrt (1+epsilon)) *
        (⨅ gamma : {p : Path x y // admissible p}, MorganTianLib.metricPathIntegral g0 gamma.1) :=
/- SWARM_PROOF_BEGIN -/
by
  have he0 : 0 < epsilon := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.1
  have he1 : epsilon < 1 / 2 := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.2.1
  have h1me : 0 < 1 - epsilon :=
    sub_pos.mpr (he1.trans (by norm_num : (1 : ℝ) / 2 < 1))
  have h1pe : 0 < 1 + epsilon := add_pos_of_nonneg_of_pos zero_le_one he0
  exact PoincareConjecture.ParallelMath.Transport.ennreal_infimum_twoSided
    (fun gamma : {p : Path x y // admissible p} =>
      MorganTianLib.metricPathIntegral g0 gamma.1)
    (fun gamma : {p : Path x y // admissible p} =>
      MorganTianLib.metricPathIntegral g gamma.1)
    (ENNReal.ofReal (Real.sqrt (1 - epsilon)))
    (ENNReal.ofReal (Real.sqrt (1 + epsilon)))
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr h1me)))
    ENNReal.ofReal_ne_top
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr h1pe)))
    ENNReal.ofReal_ne_top
    (fun gamma => epsilonClose_path_integral_twoSided g0 g h gamma.1)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport.Reference
