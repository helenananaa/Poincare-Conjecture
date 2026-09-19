import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
import MorganTianLib.Ch03.RicciFlow.DistanceVariation
import ReferenceBridges.Quantitative.EpsilonSpeedComparison

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

/-- **Math.** Actual epsilon-close metrics compare actual Riemannian path integrals; no finite-length assumption. -/
theorem epsilonClose_path_integral_twoSided {epsilon : ℝ}
    (g0 g : Riemannian.RiemannianMetric I M) (h : MorganTianLib.EpsilonClose epsilon g0 g)
    {x y : M} (gamma : Path x y) :
    ENNReal.ofReal (Real.sqrt (1-epsilon)) * MorganTianLib.metricPathIntegral g0 gamma ≤
      MorganTianLib.metricPathIntegral g gamma ∧
    MorganTianLib.metricPathIntegral g gamma ≤
      ENNReal.ofReal (Real.sqrt (1+epsilon)) * MorganTianLib.metricPathIntegral g0 gamma :=
/- SWARM_PROOF_BEGIN -/
by
  have hspd :=
    PoincareConjecture.ParallelMath.Quantitative.Reference.epsilonClose_speed_comparison
      (epsilon := epsilon) g0 g h
  have hlo : 0 ≤ Real.sqrt (1 - epsilon) := Real.sqrt_nonneg _
  have hhi : 0 ≤ Real.sqrt (1 + epsilon) := Real.sqrt_nonneg _
  constructor
  · unfold MorganTianLib.metricPathIntegral
    calc
      ENNReal.ofReal (Real.sqrt (1 - epsilon)) *
          (∫⁻ t, ENNReal.ofReal (Real.sqrt (g0.metricInner (gamma t)
            (mfderiv% gamma t 1) (mfderiv% gamma t 1)))) =
        ∫⁻ t, ENNReal.ofReal (Real.sqrt (1 - epsilon)) *
          ENNReal.ofReal (Real.sqrt (g0.metricInner (gamma t)
            (mfderiv% gamma t 1) (mfderiv% gamma t 1))) := by
        exact (MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ t, ENNReal.ofReal (Real.sqrt (g.metricInner (gamma t)
            (mfderiv% gamma t 1) (mfderiv% gamma t 1))) := by
        apply MeasureTheory.lintegral_mono
        intro t
        change
          ENNReal.ofReal (Real.sqrt (1 - epsilon)) *
              ENNReal.ofReal (Real.sqrt (g0.metricInner (gamma t)
                (mfderiv% gamma t 1) (mfderiv% gamma t 1))) ≤
            ENNReal.ofReal (Real.sqrt (g.metricInner (gamma t)
              (mfderiv% gamma t 1) (mfderiv% gamma t 1)))
        rw [← ENNReal.ofReal_mul hlo]
        exact ENNReal.ofReal_le_ofReal (hspd (gamma t) (mfderiv% gamma t 1)).1
  · unfold MorganTianLib.metricPathIntegral
    calc
      (∫⁻ t, ENNReal.ofReal (Real.sqrt (g.metricInner (gamma t)
        (mfderiv% gamma t 1) (mfderiv% gamma t 1)))) ≤
        ∫⁻ t, ENNReal.ofReal (Real.sqrt (1 + epsilon)) *
          ENNReal.ofReal (Real.sqrt (g0.metricInner (gamma t)
            (mfderiv% gamma t 1) (mfderiv% gamma t 1))) := by
        apply MeasureTheory.lintegral_mono
        intro t
        change
          ENNReal.ofReal (Real.sqrt (g.metricInner (gamma t)
            (mfderiv% gamma t 1) (mfderiv% gamma t 1))) ≤
          ENNReal.ofReal (Real.sqrt (1 + epsilon)) *
            ENNReal.ofReal (Real.sqrt (g0.metricInner (gamma t)
              (mfderiv% gamma t 1) (mfderiv% gamma t 1)))
        rw [← ENNReal.ofReal_mul hhi]
        exact ENNReal.ofReal_le_ofReal (hspd (gamma t) (mfderiv% gamma t 1)).2
      _ = ENNReal.ofReal (Real.sqrt (1 + epsilon)) *
          (∫⁻ t, ENNReal.ofReal (Real.sqrt (g0.metricInner (gamma t)
            (mfderiv% gamma t 1) (mfderiv% gamma t 1)))) := by
        rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport.Reference
