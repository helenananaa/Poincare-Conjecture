import ReferenceBridges.GlobalTransfer.LengthReadback
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

/-- **Math.** Actual epsilon-close metrics compare the genuine path lengths using square-root constants. -/
theorem epsilonClose_path_length {ε : ℝ} (g0 g : RiemannianMetric I M)
    (h : MorganTianLib.EpsilonClose ε g0 g) (γ : ℝ → M) (a b : ℝ) :
    ENNReal.ofReal (Real.sqrt (1-ε)) * metricPathLength g0 γ a b ≤ metricPathLength g γ a b ∧
    metricPathLength g γ a b ≤ ENNReal.ofReal (Real.sqrt (1+ε)) * metricPathLength g0 γ a b :=
/- SWARM_PROOF_BEGIN -/
by
  have hspd :=
    PoincareConjecture.ParallelMath.Quantitative.Reference.epsilonClose_speed_comparison
      (epsilon := ε) g0 g h
  have hlo : 0 ≤ Real.sqrt (1 - ε) := Real.sqrt_nonneg _
  have hhi : 0 ≤ Real.sqrt (1 + ε) := Real.sqrt_nonneg _
  rw [metricPathLength_eq_integral g0, metricPathLength_eq_integral g]
  constructor
  · calc
      ENNReal.ofReal (Real.sqrt (1 - ε)) *
          (∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (g0.metricInner (γ t)
            (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)))) =
        ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (1 - ε)) *
          ENNReal.ofReal (Real.sqrt (g0.metricInner (γ t)
            (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1))) := by
        exact (MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (g.metricInner (γ t)
            (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1))) := by
        apply MeasureTheory.setLIntegral_mono' measurableSet_Icc
        intro t _ht
        rw [← ENNReal.ofReal_mul hlo]
        exact ENNReal.ofReal_le_ofReal (hspd (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)).1
  · calc
      (∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (g.metricInner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)))) ≤
        ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (1 + ε)) *
          ENNReal.ofReal (Real.sqrt (g0.metricInner (γ t)
            (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1))) := by
        apply MeasureTheory.setLIntegral_mono' measurableSet_Icc
        intro t _ht
        rw [← ENNReal.ofReal_mul hhi]
        exact ENNReal.ofReal_le_ofReal (hspd (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)).2
      _ = ENNReal.ofReal (Real.sqrt (1 + ε)) *
          (∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (g0.metricInner (γ t)
            (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)))) := by
        rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
