import MorganTianLib.Ch02.NeckVolume.EpsilonQuadratic
import MorganTianLib.Ch02.NeckVolume.QuadraticDensity
import MorganTianLib.Ch01.RiemannianMeasureComparison

open Set MeasureTheory Riemannian Matrix Function
open scoped ContDiff Manifold Topology ENNReal Bundle BigOperators

noncomputable section
namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

variable [I.Boundaryless] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

/-- **Math.** The actual canonical measures of epsilon-close metrics are uniformly comparable. -/
theorem riemannianMeasure_comparison_of_epsilonClose
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {epsilon : ℝ} {g0 g : RiemannianMetric I M}
    (hclose : EpsilonClose epsilon g0 g)
    {s : Set M} (hs : MeasurableSet s) :
    ENNReal.ofReal (Real.sqrt ((1 - epsilon) ^ Module.finrank ℝ E)) *
        riemannianMeasure (I := I) g0 mu s ≤ riemannianMeasure (I := I) g mu s ∧
    riemannianMeasure (I := I) g mu s ≤
      ENNReal.ofReal (Real.sqrt ((1 + epsilon) ^ Module.finrank ℝ E)) *
        riemannianMeasure (I := I) g0 mu s := by
/- SWARM_PROOF_BEGIN -/
  have hepsilon : 0 < epsilon := hclose.1
  have hepsilon_half : epsilon < 1 / 2 := hclose.2.1
  have hminus : 0 ≤ 1 - epsilon := by
    linarith
  have hplus : 0 ≤ 1 + epsilon := by
    linarith
  refine riemannianMeasure_global_chartDensity_comparison (I := I) (mu := mu)
    (g₀ := g0) (g₁ := g) (s := s) hs
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) ?_
  intro alpha y hy
  exact chartVolumeDensity_comparison_of_metricInner
    (I := I) (g0 := g0) (g := g) (c0 := 1 - epsilon) (c1 := 1 + epsilon)
    hminus hplus alpha (chartPreimage_subset_target (I := I) alpha s hy)
    (epsilonClose_metricInner_comparison hclose ((extChartAt I alpha).symm y))
/- SWARM_PROOF_END -/

end MorganTianLib
