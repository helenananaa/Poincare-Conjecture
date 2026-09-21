import MorganTianLib.Ch03.RicciFlow.ChartVolumeScalarLower
import MorganTianLib.Ch01.RiemannianMeasureComparison

open Set MeasureTheory Riemannian
open scoped ContDiff Manifold Topology ENNReal Bundle

noncomputable section
namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
  [SigmaCompactSpace M] [T2Space M]

theorem riemannianMeasure_upper_of_scalar_lower
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {g : ℝ → RiemannianMetric I M} {T C : ℝ}
    (hflow : IsRicciFlowOn g (Icc 0 T))
    (hscalar : ∀ s ∈ Icc (0 : ℝ) T, ∀ p : M,
      -C ≤ scalarCurvatureAt (g s) (g s).leviCivitaConnection
        (canonicalLeviCivita_isLeviCivita (g s)) p)
    {s : Set M} (hs : MeasurableSet s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    riemannianMeasure (I := I) (g t) mu s ≤
      ENNReal.ofReal (Real.exp (C * t)) * riemannianMeasure (I := I) (g 0) mu s := by
/- SWARM_PROOF_BEGIN -/
  have hcomp := riemannianMeasure_global_chartDensity_comparison mu hs
    (g₀ := g 0) (g₁ := g t) (s := s)
    (Cminus := 0) (Cplus := Real.exp (C * t))
    (by norm_num) (Real.exp_pos _).le (by
      intro alpha y hy
      have hy' := chartPreimage_subset_target (I := I) alpha s hy
      refine ⟨by simpa using (chartVolumeDensity_pos (I := I) (g t) alpha hy').le, ?_⟩
      exact chartVolumeDensity_upper_of_scalar_lower hflow hscalar alpha
        hy' ht)
  exact hcomp.2
/- SWARM_PROOF_END -/

end MorganTianLib
