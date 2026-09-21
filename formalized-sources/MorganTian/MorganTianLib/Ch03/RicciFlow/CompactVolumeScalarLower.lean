import MorganTianLib.Ch01.RiemannianMeasureRegularity
import MorganTianLib.Ch03.RicciFlow.RealVolumeScalarLower

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
  [CompactSpace M] [T2Space M]

/-- **Math.** On a compact source, initial volume finiteness is proved rather than assumed. -/
theorem compact_real_volume_upper_of_scalar_lower
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {g : ℝ → RiemannianMetric I M} {T C : ℝ}
    (hflow : IsRicciFlowOn g (Icc 0 T))
    (hscalar : ∀ s ∈ Icc (0 : ℝ) T, ∀ p : M,
      -C ≤ scalarCurvatureAt (g s) (g s).leviCivitaConnection
        (canonicalLeviCivita_isLeviCivita (g s)) p)
    {s : Set M} (hs : MeasurableSet s) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    riemannianMeasure (I := I) (g t) mu s ≠ ⊤ ∧
      (riemannianMeasure (I := I) (g t) mu s).toReal ≤
        Real.exp (C * t) * (riemannianMeasure (I := I) (g 0) mu s).toReal := by
  have htotal : riemannianMeasure (I := I) (g 0) mu Set.univ < ⊤ :=
    riemannianMeasure_lt_top_of_isCompact mu (g 0) isCompact_univ
  have hfinite : riemannianMeasure (I := I) (g 0) mu s ≠ ⊤ :=
    ne_of_lt ((measure_mono (subset_univ s)).trans_lt htotal)
  exact finite_real_volume_upper_of_scalar_lower mu hflow hscalar hs hfinite ht

end MorganTianLib
