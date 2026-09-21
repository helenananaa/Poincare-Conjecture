import MorganTianLib.Ch03.RicciFlow.GlobalVolumeScalarLower

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

/-- **Math.** Finite initial volume stays finite. The real-valued inequality may therefore be used
in numerical surgery budgets without incorrectly taking toReal of an infinite measure. -/
theorem finite_real_volume_upper_of_scalar_lower
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {g : ℝ → RiemannianMetric I M} {T C : ℝ}
    (hflow : IsRicciFlowOn g (Icc 0 T))
    (hscalar : ∀ s ∈ Icc (0 : ℝ) T, ∀ p : M,
      -C ≤ scalarCurvatureAt (g s) (g s).leviCivitaConnection
        (canonicalLeviCivita_isLeviCivita (g s)) p)
    {s : Set M} (hs : MeasurableSet s)
    (hfinite : riemannianMeasure (I := I) (g 0) mu s ≠ ⊤)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    riemannianMeasure (I := I) (g t) mu s ≠ ⊤ ∧
      (riemannianMeasure (I := I) (g t) mu s).toReal ≤
        Real.exp (C * t) * (riemannianMeasure (I := I) (g 0) mu s).toReal := by
  have hupper := riemannianMeasure_upper_of_scalar_lower mu hflow hscalar hs ht
  have hright : ENNReal.ofReal (Real.exp (C * t)) *
      riemannianMeasure (I := I) (g 0) mu s ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite
  have hleft : riemannianMeasure (I := I) (g t) mu s ≠ ⊤ :=
    ne_top_of_le_ne_top hright hupper
  refine ⟨hleft, ?_⟩
  have hr := (ENNReal.toReal_le_toReal hleft hright).2 hupper
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos (C * t)).le] using hr

end MorganTianLib
