import MorganTianLib.Ch03.RicciFlow.VolumeDensityScalarLower

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

/-- A genuine Ricci-flow chart density estimate from a one-sided scalar curvature bound. -/
theorem chartVolumeDensity_upper_of_scalar_lower
    {g : ℝ → RiemannianMetric I M} {T C : ℝ}
    (hflow : IsRicciFlowOn g (Icc 0 T))
    (hscalar : ∀ s ∈ Icc (0 : ℝ) T, ∀ p : M,
      -C ≤ scalarCurvatureAt (g s) (g s).leviCivitaConnection
        (canonicalLeviCivita_isLeviCivita (g s)) p)
    (alpha : M) {y : E} (hy : y ∈ (extChartAt I alpha).target)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    chartVolumeDensity (I := I) (g t) alpha y ≤
      Real.exp (C * t) * chartVolumeDensity (I := I) (g 0) alpha y := by
/- SWARM_PROOF_BEGIN -/
  let p : M := (extChartAt I alpha).symm y
  let rho : ℝ → ℝ := fun s => chartVolumeDensity (I := I) (g s) alpha y
  let R : ℝ → ℝ := fun s =>
    scalarCurvatureAt (g s) (g s).leviCivitaConnection
      (canonicalLeviCivita_isLeviCivita (g s)) p
  have hderiv : IsVolumeDensityEvolution rho R (Icc 0 T) := by
    intro s hs
    dsimp [rho, R, p]
    exact hasDerivWithinAt_chartVolumeDensity_of_isRicciFlowOn
      hflow alpha hs hy
  have hlower : ∀ s ∈ Icc (0 : ℝ) T, -C ≤ R s := by
    intro s hs
    dsimp [R]
    exact hscalar s hs p
  have hpos : ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ rho s := by
    intro s hs
    dsimp [rho]
    exact (chartVolumeDensity_pos (I := I) (g s) alpha hy).le
  simpa [rho] using volumeDensity_upper_of_scalar_lower
    hderiv hlower hpos ht
/- SWARM_PROOF_END -/

end MorganTianLib
