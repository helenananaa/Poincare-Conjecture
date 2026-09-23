import PoincareConjecture.ParallelImplementation.MetricCoefficientDerivative
set_option autoImplicit false
noncomputable section
open Filter Riemannian Bundle MorganTianLib
open scoped Manifold Topology ContDiff Bundle
namespace PoincareConjecture.ParallelImplementation.RicciMovingPairing
open PoincareConjecture.ParallelImplementation.MetricCoefficientDerivative
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
/-- Fixed-fiber Ricci pairing, with no separate coefficient-derivative assumption. -/
theorem ricciFlow_metricInner_hasDerivWithinAt
    (g : ℝ → MorganTianLib.RiemannianMetric I M) (J : Set ℝ)
    (hflow : IsRicciFlowOn g J) (hJ : ∀ t ∈ J, UniqueDiffWithinAt ℝ J t)
    (t₀ : ℝ) (ht₀ : t₀ ∈ J) (p : M)
    (X Y : ℝ → TangentSpace I p) (dX dY : TangentSpace I p)
    (hX : HasDerivWithinAt X dX J t₀) (hY : HasDerivWithinAt Y dY J t₀) :
    HasDerivWithinAt (fun t => (g t).metricInner p (X t) (Y t))
      (-2 * ricciTensorAt (g t₀) p (X t₀) (Y t₀) +
       (g t₀).metricInner p dX (Y t₀) + (g t₀).metricInner p (X t₀) dY) J t₀ :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨dh, hdh, hcoeff⟩ := metricCoefficient_hasDerivWithinAt_of_variation
    g (fun t p x y => -2 * ricciTensorAt (g t) p x y)
    J hJ hflow.equation t₀ ht₀ p
  have hthree := (hcoeff.clm_apply hX).clm_apply hY
  simpa only [Riemannian.RiemannianMetric.metricInner,
    ContinuousLinearMap.add_apply, add_assoc, hdh] using hthree
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RicciMovingPairing
