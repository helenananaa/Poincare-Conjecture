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

/-- **Math.** Read the genuine Riemannian path length as the explicit chosen metric-speed integral. -/
theorem metricPathLength_eq_integral (g : RiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) :
    metricPathLength g γ a b =
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt
        (g.metricInner (γ t) (mfderiv 𝓘(ℝ,ℝ) I γ t 1) (mfderiv 𝓘(ℝ,ℝ) I γ t 1))) :=
/- SWARM_PROOF_BEGIN -/
by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  unfold metricPathLength
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  rw [Riemannian.enorm_tangent_eq_sqrt_metricInner (I := I) g (γ t)
    (mfderiv 𝓘(ℝ, ℝ) I γ t 1)]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
