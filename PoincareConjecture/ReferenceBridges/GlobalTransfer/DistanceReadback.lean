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

/-- **Math.** The actual Riemannian distance is the infimum over real C1 joining curves; disconnected endpoints remain at infinity. -/
theorem metricEDist_eq_joining_inf (g : RiemannianMetric I M) (x y : M) :
    metricEDist g x y = ⨅ γ : JoiningCurve I x y, metricPathLength g γ.1 0 1 :=
/- SWARM_PROOF_BEGIN -/
by
  letI : Bundle.RiemannianBundle (fun z : M => TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  change riemannianEDist I x y = ⨅ γ : JoiningCurve I x y, pathELength I γ.1 0 1
  refine le_antisymm ?le ?ge
  · refine le_iInf fun γ => ?_
    exact riemannianEDist_le_pathELength γ.2.2.2 γ.2.1 γ.2.2.1 zero_le_one
  · refine le_of_forall_gt fun r hr => ?_
    obtain ⟨γ, hγ0, hγ1, hγdiff, hlen⟩ := exists_lt_of_riemannianEDist_lt hr
    exact (iInf_le_of_le ⟨γ, hγ0, hγ1, hγdiff⟩ le_rfl).trans_lt hlen
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
