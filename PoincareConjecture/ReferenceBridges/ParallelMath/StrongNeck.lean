import MorganTianLib.Ch03.RicciFlow.EvolvingEpsilonNeck
import ReferenceBridges.ParallelMath.EvolvingDepth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Reference
open Set Function Filter
open scoped BigOperators Topology Manifold ContDiff Bundle RealInnerProductSpace

/-- An evolving neck with at least one unit of backward depth supplies a genuine strong neck. -/
theorem strongNeck_of_depth_ge_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    {epsilon tau : ℝ} {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    {x : M} {t0 : J} (N : MorganTianLib.EvolvingEpsilonNeck epsilon g J x t0 tau)
    (htau : 1 ≤ tau) :
    ∃ N' : MorganTianLib.StrongEpsilonNeck epsilon g J x t0,
      N'.centralNeck = N.centralNeck :=
/- SWARM_PROOF_BEGIN -/
by
  exact evolvingNeck_restrict_depth N 1 zero_lt_one htau
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Reference
