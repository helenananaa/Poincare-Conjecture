import MorganTianLib.Ch02.EpsilonClose
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Reference
open Set Function Filter
open scoped BigOperators Topology Manifold ContDiff Bundle RealInnerProductSpace

/-- Uniform spatial epsilon-closeness survives restriction or reindexing of time. -/
theorem epsilonCloseFamily_reindex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    {T U : Type*} {epsilon : ℝ} (g0 g : T → Riemannian.RiemannianMetric I M)
    (h : MorganTianLib.EpsilonCloseFamily epsilon g0 g) (f : U → T) :
    MorganTianLib.EpsilonCloseFamily epsilon (g0 ∘ f) (g ∘ f) :=
/- SWARM_PROOF_BEGIN -/
by
  rw [MorganTianLib.EpsilonCloseFamily] at h ⊢
  obtain ⟨hεpos, hεhalf, C, hClt, hbound⟩ := h
  refine ⟨hεpos, hεhalf, C, hClt, ?_⟩
  intro u p
  simpa using hbound (f u) p
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Reference
