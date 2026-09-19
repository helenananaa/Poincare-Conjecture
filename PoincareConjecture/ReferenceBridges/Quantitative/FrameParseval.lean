import Mathlib
import PoincareConjecture.ParallelMath.Core
import MorganTianLib.Ch02.EpsilonClose
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PoincareConjecture.ParallelMath.Quantitative.Reference
open Set Function Filter Riemannian
open scoped BigOperators Topology Manifold ContDiff
open MorganTianLib
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Parseval identity in the actual metric-orthonormal frame. -/
theorem metric_frame_parseval (g0 : Riemannian.RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    (∑ i : Fin (Module.finrank ℝ E), (g0.metricInner p v (orthoFrameField g0 p i p))^2) =
      g0.metricInner p v v :=
/- SWARM_PROOF_BEGIN -/
by
  have hp : p ∈ orthoFrameSet (I := I) (M := M) p :=
    mem_orthoFrameSet_self (I := I) p
  have hexp := orthoFrameField_expansion g0 p hp v
  let L : TangentSpace I p →ₗ[ℝ] ℝ :=
    { toFun := fun w => g0.metricInner p v w
      map_add' := g0.metricInner_add_right p v
      map_smul' := fun a w => by
        rw [g0.metricInner_smul_right, RingHom.id_apply, smul_eq_mul] }
  calc ∑ i : Fin (Module.finrank ℝ E),
        (g0.metricInner p v (orthoFrameField g0 p i p)) ^ 2
      = ∑ i, L (g0.metricInner p v (orthoFrameField g0 p i p) •
          orthoFrameField g0 p i p) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          change _ = g0.metricInner p v
            (g0.metricInner p v (orthoFrameField g0 p i p) •
              orthoFrameField g0 p i p)
          rw [g0.metricInner_smul_right, pow_two]
      _ = L (∑ i, g0.metricInner p v (orthoFrameField g0 p i p) •
          orthoFrameField g0 p i p) := (map_sum L _ _).symm
      _ = L v := by rw [← hexp]
      _ = g0.metricInner p v v := rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative.Reference
