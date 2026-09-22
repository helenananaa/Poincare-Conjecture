import PoincareConjecture.ProofContract.Proofs.CoordinateOpenCompact
import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- The coordinate-ball closure and frontier agree with the actual closed ball and sphere. -/
theorem coordinate_closure_frontier {M : ClosedThreeManifold.{u}}
    (b : CoordinateBall M) :
    closure b.removed = b.parametrization '' Metric.closedBall 0 1 ∧
    frontier b.removed = b.parametrization '' Metric.sphere 0 1 :=
/- SWARM_PROOF_BEGIN -/
by
  have hclosed_source : Metric.closedBall (0 : Euclidean3) 1 ⊆
      b.parametrization.source := by
    intro x hx
    apply b.contains_two
    have hxnorm : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall] using hx
    simpa [Metric.mem_closedBall] using (show ‖x‖ ≤ 2 by linarith)
  have hcont : ContinuousOn b.parametrization (Metric.closedBall 0 1) :=
    b.parametrization.continuousOn.mono hclosed_source
  have hcompact : IsCompact (b.parametrization '' Metric.closedBall 0 1) :=
    (isCompact_closedBall (0 : Euclidean3) 1).image_of_continuousOn hcont
  have hclosed : IsClosed (b.parametrization '' Metric.closedBall 0 1) :=
    hcompact.isClosed
  have hclosure : closure b.removed = b.parametrization '' Metric.closedBall 0 1 := by
    apply Subset.antisymm
    · apply closure_minimal
      · exact image_mono Metric.ball_subset_closedBall
      · exact hclosed
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ((hcont x hx).mono Metric.ball_subset_closedBall).mem_closure_image
        (by rw [closure_ball 0 one_ne_zero]; exact hx)
  have hinj : Set.InjOn b.parametrization (Metric.closedBall (0 : Euclidean3) 1) := by
    intro x hx y hy hxy
    have h := congrArg b.parametrization.symm hxy
    simpa only [b.parametrization.left_inv (hclosed_source hx),
      b.parametrization.left_inv (hclosed_source hy)] using h
  have hopen : IsOpen b.removed :=
    coordinate_removed_open_complement_compact b |>.1
  constructor
  · exact hclosure
  · calc
      frontier b.removed = closure b.removed \ b.removed := hopen.frontier_eq
      _ = b.parametrization '' Metric.closedBall 0 1 \
          b.parametrization '' Metric.ball 0 1 := by
        rw [hclosure]
        rfl
      _ = b.parametrization '' (Metric.closedBall 0 1 \ Metric.ball 0 1) :=
        (Set.image_sdiff_of_injOn hinj Metric.ball_subset_closedBall).symm
      _ = b.parametrization '' Metric.sphere 0 1 := by
        rw [Metric.closedBall_sdiff_ball]
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
