import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- The removed ball is genuinely open and its complement is compact. -/
theorem coordinate_removed_open_complement_compact {M : ClosedThreeManifold.{u}}
    (b : CoordinateBall M) : IsOpen b.removed ∧ CompactSpace b.Complement :=
/- SWARM_PROOF_BEGIN -/
by
  have hopen : IsOpen b.removed := by
    exact b.parametrization.isOpen_image_of_subset_source Metric.isOpen_ball (fun x hx =>
      b.contains_two (by
        have hxnorm : ‖x‖ < 1 := by simpa using hx
        simpa [Metric.mem_closedBall] using (show ‖x‖ ≤ 2 by linarith)))
  constructor
  · exact hopen
  · exact isCompact_iff_compactSpace.mp
      ((isClosed_compl_iff.mpr hopen).isCompact)
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
