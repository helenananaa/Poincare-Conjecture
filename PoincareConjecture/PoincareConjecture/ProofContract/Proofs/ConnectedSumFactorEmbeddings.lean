import PoincareConjecture.ProofContract.Proofs.ConnectedSumFibers
import PoincareConjecture.ProofContract.Proofs.CoordinateOpenCompact
import PoincareConjecture.ProofContract.Proofs.DoubleBallCore
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 DoubleBall Set Function Topology
open scoped Topology Manifold ContDiff
/-- The punctured factors embed as actual closed subspaces of a presented connected sum. -/
theorem connectedSum_factor_closedEmbeddings {A B M : ClosedThreeManifold.{u}}
    (p : ConnectedSumPresentation A B M) :
    IsClosedEmbedding (fun x : p.leftBall.Complement => p.realization.symm
      (Quot.mk (connectedSumSeam p.leftBall p.rightBall p.gluing) (Sum.inl x))) ∧
    IsClosedEmbedding (fun y : p.rightBall.Complement => p.realization.symm
      (Quot.mk (connectedSumSeam p.leftBall p.rightBall p.gluing) (Sum.inr y))) :=
/- SWARM_PROOF_BEGIN -/
by
  letI : CompactSpace p.leftBall.Complement :=
    (coordinate_removed_open_complement_compact p.leftBall).2
  letI : CompactSpace p.rightBall.Complement :=
    (coordinate_removed_open_complement_compact p.rightBall).2
  have hleft : IsClosedEmbedding (fun x : p.leftBall.Complement =>
      p.realization.symm
        (Quot.mk (connectedSumSeam p.leftBall p.rightBall p.gluing) (Sum.inl x))) := by
    apply (p.realization.symm.continuous.comp
      (continuous_quot_mk.comp continuous_inl)).isClosedEmbedding
    intro x y hxy
    apply (connectedSum_quotient_fibers p.leftBall p.rightBall p.gluing).1
    exact p.realization.symm.injective hxy
  have hright : IsClosedEmbedding (fun y : p.rightBall.Complement =>
      p.realization.symm
        (Quot.mk (connectedSumSeam p.leftBall p.rightBall p.gluing) (Sum.inr y))) := by
    apply (p.realization.symm.continuous.comp
      (continuous_quot_mk.comp continuous_inr)).isClosedEmbedding
    intro x y hxy
    apply (connectedSum_quotient_fibers p.leftBall p.rightBall p.gluing).2.1
    exact p.realization.symm.injective hxy
  exact ⟨hleft, hright⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
