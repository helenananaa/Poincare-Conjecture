import PoincareConjecture.ProofContract.Proofs.ComplementPi1Surjective
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Exact unconditional proof of the frozen V1 connected-sum factors obligation. -/
theorem connectedSum_factors_proved : ConnectedSumFactorsStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  exact connectedSumFactors_of_complement_surjection coordinate_complement_pi1_surjective
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
