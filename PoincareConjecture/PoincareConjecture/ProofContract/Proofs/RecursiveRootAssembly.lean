import PoincareConjecture.ProofContract.V1.Assembly
import PoincareConjecture.ProofContract.Proofs.CoverRecognition
import PoincareConjecture.ProofContract.Proofs.HandleExclusion
import PoincareConjecture.ProofContract.Proofs.ConnectedSumFactorsReduction
import PoincareConjecture.ProofContract.Proofs.ConnectedSumSphereReduction
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1

/-- Checked recursive assembly into the unchanged public root.
All four unproved mathematical inputs remain explicit: this is NOT completion. -/
theorem topological_of_refined_contracts
    (smoothing : SmoothingStatement.{u})
    (geometric : GeometricTraceStatement.{u})
    (embedding : ConnectedSumPi1EmbeddingStatement.{u})
    (relativeBall : SphereComplementBallStatement.{u}) : TopologicalPoincareStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  exact topological_of_contracts smoothing geometric sphere_cover_recognition
    handle_exclusion (connectedSumFactors_of_pi1_embeddings embedding)
    (connectedSumSphere_of_complement_ball relativeBall)
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
