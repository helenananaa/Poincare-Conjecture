import PoincareConjecture.ProofContract.V1.Assembly
import PoincareConjecture.ProofContract.Proofs.CoverRecognition
import PoincareConjecture.ProofContract.Proofs.HandleExclusion
import PoincareConjecture.ProofContract.Proofs.ConnectedSumFactorsProof
import PoincareConjecture.ProofContract.Proofs.ConnectedSumSphereReduction
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Conditional root assembly: smoothing, geometric trace, and relative-ball recognition remain open. -/
theorem topological_of_three_contracts (smoothing : SmoothingStatement.{u})
    (geometric : GeometricTraceStatement.{u}) (relativeBall : SphereComplementBallStatement.{u}) :
    TopologicalPoincareStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  exact topological_of_contracts smoothing geometric sphere_cover_recognition
    handle_exclusion connectedSum_factors_proved
    (connectedSumSphere_of_complement_ball relativeBall)
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
