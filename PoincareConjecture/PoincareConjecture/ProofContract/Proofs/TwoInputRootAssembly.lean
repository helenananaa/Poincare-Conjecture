import PoincareConjecture.ProofContract.V1.Assembly
import PoincareConjecture.ProofContract.Proofs.CoverRecognition
import PoincareConjecture.ProofContract.Proofs.HandleExclusion
import PoincareConjecture.ProofContract.Proofs.ConnectedSumFactorsProof
import PoincareConjecture.ProofContract.Proofs.ConnectedSumSphereProof
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1
/-- Conditional root: smoothing and the actual geometric trace are still unproved inputs. -/
theorem topological_of_two_contracts (smoothing : SmoothingStatement.{u})
    (geometric : GeometricTraceStatement.{u}) : TopologicalPoincareStatement.{u} :=
  topological_of_contracts smoothing geometric sphere_cover_recognition
    handle_exclusion connectedSum_factors_proved connectedSum_sphere_proved
end PoincareConjecture.ProofContract.Proofs
