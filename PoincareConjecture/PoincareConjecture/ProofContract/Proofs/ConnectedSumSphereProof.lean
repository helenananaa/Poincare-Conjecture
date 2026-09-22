import PoincareConjecture.ProofContract.Proofs.SphereComplementBallProof
import PoincareConjecture.ProofContract.Proofs.CoordinateOpenExterior
import PoincareConjecture.ProofContract.Proofs.ShrunkCoordinateComplement
import PoincareConjecture.ProofContract.Proofs.CompactChartSqueeze
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
import PoincareConjecture.ProofContract.Proofs.RelativeCompactCollapse
import PoincareConjecture.ProofContract.Proofs.MarkedCollapseRecognition
import PoincareConjecture.ProofContract.Proofs.ConnectedSumSphereReduction
import Mathlib
set_option autoImplicit false
noncomputable section
universe u v
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Filter Topology
open scoped Topology Manifold ContDiff
/-- Exact existing V1 sphere connected-sum leaf, discharged by actual relative-ball recognition. -/
theorem connectedSum_sphere_proved : ConnectedSumSphereStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  exact connectedSumSphere_of_complement_ball sphere_complement_ball_proved
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
