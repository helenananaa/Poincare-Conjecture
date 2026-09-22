import PoincareConjecture.ProofContract.Proofs.ThreeInputRootAssembly

universe u
open PoincareConjecture.ProofContract.V1
open PoincareConjecture.ProofContract.Proofs

/-- An exact-type audit: no extra assumptions may appear in this leaf. -/
theorem stage3_exact_factors : ConnectedSumFactorsStatement.{u} :=
  connectedSum_factors_proved

/-- The unchanged public target, with exactly the three still-unproved inputs. -/
theorem stage3_exact_root (smoothing : SmoothingStatement.{u})
    (geometric : GeometricTraceStatement.{u}) (relativeBall : SphereComplementBallStatement.{u}) :
    TopologicalPoincareStatement.{u} :=
  topological_of_three_contracts smoothing geometric relativeBall

#print axioms stage3_exact_factors
#print axioms coordinate_complement_pi1_surjective
#print axioms connectedSum_factors_proved
#print axioms stage3_exact_root
#print topological_of_three_contracts
