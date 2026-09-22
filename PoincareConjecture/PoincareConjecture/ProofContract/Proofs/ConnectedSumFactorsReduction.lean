import PoincareConjecture.ProofContract.Proofs.SimplyConnectedPi1
import PoincareConjecture.ProofContract.Proofs.DoubleBallCore
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Function Topology
open scoped Topology Manifold ContDiff
/-- Open van Kampen boundary, stated for every genuine presented connected sum. -/
def ConnectedSumPi1EmbeddingStatement : Prop :=
  ∀ A B M : ClosedThreeManifold.{u}, ConnectedSumPresentation A B M →
    ∃ (a : A) (b : B) (m : M)
      (fa : FundamentalGroup A a →* FundamentalGroup M m)
      (fb : FundamentalGroup B b →* FundamentalGroup M m),
      Injective fa ∧ Injective fb

/-- Conditional reduction into the unchanged V1 factor goal; the embedding producer remains open. -/
theorem connectedSumFactors_of_pi1_embeddings
    (embedding : ConnectedSumPi1EmbeddingStatement.{u}) : ConnectedSumFactorsStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro A B M hP hM
  letI : SimplyConnectedSpace M := hM
  obtain ⟨p⟩ := hP
  obtain ⟨a, b, m, fa, fb, hfa, hfb⟩ := embedding A B M p
  have hA : Subsingleton (FundamentalGroup A a) := hfa.subsingleton
  have hB : Subsingleton (FundamentalGroup B b) := hfb.subsingleton
  exact ⟨simplyConnected_of_trivial_pi1 A a hA,
    simplyConnected_of_trivial_pi1 B b hB⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
