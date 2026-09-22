import PoincareConjecture.ProofContract.V1.Manifolds

/-!
# Exact public targets (not proofs)

The README's topological assertion is the public root. The blueprint's smooth
assertion is separately named, never substituted for the topological assertion.
Declaring these Props proves neither. No project axiom or proof hole is used.
-/

universe u
namespace PoincareConjecture.ProofContract.V1
open scoped Manifold ContDiff Topology

/-- Public, unconditional mathematical target. No Ricci flow, decomposition,
smoothing, or target-equivalent certificate is included among its hypotheses. -/
def TopologicalPoincareStatement : Prop :=
  ∀ M : ClosedThreeManifold.{u}, SimplyConnectedSpace M → Nonempty (M ≃ₜ Sphere3)

/-- Internal topological conclusion for an already smooth atlas. -/
def SmoothTopologicalPoincareStatement : Prop :=
  ∀ M : ClosedThreeManifold.{u}, IsSmooth M →
    SimplyConnectedSpace M → Nonempty (M ≃ₜ Sphere3)

/-- Stronger smooth endpoint in the existing blueprint. This is a distinct target. -/
def SmoothPoincareStatement : Prop :=
  ∀ M : ClosedThreeManifold.{u}, IsSmooth M →
    SimplyConnectedSpace M → Nonempty (Diffeomorph (𝓡 3) (𝓡 3) M Sphere3 ∞)

/-- Classical smoothing existence is exposed rather than treated as an axiom. -/
def SmoothingStatement : Prop :=
  ∀ M : ClosedThreeManifold.{u}, Nonempty (Smoothing M)

end PoincareConjecture.ProofContract.V1
