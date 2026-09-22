import PoincareConjecture.ProofContract.V1.Root
import PoincareConjecture.ProofContract.V1.Decomposition

/-!
# Explicit remaining propositions

These are propositions to prove, not axioms, instances, or completed theorems.
Their proof arguments remain visible in every conditional assembly theorem.
The geometric producer intentionally freezes only its exact output boundary:
its Ricci-flow/PDE/surgery implementation is not falsely declared frozen.
-/

universe u
namespace PoincareConjecture.ProofContract.V1

def SphereCoverRecognitionStatement : Prop :=
  ∀ M : ClosedThreeManifold.{u}, SimplyConnectedSpace M →
    HasSphereCover M → Nonempty (M ≃ₜ Sphere3)

def HandleExclusionStatement : Prop :=
  ∀ M : ClosedThreeManifold.{u}, SimplyConnectedSpace M → ¬ IsSphereHandle M

/-- The van Kampen input; it makes no sphere-recognition assertion. -/
def ConnectedSumFactorsStatement : Prop :=
  ∀ A B M : ClosedThreeManifold.{u}, Nonempty (ConnectedSumPresentation A B M) →
    SimplyConnectedSpace M → SimplyConnectedSpace A ∧ SimplyConnectedSpace B

/-- A local connected-sum identity, independent of Ricci flow and extinction. -/
def ConnectedSumSphereStatement : Prop :=
  ∀ A B M : ClosedThreeManifold.{u}, Nonempty (ConnectedSumPresentation A B M) →
    Nonempty (A ≃ₜ Sphere3) → Nonempty (B ≃ₜ Sphere3) → Nonempty (M ≃ₜ Sphere3)

/-- Unproved geometric producer: construct a concrete finite topological
reduction. Normalization, controlled flow, extinction, and correspondence of
actual surgery to the rewrites remain mathematical obligations behind this
boundary. A generic flow interface without an implementation does not fill it. -/
def GeometricTraceStatement : Prop :=
  ∀ M : ClosedThreeManifold.{u}, IsSmooth M → SimplyConnectedSpace M →
    FiniteExtinctionTrace [M]

end PoincareConjecture.ProofContract.V1
