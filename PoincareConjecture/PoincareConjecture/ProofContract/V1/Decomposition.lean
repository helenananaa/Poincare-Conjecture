import PoincareConjecture.ProofContract.V1.ConnectedSum

/-!
# Finite topological output of the geometric route

A sphere-covered component has a genuine covering map, not a homeomorphism
provided as a field. Handles are the actual space S² × S¹. The inductive
constructors record a finite expression using actual connected-sum quotients.
Producing this data for the input manifold is NOT proved in this module.
-/

universe u
namespace PoincareConjecture.ProofContract.V1

/-- Surjectivity is explicit: it must not be inferred from a convention about
`IsCoveringMap`. No constant-curvature or Ricci-flow result is asserted. -/
def HasSphereCover (M : ClosedThreeManifold.{u}) : Prop :=
  ∃ p : Sphere3 → M, IsCoveringMap p ∧ Function.Surjective p

abbrev SphereHandle := Sphere2 × Circle

def IsSphereHandle (M : ClosedThreeManifold.{u}) : Prop :=
  Nonempty (M ≃ₜ SphereHandle)

/-- Finite standard-factor expression. No empty connected sum is admitted. -/
inductive StandardDecomposition : ClosedThreeManifold.{u} → Prop
  | sphereCovered {M} : HasSphereCover M → StandardDecomposition M
  | handle {M} : IsSphereHandle M → StandardDecomposition M
  | connectedSum {A B M} : Nonempty (ConnectedSumPresentation A B M) →
      StandardDecomposition A → StandardDecomposition B → StandardDecomposition M

/-- An elementary, exact topological rewrite of a finite component list.
Geometric surgery must be related to these rewrites by a separate proof. -/
inductive TopologicalStep : List ClosedThreeManifold.{u} → List ClosedThreeManifold.{u} → Prop
  | discardCovered (before after : List ClosedThreeManifold) (M) : HasSphereCover M →
      TopologicalStep (before ++ M :: after) (before ++ after)
  | discardHandle (before after : List ClosedThreeManifold) (M) : IsSphereHandle M →
      TopologicalStep (before ++ M :: after) (before ++ after)
  | split (before after : List ClosedThreeManifold) (A B M) :
      Nonempty (ConnectedSumPresentation A B M) →
      TopologicalStep (before ++ M :: after) (before ++ A :: B :: after)

/-- A finite topological reduction ending at the empty component list.
This is not a definition of a Ricci flow and does not assume that a flow exists. -/
inductive FiniteExtinctionTrace : List ClosedThreeManifold.{u} → Prop
  | empty : FiniteExtinctionTrace []
  | step {before after} : TopologicalStep before after →
      FiniteExtinctionTrace after → FiniteExtinctionTrace before

end PoincareConjecture.ProofContract.V1
