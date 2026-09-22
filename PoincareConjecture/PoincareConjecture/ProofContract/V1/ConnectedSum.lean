import PoincareConjecture.ProofContract.V1.Manifolds

/-!
# A concrete, choice-dependent connected-sum presentation

The removed balls are coordinate balls with a larger coordinate neighborhood,
not arbitrary possibly wild embeddings. The gluing space is the actual
quotient of the punctured disjoint union, identifying only the two boundary
spheres. No classification, fundamental-group rule, or sphere identity is a
field of these definitions. Those are separate open theorem obligations.
-/

universe u
namespace PoincareConjecture.ProofContract.V1
open Set

/-- A unit coordinate ball whose closed radius-two neighborhood is in the chart. -/
structure CoordinateBall (M : ClosedThreeManifold.{u}) where
  parametrization : OpenPartialHomeomorph Euclidean3 M
  contains_two : Metric.closedBall 0 2 ⊆ parametrization.source

namespace CoordinateBall
variable {M : ClosedThreeManifold} (b : CoordinateBall M)

def removed : Set M := b.parametrization '' Metric.ball 0 1
abbrev Complement := {x : M // x ∉ b.removed}

/-- The standard unit sphere maps into the complement of the removed open ball. -/
def boundary (x : Sphere2) : b.Complement := by
  refine ⟨b.parametrization x, ?_⟩
  rintro ⟨y, hy, he⟩
  have hxnorm : ‖(x : Euclidean3)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hynorm : ‖y‖ < 1 := by simpa using hy
  have hxsrc : (x : Euclidean3) ∈ b.parametrization.source :=
    b.contains_two (by simp [Metric.mem_closedBall, hxnorm])
  have hysrc : y ∈ b.parametrization.source :=
    b.contains_two (by simpa [Metric.mem_closedBall] using (show ‖y‖ ≤ 2 by linarith))
  have hxy : y = (x : Euclidean3) := by
    have h := congrArg b.parametrization.symm he
    simpa only [b.parametrization.left_inv hysrc, b.parametrization.left_inv hxsrc] using h
  rw [hxy, hxnorm] at hynorm
  exact (lt_irrefl (1 : ℝ)) hynorm

end CoordinateBall

/-- Directed seam generators; `Quot` takes their equivalence closure. -/
def connectedSumSeam {A B : ClosedThreeManifold.{u}}
    (a : CoordinateBall A) (b : CoordinateBall B) (glue : Sphere2 ≃ₜ Sphere2)
    (x y : a.Complement ⊕ b.Complement) : Prop :=
  ∃ s : Sphere2, x = Sum.inl (a.boundary s) ∧ y = Sum.inr (b.boundary (glue s))

/-- Quotient topology, not a formal symbol for a connected sum. -/
abbrev ConnectedSumSpace {A B : ClosedThreeManifold.{u}}
    (a : CoordinateBall A) (b : CoordinateBall B) (glue : Sphere2 ≃ₜ Sphere2) :=
  Quot (connectedSumSeam a b glue)

/-- An actual homeomorphism to this specified connected-sum quotient. -/
structure ConnectedSumPresentation (A B M : ClosedThreeManifold.{u}) where
  leftBall : CoordinateBall A
  rightBall : CoordinateBall B
  gluing : Sphere2 ≃ₜ Sphere2
  realization : M ≃ₜ ConnectedSumSpace leftBall rightBall gluing

end PoincareConjecture.ProofContract.V1
