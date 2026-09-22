import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Continuous maps agreeing on the actual seam descend to the actual quotient. -/
theorem connectedSum_continuous_pasting {A B : ClosedThreeManifold.{u}}
    (a : CoordinateBall A) (b : CoordinateBall B) (glue : Sphere2 ≃ₜ Sphere2)
    {Y : Type*} [TopologicalSpace Y]
    (f : C(a.Complement, Y)) (g : C(b.Complement, Y))
    (hfg : ∀ s : Sphere2, f (a.boundary s) = g (b.boundary (glue s))) :
    ∃! F : C(ConnectedSumSpace a b glue, Y),
      (∀ x, F (Quot.mk (connectedSumSeam a b glue) (Sum.inl x)) = f x) ∧
      (∀ y, F (Quot.mk (connectedSumSeam a b glue) (Sum.inr y)) = g y) :=
/- SWARM_PROOF_BEGIN -/
by
  have hrel : ∀ x y, connectedSumSeam a b glue x y →
      Sum.elim (f : a.Complement → Y) (g : b.Complement → Y) x =
        Sum.elim (f : a.Complement → Y) (g : b.Complement → Y) y := by
    intro x y hxy
    rcases hxy with ⟨s, rfl, rfl⟩
    exact hfg s
  let Ffun : ConnectedSumSpace a b glue → Y :=
    Quot.lift (Sum.elim (f : a.Complement → Y) (g : b.Complement → Y)) hrel
  have hFcont : Continuous Ffun := by
    exact continuous_quot_lift hrel (f.continuous.sumElim g.continuous)
  refine ⟨⟨Ffun, hFcont⟩, ?_, ?_⟩
  · constructor <;> intro x <;> rfl
  · intro G hG
    apply ContinuousMap.ext
    intro z
    induction z using Quot.induction_on with
    | h x =>
      cases x with
      | inl x => exact hG.1 x
      | inr y => exact hG.2 y
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
