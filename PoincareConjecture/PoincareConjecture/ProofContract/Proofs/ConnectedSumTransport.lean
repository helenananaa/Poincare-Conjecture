import PoincareConjecture.ProofContract.Proofs.ConnectedSumPasting
import PoincareConjecture.ProofContract.Proofs.DoubleBallCore
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 DoubleBall Set Function Topology
open scoped Topology Manifold ContDiff
/-- Boundary-compatible homeomorphisms induce a homeomorphism of actual connected-sum quotients. -/
theorem connectedSum_homeomorph_transport {A B C D : ClosedThreeManifold.{u}}
    (a : CoordinateBall A) (b : CoordinateBall B)
    (c : CoordinateBall C) (d : CoordinateBall D)
    (h k : Sphere2 ≃ₜ Sphere2)
    (left : a.Complement ≃ₜ c.Complement) (right : b.Complement ≃ₜ d.Complement)
    (hl : ∀ s : Sphere2, left (a.boundary s) = c.boundary s)
    (hr : ∀ s : Sphere2, right (b.boundary (h s)) = d.boundary (k s)) :
    Nonempty (ConnectedSumSpace a b h ≃ₜ ConnectedSumSpace c d k) :=
/- SWARM_PROOF_BEGIN -/
by
  have hleft : ∀ s : Sphere2, left.symm (c.boundary s) = a.boundary s := by
    intro s
    rw [← hl s]
    exact left.symm_apply_apply _
  have hright : ∀ s : Sphere2, right.symm (d.boundary (k s)) = b.boundary (h s) := by
    intro s
    rw [← hr s]
    exact right.symm_apply_apply _
  have hforward : ∀ p q,
      connectedSumSeam a b h p q →
        connectedSumSeam c d k (Sum.map left right p) (Sum.map left right q) := by
    intro p q hpq
    rcases hpq with ⟨s, rfl, rfl⟩
    refine ⟨s, ?_, ?_⟩
    · simpa [Sum.map] using
        congrArg (fun z : c.Complement => (Sum.inl z : c.Complement ⊕ d.Complement)) (hl s)
    · simpa [Sum.map] using
        congrArg (fun z : d.Complement => (Sum.inr z : c.Complement ⊕ d.Complement)) (hr s)
  have hbackward : ∀ p q,
      connectedSumSeam c d k p q →
        connectedSumSeam a b h (Sum.map left.symm right.symm p)
          (Sum.map left.symm right.symm q) := by
    intro p q hpq
    rcases hpq with ⟨s, rfl, rfl⟩
    refine ⟨s, ?_, ?_⟩
    · simpa [Sum.map] using
        congrArg (fun z : a.Complement => (Sum.inl z : a.Complement ⊕ b.Complement)) (hleft s)
    · simpa [Sum.map] using
        congrArg (fun z : b.Complement => (Sum.inr z : a.Complement ⊕ b.Complement)) (hright s)
  have hforward' : ∀ p q,
      connectedSumSeam a b h p q →
        Quot.mk (connectedSumSeam c d k) (Sum.map left right p) =
          Quot.mk (connectedSumSeam c d k) (Sum.map left right q) := by
    intro p q hpq
    exact Quot.sound (hforward p q hpq)
  have hbackward' : ∀ p q,
      connectedSumSeam c d k p q →
        Quot.mk (connectedSumSeam a b h) (Sum.map left.symm right.symm p) =
          Quot.mk (connectedSumSeam a b h) (Sum.map left.symm right.symm q) := by
    intro p q hpq
    exact Quot.sound (hbackward p q hpq)
  let F : ConnectedSumSpace a b h → ConnectedSumSpace c d k :=
    Quot.lift (fun p => Quot.mk (connectedSumSeam c d k) (Sum.map left right p)) hforward'
  let G : ConnectedSumSpace c d k → ConnectedSumSpace a b h :=
    Quot.lift (fun p => Quot.mk (connectedSumSeam a b h)
      (Sum.map left.symm right.symm p)) hbackward'
  have hF : Continuous F := by
    exact continuous_quot_lift hforward'
      (continuous_quot_mk.comp (left.continuous.sumMap right.continuous))
  have hG : Continuous G := by
    exact continuous_quot_lift hbackward'
      (continuous_quot_mk.comp (left.continuous_symm.sumMap right.continuous_symm))
  have hFG : ∀ x, G (F x) = x := by
    intro x
    induction x using Quot.induction_on with
    | h p =>
      cases p with
      | inl x => simp [F, G, Sum.map]
      | inr y => simp [F, G, Sum.map]
  have hGF : ∀ y, F (G y) = y := by
    intro y
    induction y using Quot.induction_on with
    | h p =>
      cases p with
      | inl x => simp [F, G, Sum.map]
      | inr y => simp [F, G, Sum.map]
  exact ⟨⟨F, G, hFG, hGF⟩, hF, hG⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
