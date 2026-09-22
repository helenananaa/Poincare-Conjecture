import PoincareConjecture.ProofContract.Proofs.DoubleBallSphereRecursive
import PoincareConjecture.ProofContract.Proofs.AlexanderExtension
import PoincareConjecture.ProofContract.Proofs.DoubleBallCore
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 DoubleBall Set Function Topology
open scoped Topology Manifold ContDiff
/-- Arbitrary boundary homeomorphisms of two real closed balls give the three-sphere. -/
theorem doubleBall_arbitrary_gluing_recursive (h : Sphere2 ≃ₜ Sphere2) :
    Nonempty (Space h ≃ₜ Sphere3) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨H, hH⟩ := sphere_homeomorph_extends_closedBall h
  have hH_boundary (s : Sphere2) : H (boundary s) = boundary (h s) := by
    apply Subtype.ext
    simpa [boundary] using hH s
  have hH_symm_boundary (s : Sphere2) : H.symm (boundary (h s)) = boundary s := by
    rw [← hH_boundary s]
    exact H.symm_apply_apply _
  have hforward : ∀ p q, seam h p q →
      seam (Homeomorph.refl Sphere2)
        (Sum.map (Homeomorph.refl Ball) H.symm p)
        (Sum.map (Homeomorph.refl Ball) H.symm q) := by
    intro p q hpq
    rcases hpq with ⟨s, rfl, rfl⟩
    refine ⟨s, ?_, ?_⟩
    · rfl
    · simpa [Sum.map] using congrArg (fun z : Ball => (Sum.inr z : Ball ⊕ Ball))
        (hH_symm_boundary s)
  have hbackward : ∀ p q, seam (Homeomorph.refl Sphere2) p q →
      seam h
        (Sum.map (Homeomorph.refl Ball) H p)
        (Sum.map (Homeomorph.refl Ball) H q) := by
    intro p q hpq
    rcases hpq with ⟨s, rfl, rfl⟩
    refine ⟨s, ?_, ?_⟩
    · rfl
    · simpa [Sum.map] using congrArg (fun z : Ball => (Sum.inr z : Ball ⊕ Ball))
        (hH_boundary s)
  have hforward' : ∀ p q, seam h p q →
      Quot.mk (seam (Homeomorph.refl Sphere2))
          (Sum.map (Homeomorph.refl Ball) H.symm p) =
        Quot.mk (seam (Homeomorph.refl Sphere2))
          (Sum.map (Homeomorph.refl Ball) H.symm q) := by
    intro p q hpq
    exact Quot.sound (hforward p q hpq)
  have hbackward' : ∀ p q, seam (Homeomorph.refl Sphere2) p q →
      Quot.mk (seam h) (Sum.map (Homeomorph.refl Ball) H p) =
        Quot.mk (seam h) (Sum.map (Homeomorph.refl Ball) H q) := by
    intro p q hpq
    exact Quot.sound (hbackward p q hpq)
  let F : Space h → Space (Homeomorph.refl Sphere2) :=
    Quot.lift (fun p => Quot.mk (seam (Homeomorph.refl Sphere2))
      (Sum.map (Homeomorph.refl Ball) H.symm p)) hforward'
  let G : Space (Homeomorph.refl Sphere2) → Space h :=
    Quot.lift (fun p => Quot.mk (seam h)
      (Sum.map (Homeomorph.refl Ball) H p)) hbackward'
  have hF : Continuous F := by
    exact continuous_quot_lift hforward'
      (continuous_quot_mk.comp ((Homeomorph.refl Ball).continuous.sumMap H.symm.continuous))
  have hG : Continuous G := by
    exact continuous_quot_lift hbackward'
      (continuous_quot_mk.comp ((Homeomorph.refl Ball).continuous.sumMap H.continuous))
  have hGF : ∀ x, G (F x) = x := by
    intro x
    induction x using Quot.induction_on with
    | h p =>
      cases p with
      | inl x => simp [F, G, Sum.map]
      | inr y => simp [F, G, Sum.map]
  have hFG : ∀ y, F (G y) = y := by
    intro y
    induction y using Quot.induction_on with
    | h p =>
      cases p with
      | inl x => simp [F, G, Sum.map]
      | inr y => simp [F, G, Sum.map]
  let T : Space h ≃ₜ Space (Homeomorph.refl Sphere2) :=
    { toEquiv :=
        { toFun := F
          invFun := G
          left_inv := hGF
          right_inv := hFG }
      continuous_toFun := hF
      continuous_invFun := hG }
  obtain ⟨E⟩ := doubleBall_identity_sphere_recursive
  exact ⟨T.trans E⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
