import PoincareConjecture.ProofContract.Refinement20260927.Cap
import PoincareConjecture.ParallelImplementation.CapSeamOpenCollar
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedMarkedGluing
open PoincareConjecture.ProofContract.Refinement20260927
theorem marked_gluing : MarkedGluingStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro A B M C D Ctop Dtop bC bD g a b L R hL hR hraw
  have hleft : ∀ s, L.symm (a.boundary s) = bC s := by
    intro s
    rw [← hL s]
    exact L.symm_apply_apply _
  have hright : ∀ s, R.symm (b.boundary s) = bD s := by
    intro s
    rw [← hR s]
    exact R.symm_apply_apply _
  have hforward : ∀ p q,
      rawSeam bC bD g p q →
        PoincareConjecture.ProofContract.V1.connectedSumSeam a b g
          (Sum.map L R p) (Sum.map L R q) := by
    intro p q hpq
    rcases hpq with ⟨s, rfl, rfl⟩
    refine ⟨s, ?_, ?_⟩ <;> simp [Sum.map, hL, hR]
  have hbackward : ∀ p q,
      PoincareConjecture.ProofContract.V1.connectedSumSeam a b g p q →
        rawSeam bC bD g (Sum.map L.symm R.symm p) (Sum.map L.symm R.symm q) := by
    intro p q hpq
    rcases hpq with ⟨s, rfl, rfl⟩
    refine ⟨s, ?_, ?_⟩ <;> simp [Sum.map, hleft, hright]
  have hforward' : ∀ p q,
      rawSeam bC bD g p q →
        Quot.mk (PoincareConjecture.ProofContract.V1.connectedSumSeam a b g)
            (Sum.map L R p) =
          Quot.mk (PoincareConjecture.ProofContract.V1.connectedSumSeam a b g)
            (Sum.map L R q) := by
    intro p q hpq
    exact Quot.sound (hforward p q hpq)
  have hbackward' : ∀ p q,
      PoincareConjecture.ProofContract.V1.connectedSumSeam a b g p q →
        Quot.mk (rawSeam bC bD g) (Sum.map L.symm R.symm p) =
          Quot.mk (rawSeam bC bD g) (Sum.map L.symm R.symm q) := by
    intro p q hpq
    exact Quot.sound (hbackward p q hpq)
  let F : Quot (rawSeam bC bD g) →
      PoincareConjecture.ProofContract.V1.ConnectedSumSpace a b g :=
    Quot.lift (fun p => Quot.mk _ (Sum.map L R p)) hforward'
  let G : PoincareConjecture.ProofContract.V1.ConnectedSumSpace a b g →
      Quot (rawSeam bC bD g) :=
    Quot.lift (fun p => Quot.mk _ (Sum.map L.symm R.symm p)) hbackward'
  have hF : Continuous F := by
    exact continuous_quot_lift hforward'
      (continuous_quot_mk.comp (L.continuous.sumMap R.continuous))
  have hG : Continuous G := by
    exact continuous_quot_lift hbackward'
      (continuous_quot_mk.comp
        (L.continuous_symm.sumMap R.continuous_symm))
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
  let H : Quot (rawSeam bC bD g) ≃ₜ
      PoincareConjecture.ProofContract.V1.ConnectedSumSpace a b g :=
    ⟨⟨F, G, hFG, hGF⟩, hF, hG⟩
  rcases hraw with ⟨hM⟩
  exact ⟨⟨a, b, g, hM.trans H⟩⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedMarkedGluing
