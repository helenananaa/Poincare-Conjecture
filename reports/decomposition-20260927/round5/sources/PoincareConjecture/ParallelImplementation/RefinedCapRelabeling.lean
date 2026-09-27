import PoincareConjecture.ProofContract.Refinement20260927.CapRelabeling
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedCapRelabeling
open PoincareConjecture.ProofContract.Refinement20260927
theorem cap_relabeling : CapRelabelingStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  intro c d L g hboundary
  obtain ⟨B, hB⟩ :=
    PoincareConjecture.ProofContract.Proofs.sphere_homeomorph_extends_closedBall g
  have hBboundary (s : PoincareConjecture.ProofContract.V1.Sphere2) :
      B (PoincareConjecture.ParallelImplementation.CappedSpaceTopology.boundary s) =
        PoincareConjecture.ParallelImplementation.CappedSpaceTopology.boundary (g s) := by
    apply Subtype.ext
    simpa [PoincareConjecture.ParallelImplementation.CappedSpaceTopology.boundary] using hB s
  have hLback (t : PoincareConjecture.ProofContract.V1.Sphere2) :
      L.symm (d.boundaryMap t) = c.boundaryMap (g.symm t) := by
    rw [← g.apply_symm_apply t, ← hboundary (g.symm t)]
    simp
  have hBback (t : PoincareConjecture.ProofContract.V1.Sphere2) :
      B.symm (PoincareConjecture.ParallelImplementation.CappedSpaceTopology.boundary t) =
        PoincareConjecture.ParallelImplementation.CappedSpaceTopology.boundary (g.symm t) := by
    have h := congrArg B.symm (hBboundary (g.symm t))
    simpa using h.symm
  have hforward : ∀ p q,
      PoincareConjecture.ParallelImplementation.CappedSpaceTopology.capSeam
          c.boundaryMap p q →
        PoincareConjecture.ParallelImplementation.CappedSpaceTopology.capSeam
          d.boundaryMap (Sum.map L B p) (Sum.map L B q) := by
    intro p q hpq
    rcases hpq with ⟨s, rfl, rfl⟩
    refine ⟨g s, ?_, ?_⟩ <;> simp [Sum.map, hboundary s, hBboundary s]
  have hbackward : ∀ p q,
      PoincareConjecture.ParallelImplementation.CappedSpaceTopology.capSeam
          d.boundaryMap p q →
        PoincareConjecture.ParallelImplementation.CappedSpaceTopology.capSeam
          c.boundaryMap (Sum.map L.symm B.symm p) (Sum.map L.symm B.symm q) := by
    intro p q hpq
    rcases hpq with ⟨t, rfl, rfl⟩
    refine ⟨g.symm t, ?_, ?_⟩ <;> simp [Sum.map, hLback t, hBback t]
  have hforward' : ∀ p q,
      PoincareConjecture.ParallelImplementation.CappedSpaceTopology.capSeam
          c.boundaryMap p q →
        Quot.mk (PoincareConjecture.ParallelImplementation.CappedSpaceTopology.capSeam
          d.boundaryMap) (Sum.map L B p) =
          Quot.mk (PoincareConjecture.ParallelImplementation.CappedSpaceTopology.capSeam
            d.boundaryMap) (Sum.map L B q) := by
    intro p q hpq
    exact Quot.sound (hforward p q hpq)
  have hbackward' : ∀ p q,
      PoincareConjecture.ParallelImplementation.CappedSpaceTopology.capSeam
          d.boundaryMap p q →
        Quot.mk (PoincareConjecture.ParallelImplementation.CappedSpaceTopology.capSeam
          c.boundaryMap) (Sum.map L.symm B.symm p) =
          Quot.mk (PoincareConjecture.ParallelImplementation.CappedSpaceTopology.capSeam
            c.boundaryMap) (Sum.map L.symm B.symm q) := by
    intro p q hpq
    exact Quot.sound (hbackward p q hpq)
  let F : PoincareConjecture.ParallelImplementation.CappedSpaceTopology.CappedSpace
      c.boundaryMap →
      PoincareConjecture.ParallelImplementation.CappedSpaceTopology.CappedSpace d.boundaryMap :=
    Quot.lift (fun p => Quot.mk
      (PoincareConjecture.ParallelImplementation.CappedSpaceTopology.capSeam d.boundaryMap)
      (Sum.map L B p)) hforward'
  let G : PoincareConjecture.ParallelImplementation.CappedSpaceTopology.CappedSpace
      d.boundaryMap →
      PoincareConjecture.ParallelImplementation.CappedSpaceTopology.CappedSpace c.boundaryMap :=
    Quot.lift (fun p => Quot.mk
      (PoincareConjecture.ParallelImplementation.CappedSpaceTopology.capSeam c.boundaryMap)
      (Sum.map L.symm B.symm p)) hbackward'
  have hF : Continuous F := by
    exact continuous_quot_lift hforward'
      (continuous_quot_mk.comp (L.continuous.sumMap B.continuous))
  have hG : Continuous G := by
    exact continuous_quot_lift hbackward'
      (continuous_quot_mk.comp (L.continuous_symm.sumMap B.continuous_symm))
  have hGF : ∀ x, G (F x) = x := by
    intro x
    induction x using Quot.induction_on with
    | h p =>
      cases p with
      | inl y => simp [F, G, Sum.map]
      | inr y => simp [F, G, Sum.map]
  have hFG : ∀ y, F (G y) = y := by
    intro y
    induction y using Quot.induction_on with
    | h p =>
      cases p with
      | inl x => simp [F, G, Sum.map]
      | inr x => simp [F, G, Sum.map]
  refine ⟨⟨⟨F, G, hGF, hFG⟩, hF, hG⟩, ?_⟩
  intro x
  simp [F, Sum.map]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedCapRelabeling
