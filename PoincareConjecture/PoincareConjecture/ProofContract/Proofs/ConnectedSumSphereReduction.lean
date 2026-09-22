import PoincareConjecture.ProofContract.Proofs.DoubleBallGluingRecursive
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff

/-- Explicit open relative Schoenflies obligation. It concerns a manifold already
homeomorphic to S3 and its actual coordinate-ball complement, not arbitrary M. -/
def SphereComplementBallStatement : Prop :=
  ∀ A : ClosedThreeManifold.{u}, Nonempty (A ≃ₜ Sphere3) → ∀ a : CoordinateBall A,
    ∃ (e : a.Complement ≃ₜ DoubleBall.Ball) (k : Sphere2 ≃ₜ Sphere2),
      ∀ s : Sphere2, e (a.boundary s) = DoubleBall.boundary (k s)

/-- Conditional assembly into the exact unchanged V1 connected-sum sphere goal.
This theorem does NOT discharge the relative Schoenflies input. -/
theorem connectedSumSphere_of_complement_ball
    (recognition : SphereComplementBallStatement.{u}) : ConnectedSumSphereStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro A B M hp hA hB
  rcases hp with ⟨p⟩
  rcases hA with ⟨hA⟩
  rcases hB with ⟨hB⟩
  obtain ⟨eA, kA, heA⟩ := recognition A ⟨hA⟩ p.leftBall
  obtain ⟨eB, kB, heB⟩ := recognition B ⟨hB⟩ p.rightBall
  let h : Sphere2 ≃ₜ Sphere2 := (kA.symm.trans p.gluing).trans kB
  have heA_symm (s : Sphere2) :
      eA.symm (DoubleBall.boundary s) = p.leftBall.boundary (kA.symm s) := by
    have hs : DoubleBall.boundary s =
        eA (p.leftBall.boundary (kA.symm s)) := by
      simpa using (heA (kA.symm s)).symm
    rw [hs]
    exact eA.symm_apply_apply _
  have heB_symm (s : Sphere2) :
      eB.symm (DoubleBall.boundary s) = p.rightBall.boundary (kB.symm s) := by
    have hs : DoubleBall.boundary s =
        eB (p.rightBall.boundary (kB.symm s)) := by
      simpa using (heB (kB.symm s)).symm
    rw [hs]
    exact eB.symm_apply_apply _
  have hforward : ∀ x y,
      connectedSumSeam p.leftBall p.rightBall p.gluing x y →
        DoubleBall.seam h (Sum.map eA eB x) (Sum.map eA eB y) := by
    intro x y hxy
    rcases hxy with ⟨s, rfl, rfl⟩
    refine ⟨kA s, ?_, ?_⟩
    · simpa [Sum.map] using
        congrArg (fun z : DoubleBall.Ball =>
          (Sum.inl z : DoubleBall.Ball ⊕ DoubleBall.Ball)) (heA s)
    · simpa [Sum.map, h] using
        congrArg (fun z : DoubleBall.Ball =>
          (Sum.inr z : DoubleBall.Ball ⊕ DoubleBall.Ball)) (heB (p.gluing s))
  have hbackward : ∀ x y,
      DoubleBall.seam h x y →
        connectedSumSeam p.leftBall p.rightBall p.gluing
          (Sum.map eA.symm eB.symm x) (Sum.map eA.symm eB.symm y) := by
    intro x y hxy
    rcases hxy with ⟨s, rfl, rfl⟩
    refine ⟨kA.symm s, ?_, ?_⟩
    · simpa [Sum.map] using
        congrArg (fun z : p.leftBall.Complement =>
          (Sum.inl z : p.leftBall.Complement ⊕ p.rightBall.Complement)) (heA_symm s)
    · simpa [Sum.map, h] using
        congrArg (fun z : p.rightBall.Complement =>
          (Sum.inr z : p.leftBall.Complement ⊕ p.rightBall.Complement))
          (heB_symm (h s))
  have hforward' : ∀ x y,
      connectedSumSeam p.leftBall p.rightBall p.gluing x y →
        Quot.mk (DoubleBall.seam h) (Sum.map eA eB x) =
          Quot.mk (DoubleBall.seam h) (Sum.map eA eB y) := by
    intro x y hxy
    exact Quot.sound (hforward x y hxy)
  have hbackward' : ∀ x y,
      DoubleBall.seam h x y →
        Quot.mk (connectedSumSeam p.leftBall p.rightBall p.gluing)
            (Sum.map eA.symm eB.symm x) =
          Quot.mk (connectedSumSeam p.leftBall p.rightBall p.gluing)
            (Sum.map eA.symm eB.symm y) := by
    intro x y hxy
    exact Quot.sound (hbackward x y hxy)
  let F : ConnectedSumSpace p.leftBall p.rightBall p.gluing → DoubleBall.Space h :=
    Quot.lift (fun x => Quot.mk (DoubleBall.seam h) (Sum.map eA eB x)) hforward'
  let G : DoubleBall.Space h → ConnectedSumSpace p.leftBall p.rightBall p.gluing :=
    Quot.lift (fun x =>
      Quot.mk (connectedSumSeam p.leftBall p.rightBall p.gluing)
        (Sum.map eA.symm eB.symm x)) hbackward'
  have hF : Continuous F := by
    exact continuous_quot_lift hforward'
      (continuous_quot_mk.comp (eA.continuous.sumMap eB.continuous))
  have hG : Continuous G := by
    exact continuous_quot_lift hbackward'
      (continuous_quot_mk.comp (eA.continuous_symm.sumMap eB.continuous_symm))
  have hGF : ∀ x, G (F x) = x := by
    intro x
    induction x using Quot.induction_on with
    | h q =>
      cases q with
      | inl x => simp [F, G, Sum.map]
      | inr y => simp [F, G, Sum.map]
  have hFG : ∀ y, F (G y) = y := by
    intro y
    induction y using Quot.induction_on with
    | h q =>
      cases q with
      | inl x => simp [F, G, Sum.map]
      | inr y => simp [F, G, Sum.map]
  let T : ConnectedSumSpace p.leftBall p.rightBall p.gluing ≃ₜ DoubleBall.Space h :=
    { toEquiv :=
        { toFun := F
          invFun := G
          left_inv := hGF
          right_inv := hFG }
      continuous_toFun := hF
      continuous_invFun := hG }
  obtain ⟨E⟩ := doubleBall_arbitrary_gluing_recursive h
  exact ⟨p.realization.trans (T.trans E)⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
