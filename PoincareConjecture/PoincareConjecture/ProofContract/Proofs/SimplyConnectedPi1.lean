import PoincareConjecture.ProofContract.Proofs.DoubleBallCore
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Function Topology
open scoped Topology Manifold ContDiff
/-- For an actual closed connected manifold, trivial pi1 at one basepoint implies simple connectivity. -/
theorem simplyConnected_of_trivial_pi1 (M : ClosedThreeManifold.{u}) (x : M)
    (h : Subsingleton (FundamentalGroup M x)) : SimplyConnectedSpace M :=
/- SWARM_PROOF_BEGIN -/
by
  letI : PathConnectedSpace M :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  have htrivial (y : M) : Subsingleton (FundamentalGroup M y) := by
    let e := FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x y
    letI := h
    exact e.toEquiv.symm.subsingleton
  rw [simply_connected_iff_loops_nullhomotopic]
  exact ⟨inferInstance, fun y γ => by
    letI : Subsingleton (Path.Homotopic.Quotient y y) := htrivial y
    exact Path.Homotopic.Quotient.eq.mp
      (@Subsingleton.elim _ (htrivial y) (⟦γ⟧ : Path.Homotopic.Quotient y y)
        ⟦Path.refl y⟧)⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
