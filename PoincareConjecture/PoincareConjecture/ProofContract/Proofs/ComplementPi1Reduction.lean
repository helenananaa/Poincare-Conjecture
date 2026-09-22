import PoincareConjecture.ProofContract.Proofs.ConnectedSumPinch
import PoincareConjecture.ProofContract.Proofs.ConnectedSumRightPinch
import PoincareConjecture.ProofContract.Proofs.Pi1SurjectionTransfer
import PoincareConjecture.ProofContract.Proofs.SimplyConnectedPi1
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Open local-topology obligation; no instance or axiom asserts it. -/
def CoordinateComplementPi1SurjectiveStatement : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) (b : CoordinateBall M),
    ∃ c : b.Complement, Surjective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(b.Complement, M)) c)
/-- Conditional reduction using the actual left and right pinch maps. -/
theorem connectedSumFactors_of_complement_surjection
    (surjectivity : CoordinateComplementPi1SurjectiveStatement.{u}) :
    ConnectedSumFactorsStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro A B M hP hM
  obtain ⟨p⟩ := hP
  letI : SimplyConnectedSpace M := hM
  obtain ⟨cA, hcA⟩ := surjectivity A p.leftBall
  obtain ⟨cB, hcB⟩ := surjectivity B p.rightBall
  obtain ⟨rA, hrA⟩ := connectedSum_left_pinch p
  obtain ⟨rB, hrB⟩ := connectedSum_right_pinch p
  let jA : C(p.leftBall.Complement, M) :=
    ⟨fun x => p.realization.symm
        (Quot.mk (connectedSumSeam p.leftBall p.rightBall p.gluing) (Sum.inl x)),
      p.realization.symm.continuous.comp
        (continuous_quot_mk.comp continuous_inl)⟩
  let jB : C(p.rightBall.Complement, M) :=
    ⟨fun y => p.realization.symm
        (Quot.mk (connectedSumSeam p.leftBall p.rightBall p.gluing) (Sum.inr y)),
      p.realization.symm.continuous.comp
        (continuous_quot_mk.comp continuous_inr)⟩
  let gA : C(p.leftBall.Complement, A) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let gB : C(p.rightBall.Complement, B) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have hcompA : rA.comp jA = gA := by
    ext x
    change rA (p.realization.symm
      (Quot.mk (connectedSumSeam p.leftBall p.rightBall p.gluing) (Sum.inl x))) =
      (x : A)
    exact hrA x
  have hcompB : rB.comp jB = gB := by
    ext y
    change rB (p.realization.symm
      (Quot.mk (connectedSumSeam p.leftBall p.rightBall p.gluing) (Sum.inr y))) =
      (y : B)
    exact hrB y
  have hpiA := pi1_trivial_from_surjective_factorization jA rA gA hcompA cA hcA
  have hpiB := pi1_trivial_from_surjective_factorization jB rB gB hcompB cB hcB
  exact ⟨simplyConnected_of_trivial_pi1 A (cA : A) (by simpa [gA] using hpiA),
    simplyConnected_of_trivial_pi1 B (cB : B) (by simpa [gB] using hpiB)⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
