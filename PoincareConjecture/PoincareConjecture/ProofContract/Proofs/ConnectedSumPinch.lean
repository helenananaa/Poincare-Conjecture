import PoincareConjecture.ProofContract.Proofs.ComplementCapping
import PoincareConjecture.ProofContract.Proofs.ConnectedSumPasting
import PoincareConjecture.ProofContract.Proofs.DoubleBallCore
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Function Topology
open scoped Topology Manifold ContDiff
/-- A genuine continuous collapse map to the left factor, identical on its punctured complement. -/
theorem connectedSum_left_pinch {A B M : ClosedThreeManifold.{u}}
    (p : ConnectedSumPresentation A B M) :
    ∃ f : C(M, A), ∀ x : p.leftBall.Complement,
      f (p.realization.symm
        (Quot.mk (connectedSumSeam p.leftBall p.rightBall p.gluing) (Sum.inl x))) = (x : A) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨G, hG⟩ := coordinate_complement_capping p.rightBall p.gluing.symm
  let leftMap : C(DoubleBall.Ball, A) := ContinuousMap.mk
    (fun z => p.leftBall.parametrization (z : Euclidean3)) (by
      apply p.leftBall.parametrization.continuousOn.comp_continuous
        continuous_subtype_val
      intro z
      apply p.leftBall.contains_two
      simpa [Metric.mem_closedBall, dist_zero_right] using
        (le_trans z.property (by norm_num : (1 : ℝ) ≤ 2)))
  let left : C(p.leftBall.Complement, A) :=
    ⟨fun x => (x : A), continuous_subtype_val⟩
  let right : C(p.rightBall.Complement, A) := leftMap.comp G
  have hseam : ∀ s : Sphere2,
      left (p.leftBall.boundary s) = right (p.rightBall.boundary (p.gluing s)) := by
    intro s
    rw [show right (p.rightBall.boundary (p.gluing s)) =
      leftMap (G (p.rightBall.boundary (p.gluing s))) by rfl]
    rw [hG (p.gluing s)]
    change p.leftBall.parametrization (s : Euclidean3) =
      p.leftBall.parametrization ((p.gluing.symm (p.gluing s) : Sphere2) : Euclidean3)
    rw [p.gluing.symm_apply_apply]
  obtain ⟨F, hF, _⟩ := connectedSum_continuous_pasting
    p.leftBall p.rightBall p.gluing left right hseam
  let R : C(M, ConnectedSumSpace p.leftBall p.rightBall p.gluing) :=
    ⟨p.realization, p.realization.continuous⟩
  refine ⟨F.comp R, ?_⟩
  intro x
  rw [ContinuousMap.comp_apply]
  change F (p.realization (p.realization.symm
    (Quot.mk (connectedSumSeam p.leftBall p.rightBall p.gluing) (Sum.inl x)))) = (x : A)
  rw [p.realization.apply_symm_apply]
  exact hF.1 x
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
