import PoincareConjecture.ProofContract.Proofs.ComplementCapping
import PoincareConjecture.ProofContract.Proofs.ConnectedSumPasting
import PoincareConjecture.ProofContract.Proofs.DoubleBallCore
import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Actual projection to the right closed factor, fixing its punctured complement. -/
theorem connectedSum_right_pinch {A B M : ClosedThreeManifold.{u}}
    (p : ConnectedSumPresentation A B M) :
    ∃ f : C(M, B), ∀ y : p.rightBall.Complement,
      f (p.realization.symm (Quot.mk (connectedSumSeam p.leftBall p.rightBall p.gluing)
        (Sum.inr y))) = (y : B) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨F, hF⟩ := coordinate_complement_capping p.leftBall p.gluing
  let r : C(DoubleBall.Ball, B) :=
    ⟨fun x => p.rightBall.parametrization (x : Euclidean3), by
      apply p.rightBall.parametrization.continuousOn.comp_continuous
        continuous_subtype_val
      intro x
      apply p.rightBall.contains_two
      have hxnorm : ‖(x : Euclidean3)‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
      simpa [Metric.mem_closedBall] using (show ‖(x : Euclidean3)‖ ≤ 2 by linarith)⟩
  let g : C(p.rightBall.Complement, B) :=
    ⟨fun y => (y : B), continuous_subtype_val⟩
  have hfg : ∀ s : Sphere2,
      (r.comp F) (p.leftBall.boundary s) =
        g (p.rightBall.boundary (p.gluing s)) := by
    intro s
    rw [ContinuousMap.comp_apply, hF s]
    change p.rightBall.parametrization ((p.gluing s : Sphere2) : Euclidean3) =
      ((p.rightBall.boundary (p.gluing s) : p.rightBall.Complement) : B)
    rfl
  obtain ⟨H, hH, _⟩ := connectedSum_continuous_pasting
    p.leftBall p.rightBall p.gluing (r.comp F) g hfg
  let f : C(M, B) := H.comp ⟨p.realization, p.realization.continuous⟩
  refine ⟨f, ?_⟩
  intro y
  have hy := hH.2 y
  change H (p.realization (p.realization.symm
    (Quot.mk (connectedSumSeam p.leftBall p.rightBall p.gluing) (Sum.inr y)))) = g y
  rw [p.realization.apply_symm_apply]
  exact hy
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
