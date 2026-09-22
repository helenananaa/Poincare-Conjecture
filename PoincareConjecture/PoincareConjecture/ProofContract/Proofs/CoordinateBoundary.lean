import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- The actual coordinate-ball boundary is embedded in its punctured complement. -/
theorem coordinate_boundary_isClosedEmbedding {M : ClosedThreeManifold.{u}}
    (b : CoordinateBall M) : IsClosedEmbedding b.boundary :=
/- SWARM_PROOF_BEGIN -/
by
  have hsrc : ∀ x : Sphere2, (x : Euclidean3) ∈ b.parametrization.source := by
    intro x
    have hxnorm : ‖(x : Euclidean3)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    exact b.contains_two (by simp [Metric.mem_closedBall, hxnorm])
  have hcont : Continuous b.boundary := by
    apply Continuous.subtype_mk
    exact b.parametrization.continuousOn.comp_continuous continuous_subtype_val hsrc
  have hinj : Function.Injective b.boundary := by
    intro x y hxy
    have hxy' : b.parametrization x = b.parametrization y := congrArg Subtype.val hxy
    have h := congrArg b.parametrization.symm hxy'
    apply Subtype.ext
    simpa only [b.parametrization.left_inv (hsrc x),
      b.parametrization.left_inv (hsrc y)] using h
  exact hcont.isClosedEmbedding hinj
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
