import PoincareConjecture.ProofContract.V1.Obligations
import PoincareConjecture.ProofContract.Proofs.CoordinateBallExists
import PoincareConjecture.ProofContract.Proofs.OpenAnnulus
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Ambient homeomorphisms transport actual coordinate balls and marked complements. -/
theorem coordinate_ball_homeomorph_transport {M N : ClosedThreeManifold.{u}}
    (e : M ≃ₜ N) (a : CoordinateBall M) :
    ∃ b : CoordinateBall N, (∀ z : Euclidean3, b.parametrization z = e (a.parametrization z)) ∧
      ∃ q : a.Complement ≃ₜ b.Complement,
        (∀ x : a.Complement, (q x:N) = e (x:M)) ∧
        ∀ s : Sphere2, q (a.boundary s) = b.boundary s :=
/- SWARM_PROOF_BEGIN -/
by
  let p : OpenPartialHomeomorph Euclidean3 N :=
    a.parametrization.transHomeomorph e
  let b : CoordinateBall N :=
    ⟨p, by
      simpa [p, OpenPartialHomeomorph.transHomeomorph_eq_trans] using a.contains_two⟩
  have hremoved : b.removed = e '' a.removed := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨a.parametrization z, ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨z, hz, hzx⟩, rfl⟩
      exact ⟨z, hz, hzx ▸ rfl⟩
  have hiff : ∀ x : M, x ∉ a.removed ↔ e x ∉ b.removed := by
    intro x
    rw [hremoved]
    constructor
    · intro hx hmem
      rcases hmem with ⟨y, hy, hye⟩
      exact hx ((e.injective hye).symm ▸ hy)
    · intro hx hmem
      rcases hmem with ⟨y, hy, hye⟩
      apply hx
      refine ⟨a.parametrization y, ⟨y, hy, rfl⟩, ?_⟩
      simpa [hye]
  let q : a.Complement ≃ₜ b.Complement := e.subtype (hiff ·)
  refine ⟨b, ?_, q, ?_, ?_⟩
  · intro z
    rfl
  · intro x
    rfl
  · intro s
    apply Subtype.ext
    rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
