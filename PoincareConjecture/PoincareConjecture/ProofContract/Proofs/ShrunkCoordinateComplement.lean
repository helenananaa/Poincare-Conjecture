import PoincareConjecture.ProofContract.Proofs.AmbientBallCompression
import PoincareConjecture.ProofContract.Proofs.CoordinateBallNeighborhood
import PoincareConjecture.ProofContract.Proofs.CoordinateBallTransport
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Buffered radial shrinking preserves the actual marked complement up to homeomorphism. -/
theorem shrunk_coordinate_complement_homeomorph {M : ClosedThreeManifold.{u}}
    (a : CoordinateBall M) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ b : CoordinateBall M,
      (∀ z : Euclidean3, b.parametrization z = a.parametrization (r • z)) ∧
      ∃ q : a.Complement ≃ₜ b.Complement, ∀ s : Sphere2, q (a.boundary s) = b.boundary s :=
/- SWARM_PROOF_BEGIN -/
by
  let h : Euclidean3 ≃ₜ Euclidean3 := Homeomorph.smulOfNeZero r hr.ne'
  let p : OpenPartialHomeomorph Euclidean3 M :=
    h.toOpenPartialHomeomorph.trans a.parametrization
  have hsource : Metric.closedBall (0 : Euclidean3) 2 ⊆ p.source := by
    rw [OpenPartialHomeomorph.trans_source]
    intro z hz
    refine ⟨by simp, ?_⟩
    change h z ∈ a.parametrization.source
    apply a.contains_two
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖r • z‖ ≤ 2
    rw [norm_smul, Real.norm_of_nonneg hr.le]
    have hz' : ‖z‖ ≤ 2 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    nlinarith
  let b : CoordinateBall M := ⟨p, hsource⟩
  refine ⟨b, ?_, ?_⟩
  · intro z
    rfl
  obtain ⟨F, hF, hFoutside⟩ := coordinate_ball_ambient_compression a r hr hr1
  have hremoved : b.removed = F '' a.removed := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨a.parametrization z, ⟨z, hz, rfl⟩, ?_⟩
      have hz' : ‖z‖ ≤ 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using (Metric.mem_ball.mp hz).le
      rw [hF z hz']
      rfl
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨z, hz, ?_⟩
      have hz' : ‖z‖ ≤ 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using (Metric.mem_ball.mp hz).le
      rw [hF z hz']
      rfl
  have hiff : ∀ x : M, x ∉ a.removed ↔ F x ∉ b.removed := by
    intro x
    rw [hremoved]
    constructor
    · intro hx hmem
      rcases hmem with ⟨y, hy, hFy⟩
      apply hx
      exact (F.injective hFy).symm ▸ hy
    · intro hx hmem
      apply hx
      exact ⟨x, hmem, rfl⟩
  let q : a.Complement ≃ₜ b.Complement := F.subtype (hiff ·)
  refine ⟨q, ?_⟩
  intro s
  apply Subtype.ext
  change F (a.parametrization (s : Euclidean3)) = b.parametrization (s : Euclidean3)
  rw [hF (s : Euclidean3) (by simpa using (show ‖(s : Euclidean3)‖ ≤ 1 by
    have := (Metric.mem_sphere.mp s.property).le
    simpa [dist_zero_right] using this))]
  rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
