import PoincareConjecture.ProofContract.Proofs.EuclideanBallCompression
import PoincareConjecture.ProofContract.Proofs.ChartSupportedHomeomorph
import PoincareConjecture.ProofContract.V1.Obligations
import PoincareConjecture.ProofContract.Proofs.CoordinateBallExists
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Actual ambient compression inside an arbitrary buffered coordinate ball. -/
theorem coordinate_ball_ambient_compression {M : ClosedThreeManifold.{u}}
    (b : CoordinateBall M) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ F : M ≃ₜ M,
      (∀ z : Euclidean3, ‖z‖ ≤ 1 → F (b.parametrization z) = b.parametrization (r • z)) ∧
      (∀ x : M, x ∉ b.parametrization.target → F x = x) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨H, hHunit, hHfix⟩ := euclidean_buffered_ball_compression r hr hr1
  obtain ⟨F, hF, hFoutside⟩ := chart_supported_homeomorph b H hHfix
  refine ⟨F, ?_, hFoutside⟩
  intro z hz
  have hzsource : z ∈ b.parametrization.source := by
    apply b.contains_two
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith
  rw [hF z hzsource, hHunit z hz]
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
