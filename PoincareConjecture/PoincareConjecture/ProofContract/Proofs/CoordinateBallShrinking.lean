import PoincareConjecture.ProofContract.Proofs.AmbientBallCompression
import PoincareConjecture.ProofContract.Proofs.CoordinateBallNeighborhood
import PoincareConjecture.ProofContract.Proofs.CoordinateBallTransport
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- A buffered coordinate ball can be ambiently compressed into any neighborhood of its center. -/
theorem coordinate_ball_shrink_into_neighborhood {M : ClosedThreeManifold.{u}}
    (b : CoordinateBall M) (U : Set M) (hU : IsOpen U) (hcenter : b.parametrization 0 ∈ U) :
    ∃ F : M ≃ₜ M,
      (∀ z : Euclidean3, ‖z‖ ≤ 1 → F (b.parametrization z) ∈ U) ∧
      (∀ x : M, x ∉ b.parametrization.target → F x = x) :=
/- SWARM_PROOF_BEGIN -/
by
  have hzero : (0 : Euclidean3) ∈ b.parametrization.source := by
    apply b.contains_two
    simp [Metric.mem_closedBall]
  have hcont : ContinuousAt b.parametrization 0 :=
    b.parametrization.continuousOn.continuousAt
      (b.parametrization.open_source.mem_nhds hzero)
  have hpre : b.parametrization ⁻¹' U ∈ 𝓝 (0 : Euclidean3) := by
    exact hcont.preimage_mem_nhds (hU.mem_nhds hcenter)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hpre
  let r : ℝ := min (ε / 2) (1 / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (div_pos hε (by norm_num)) (by norm_num)
  have hr1 : r < 1 := by
    dsimp [r]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨F, hFunit, hFfix⟩ := coordinate_ball_ambient_compression b r hr hr1
  refine ⟨F, ?_, hFfix⟩
  intro z hz
  rw [hFunit z hz]
  apply hεU
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hr.le]
  calc
    r * ‖z‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hz hr.le
    _ = r := by ring
    _ ≤ ε / 2 := min_le_left _ _
    _ < ε := by linarith
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
