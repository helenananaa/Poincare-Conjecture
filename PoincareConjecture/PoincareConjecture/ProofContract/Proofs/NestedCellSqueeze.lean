import PoincareConjecture.ProofContract.Proofs.NestedCompactNeighborhood
import PoincareConjecture.ProofContract.Proofs.CompactChartSqueeze
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
import PoincareConjecture.ProofContract.Proofs.ChartSupportedHomeomorph
import PoincareConjecture.ProofContract.Proofs.EuclideanBallCompression
import PoincareConjecture.ProofContract.Proofs.BufferedRadiusProfile
import PoincareConjecture.ProofContract.Proofs.RadialHomeomorphLift
set_option autoImplicit false
noncomputable section
universe u v
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Filter Topology
open scoped Topology
theorem nested_coordinate_cells_squeezable (M : ClosedThreeManifold.{u})
    (b : ℕ → CoordinateBall M)
    (hn : ∀ n, (b (n+1)).parametrization '' Metric.closedBall (0:Euclidean3) 1 ⊆ (b n).removed)
    (U : Set M) (hU : IsOpen U)
    (hKU : (⋂ n, (b n).parametrization '' Metric.closedBall (0:Euclidean3) 1) ⊆ U) :
    ∃ z ∈ U, ∀ V : Set M, IsOpen V → z ∈ V →
      ∃ H : M ≃ₜ M,
        H '' (⋂ n, (b n).parametrization '' Metric.closedBall (0:Euclidean3) 1) ⊆ V ∧
        ∀ x : M, x ∉ U → H x = x :=
/- SWARM_PROOF_BEGIN -/
by
  let K : ℕ → Set M := fun n =>
    (b n).parametrization '' Metric.closedBall (0 : Euclidean3) 1
  have hKcompact : ∀ n, IsCompact (K n) := by
    intro n
    dsimp [K]
    apply (isCompact_closedBall (0 : Euclidean3) 1).image_of_continuousOn
    apply (b n).parametrization.continuousOn.mono
    intro z hz
    apply (b n).contains_two
    have hz' : ‖z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall] using hz
    simpa [Metric.mem_closedBall] using (show ‖z‖ ≤ 2 by linarith)
  have hKanti : Antitone K := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp [K]
    exact (hn n).trans (image_mono Metric.ball_subset_closedBall)
  have hKU' : (⋂ n, K n) ⊆ U := by
    simpa [K] using hKU
  obtain ⟨n, hnU⟩ :=
    nested_compact_eventually_in_neighborhood K hKcompact hKanti U hU hKU'
  let z : M := (b n).parametrization 0
  have hzK : z ∈ K n := by
    refine ⟨0, ?_, rfl⟩
    simp [Metric.mem_closedBall]
  have hzU : z ∈ U := hnU hzK
  refine ⟨z, hzU, ?_⟩
  intro V hV hzV
  have hnext_removed : K (n + 1) ⊆ (b n).removed := by
    simpa [K] using hn n
  obtain ⟨H, hHV, hfix⟩ :=
    compact_subset_coordinate_squeeze (b n) (K (n + 1)) (hKcompact (n + 1))
      hnext_removed V hV hzV
  refine ⟨H, ?_, ?_⟩
  · exact (image_mono (iInter_subset K (n + 1))).trans hHV
  · intro x hxU
    apply hfix x
    intro hxremoved
    apply hxU
    apply hnU
    exact (image_mono Metric.ball_subset_closedBall) hxremoved
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
