import PoincareConjecture.ProofContract.Proofs.SqueezableCompactCollapse
import PoincareConjecture.ProofContract.Proofs.NestedCellSqueeze
import PoincareConjecture.ProofContract.Proofs.CollapseComplementHomeomorph
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
import Mathlib.Geometry.Manifold.Instances.Sphere
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Filter Topology
open scoped Topology Manifold ContDiff
/-- Produce an actual collapse for nested buffered cells in the original topological manifold. -/
theorem nested_cells_actual_collapse (M : ClosedThreeManifold.{u}) (b : ℕ → CoordinateBall M)
    (hn : ∀ n, (b (n+1)).parametrization '' Metric.closedBall (0:Euclidean3) 1 ⊆ (b n).removed) :
    let K : Set M := ⋂ n, (b n).parametrization '' Metric.closedBall (0:Euclidean3) 1
    K.Nonempty ∧ ∃ q : M → M, Continuous q ∧ Surjective q ∧
      ∀ x y : M, q x = q y ↔ x=y ∨ (x∈K ∧ y∈K) :=
/- SWARM_PROOF_BEGIN -/
by
  let C : ℕ → Set M := fun n =>
    (b n).parametrization '' Metric.closedBall (0 : Euclidean3) 1
  let K : Set M := ⋂ n, C n
  change K.Nonempty ∧ ∃ q : M → M, Continuous q ∧ Surjective q ∧
    ∀ x y : M, q x = q y ↔ x = y ∨ (x ∈ K ∧ y ∈ K)
  letI : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace (𝓘(ℝ, Euclidean3)) M
  letI : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  have hCcompact : ∀ n, IsCompact (C n) := by
    intro n
    dsimp [C]
    apply (isCompact_closedBall (0 : Euclidean3) 1).image_of_continuousOn
    apply (b n).parametrization.continuousOn.mono
    intro z hz
    apply (b n).contains_two
    have hz' : ‖z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall] using hz
    simpa [Metric.mem_closedBall] using (show ‖z‖ ≤ 2 by linarith)
  have hCnonempty : ∀ n, (C n).Nonempty := by
    intro n
    refine ⟨(b n).parametrization 0, ⟨0, ?_, rfl⟩⟩
    simp [Metric.mem_closedBall]
  have hCstep : ∀ n, C (n + 1) ⊆ C n := by
    intro n
    dsimp [C]
    exact (hn n).trans (image_mono Metric.ball_subset_closedBall)
  have hCanti : Antitone C := antitone_nat_of_succ_le hCstep
  have hCclosed : ∀ n, IsClosed (C n) := fun n => (hCcompact n).isClosed
  have hKnonempty : K.Nonempty := by
    dsimp [K]
    exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
      hCstep hCnonempty (hCcompact 0) hCclosed
  have hKclosed : IsClosed K := by
    dsimp [K]
    exact isClosed_iInter hCclosed
  have hKcompact : IsCompact K := by
    exact isCompact_univ.of_isClosed_subset hKclosed (subset_univ K)
  have hshrink : ∀ U : Set M, IsOpen U → K ⊆ U → ∀ eps : ℝ, 0 < eps →
      ∃ h : M ≃ₜ M, (∀ x, x ∉ U → h x = x) ∧
        ∀ x ∈ K, ∀ y ∈ K, dist (h x) (h y) < eps := by
    intro U hU hKU eps heps
    obtain ⟨z, hzU, hzcompress⟩ :=
      nested_coordinate_cells_squeezable M b hn U hU (by
        simpa [K, C] using hKU)
    have hhalf : 0 < eps / 2 := by linarith
    obtain ⟨H, hH, hfix⟩ := hzcompress (Metric.ball z (eps / 2))
      Metric.isOpen_ball (Metric.mem_ball_self hhalf)
    refine ⟨H, hfix, ?_⟩
    intro x hx y hy
    have hxball : H x ∈ Metric.ball z (eps / 2) := hH ⟨x, hx, rfl⟩
    have hyball : H y ∈ Metric.ball z (eps / 2) := hH ⟨y, hy, rfl⟩
    have hxlt : dist (H x) z < eps / 2 := Metric.mem_ball.mp hxball
    have hylt : dist z (H y) < eps / 2 := by
      simpa [dist_comm] using (Metric.mem_ball.mp hyball)
    calc
      dist (H x) (H y) ≤ dist (H x) z + dist z (H y) := dist_triangle _ _ _
      _ < eps / 2 + eps / 2 := add_lt_add hxlt hylt
      _ = eps := by ring
  obtain ⟨q, hq, hqsurj, hqfib⟩ :=
    squeezable_compact_single_fiber_map K hKcompact hKnonempty hshrink
  exact ⟨hKnonempty, q, hq, hqsurj, hqfib⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
