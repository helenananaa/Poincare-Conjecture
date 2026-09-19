import Mathlib
import PoincareConjecture.ParallelMath.Core
import ReferenceBridges.Quantitative.ShortPath
import PoincareConjecture.ParallelMath.Quantitative.PathSubdivision
import PoincareConjecture.ParallelMath.Quantitative.VariationPartition
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PoincareConjecture.ParallelMath.Quantitative.Reference
open Set Function Filter
open scoped BigOperators Topology Manifold ContDiff

/-- **Math.** In the original length metric, open-cover piece chains approximate distance. -/
theorem lengthSpace_open_cover_piece_chains {ι X : Type*} [PseudoMetricSpace X]
    [Shared.LengthSpace X] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (x y : X) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ n : ℕ, ∃ z : Fin (n+1) → X, ∃ piece : Fin n → ι,
      z 0 = x ∧ z (Fin.last n) = y ∧
      (∀ i, z i.castSucc ∈ U (piece i) ∧ z i.succ ∈ U (piece i)) ∧
      (∑ i : Fin n, dist (z i.castSucc) (z i.succ)) ≤ dist x y + epsilon :=
/- SWARM_PROOF_BEGIN -/
by
  -- A genuine length metric supplies a finite path strictly shorter than
  -- `dist x y + epsilon`.
  obtain ⟨γ, hγfin, hγlt⟩ := exists_short_path_of_lengthSpace x y epsilon he
  -- Subdivide so each whole closed subpath lands in one set of the cover.
  obtain ⟨n, t, piece, ht0, ht1, htmono, hmaps⟩ :=
    path_subdivision_of_open_cover U hU hcover γ
  -- Sample the path at the partition nodes.
  refine ⟨n, fun i => γ (t i), piece, ?_, ?_, ?_, ?_⟩
  · -- Left endpoint of the path.
    dsimp; rw [ht0]; exact γ.source
  · -- Right endpoint of the path.
    dsimp; rw [ht1]; exact γ.target
  · -- Endpoints of each closed subpath lie in the chosen cover set.
    intro i
    have hle : t i.castSucc ≤ t i.succ := htmono i.castSucc_le_succ
    exact ⟨hmaps i (left_mem_Icc.2 hle), hmaps i (right_mem_Icc.2 hle)⟩
  · -- Partition distances are bounded by total variation of the short path.
    have hsum :=
      dist_partition_sum_le_variation (γ : unitInterval → X) hγfin n t htmono
    exact hsum.trans (le_of_lt hγlt)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative.Reference
