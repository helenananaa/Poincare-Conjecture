import Mathlib
import PoincareConjecture.ParallelMath.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Quantitative
open Set Function Filter
open scoped BigOperators Topology Manifold ContDiff

/-- **Math.** An open cover gives a finite path subdivision with each whole subpath in one piece. -/
theorem path_subdivision_of_open_cover {ι X : Type*} [TopologicalSpace X]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    {x y : X} (γ : Path x y) :
    ∃ n : ℕ, ∃ t : Fin (n+1) → unitInterval, ∃ piece : Fin n → ι,
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
      ∀ i, MapsTo γ (Icc (t i.castSucc) (t i.succ)) (U (piece i)) :=
/- SWARM_PROOF_BEGIN -/
by
  -- Pull the open cover back along the path.
  let c : ι → Set unitInterval := fun i ↦ γ ⁻¹' U i
  have hc_open : ∀ i, IsOpen (c i) := fun i ↦ (hU i).preimage γ.continuous
  have hc_cover : (univ : Set unitInterval) ⊆ ⋃ i, c i := fun t _ ↦
    mem_iUnion.mpr (hcover (γ t))
  obtain ⟨tNat, ht0, htmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc_open hc_cover
  -- Restrict the eventually-1 sequence to `Fin (n+1)`.
  let t : Fin (n + 1) → unitInterval := fun i ↦ tNat i
  -- Choose a cover index for each closed subinterval of the partition.
  choose piece hpiece using fun i : Fin n ↦ hsub i
  refine ⟨n, t, piece, ht0, ?_, ?_, ?_⟩
  · -- The last node is the right endpoint `1`.
    simpa [t, Fin.val_last] using hn n le_rfl
  · -- Restriction of a monotone sequence is monotone.
    intro i j hij
    exact htmono (mod_cast hij)
  · -- Whole closed subpath, not just the endpoints, lands in one piece.
    intro i s hs
    have hs' : s ∈ Icc (tNat i) (tNat (i + 1)) := by
      simpa [t, Fin.val_castSucc, Fin.val_succ] using hs
    exact hpiece i hs'
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative
