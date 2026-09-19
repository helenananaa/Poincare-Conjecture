import PoincareConjecture.ParallelMath.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath
open Set Function Filter
open scoped BigOperators Topology

/-- Telescoping bound for a finite metric chain, including a zero-edge chain. -/
theorem finite_chain_dist_le {Y : Type*} [PseudoMetricSpace Y]
    (n : ℕ) (z : Fin (n+1) → Y) :
    dist (z 0) (z (Fin.last n)) ≤
      ∑ i : Fin n, dist (z i.castSucc) (z i.succ) :=
/- SWARM_PROOF_BEGIN -/
by
  -- Polygon inequality on a ℕ-indexed extension of the Fin-chain; `n = 0` is empty.
  let f : ℕ → Y := fun k =>
    z ⟨k ⊓ n, (Nat.min_le_right k n).trans_lt n.lt_succ_self⟩
  have hf0 : f 0 = z 0 := by
    simp [f]
  have hfn : f n = z (Fin.last n) := by
    simp [f, Fin.last]
  have hsum :
      ∑ i ∈ Finset.range n, dist (f i) (f (i + 1)) =
        ∑ i : Fin n, dist (z i.castSucc) (z i.succ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (i : ℕ) ≤ n := Nat.le_of_lt i.isLt
    have hi1 : (i : ℕ) + 1 ≤ n := Nat.succ_le_of_lt i.isLt
    simp only [f, min_eq_left hi, min_eq_left hi1]
    rfl
  calc
    dist (z 0) (z (Fin.last n)) = dist (f 0) (f n) := by rw [hf0, hfn]
    _ ≤ ∑ i ∈ Finset.range n, dist (f i) (f (i + 1)) := dist_le_range_sum_dist f n
    _ = ∑ i : Fin n, dist (z i.castSucc) (z i.succ) := hsum
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath
