import Mathlib
import PoincareConjecture.ParallelMath.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Quantitative
open Set Function Filter
open scoped BigOperators Topology Manifold ContDiff

/-- **Math.** Finite monotone partition sums are bounded by the actual finite total variation. -/
theorem dist_partition_sum_le_variation {X : Type*} [PseudoMetricSpace X]
    (f : unitInterval → X) (hfinite : eVariationOn f univ ≠ ⊤)
    (n : ℕ) (t : Fin (n+1) → unitInterval) (ht : Monotone t) :
    (∑ i : Fin n, dist (f (t i.castSucc)) (f (t i.succ))) ≤
      (eVariationOn f univ).toReal :=
/- SWARM_PROOF_BEGIN -/
by
  -- Clamp the Fin-partition to a ℕ-indexed monotone path; `n = 0` is the empty sum.
  let u : ℕ → unitInterval := fun k =>
    t ⟨k ⊓ n, (Nat.min_le_right k n).trans_lt n.lt_succ_self⟩
  have hu : Monotone u := fun i j hij =>
    ht (Fin.mk_le_mk.mpr (min_le_min hij le_rfl))
  have hsum :
      ∑ i ∈ Finset.range n, dist (f (u i)) (f (u (i + 1))) =
        ∑ i : Fin n, dist (f (t i.castSucc)) (f (t i.succ)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (i : ℕ) ≤ n := Nat.le_of_lt i.isLt
    have hi1 : (i : ℕ) + 1 ≤ n := Nat.succ_le_of_lt i.isLt
    simp only [u, min_eq_left hi, min_eq_left hi1]
    rfl
  have hle :
      (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤ eVariationOn f univ :=
    eVariationOn.sum_le hu fun _ => mem_univ _
  have hsum_edist :
      ∑ i ∈ Finset.range n, dist (f (u i)) (f (u (i + 1))) =
        (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))).toReal := by
    rw [ENNReal.toReal_sum fun _ _ => edist_ne_top _ _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dist_comm, dist_edist]
  rw [← hsum, hsum_edist]
  exact ENNReal.toReal_mono hfinite hle
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative
