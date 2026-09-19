import PoincareConjecture.ParallelMath.SurgeryMetric.ChainTriangle
import PoincareConjecture.ParallelMath.SurgeryMetric.GluedMap
import PoincareConjecture.ParallelMath.SurgeryMetric.EpsilonRemoval
import PoincareConjecture.ParallelMath.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath
open Set Function Filter
open scoped BigOperators Topology

/-- Gluing local maps is globally Lipschitz when finite piece-chains approximate ambient distance. -/
theorem lipschitz_gluing_of_approximate_piece_chains
    {ι X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (S : ι → Set X) (hcover : ∀ x : X, ∃ i, x ∈ S i)
    (f : ι → X → Y) (cost : ι → X → X → ℝ) (L : NNReal)
    (hcompat : ∀ i j x, x ∈ S i → x ∈ S j → f i x = f j x)
    (hlocal : ∀ i x y, x ∈ S i → y ∈ S i →
      dist (f i x) (f i y) ≤ (L : ℝ)*cost i x y)
    (hchains : ∀ x y : X, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ n : ℕ, ∃ z : Fin (n+1) → X, ∃ piece : Fin n → ι,
        z 0 = x ∧ z (Fin.last n) = y ∧
        (∀ i, z i.castSucc ∈ S (piece i) ∧ z i.succ ∈ S (piece i)) ∧
        (∑ i : Fin n, cost (piece i) (z i.castSucc) (z i.succ)) ≤ dist x y + epsilon) :
    ∃ F : X → Y, (∀ i x, x ∈ S i → F x = f i x) ∧ LipschitzWith L F :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨F, hF⟩ := exists_map_of_compatible_cover S hcover f hcompat
  refine ⟨F, hF, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  refine le_mul_of_forall_length_error (dist (F x) (F y)) (dist x y) (L : ℝ)
      (NNReal.coe_nonneg L) ?_
  intro epsilon hε
  obtain ⟨n, z, piece, hz0, hzn, hmem, hcost⟩ := hchains x y epsilon hε
  have hstep : ∀ i : Fin n,
      dist (F (z i.castSucc)) (F (z i.succ)) ≤
        (L : ℝ) * cost (piece i) (z i.castSucc) (z i.succ) := by
    intro i
    rcases hmem i with ⟨hzi, hzis⟩
    calc
      dist (F (z i.castSucc)) (F (z i.succ))
          = dist (f (piece i) (z i.castSucc)) (f (piece i) (z i.succ)) := by
            rw [hF (piece i) (z i.castSucc) hzi, hF (piece i) (z i.succ) hzis]
      _ ≤ (L : ℝ) * cost (piece i) (z i.castSucc) (z i.succ) :=
            hlocal (piece i) _ _ hzi hzis
  calc
    dist (F x) (F y) = dist (F (z 0)) (F (z (Fin.last n))) := by rw [hz0, hzn]
    _ ≤ ∑ i : Fin n, dist (F (z i.castSucc)) (F (z i.succ)) :=
          finite_chain_dist_le n (fun i => F (z i))
    _ ≤ ∑ i : Fin n, (L : ℝ) * cost (piece i) (z i.castSucc) (z i.succ) :=
          Finset.sum_le_sum fun i _ => hstep i
    _ = (L : ℝ) * ∑ i : Fin n, cost (piece i) (z i.castSucc) (z i.succ) :=
          (Finset.mul_sum _ _ _).symm
    _ ≤ (L : ℝ) * (dist x y + epsilon) :=
          mul_le_mul_of_nonneg_left hcost (NNReal.coe_nonneg L)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath
