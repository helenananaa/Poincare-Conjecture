import PoincareConjecture.ParallelImplementation.ForcingGraphBilinearProduct
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.MixedProjectedForcingBilinear
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
 theorem exists_mixed_projected_forcing_bilinear
    {Y V W Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T alpha : ℝ) (B : V →L[ℝ] W →L[ℝ] Z)
    (X : Submodule ℝ (ForcingJet Z T))
    (hX : (X : Set (ForcingJet Z T)) = forcingGraph Z T alpha)
    (P : Y →L[ℝ] ForcingJet V T) (Q : Y →L[ℝ] ForcingJet W T)
    (hP : ∀ z, P z ∈ forcingGraph V T alpha)
    (hQ : ∀ z, Q z ∈ forcingGraph W T alpha) :
    ∃ N : Y → X, N 0 = 0 ∧
      (∀ z p, (N z).1.1 p = B ((P z).1 p) ((Q z).1 p)) ∧
      (∀ z w, ‖N z-N w‖ ≤
        (2*‖B‖*‖P‖*‖Q‖)*(‖z‖+‖w‖)*‖z-w‖) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let M (a : ForcingJet V T) (ha : a ∈ forcingGraph V T alpha) :
      ForcingJet W T →L[ℝ] ForcingJet Z T :=
    Classical.choose
      (PoincareConjecture.ParallelImplementation.ForcingGraphBilinearProduct.exists_forcing_bilinear_product
        B T alpha a ha)
  have hM (a : ForcingJet V T) (ha : a ∈ forcingGraph V T alpha) :=
    Classical.choose_spec
      (PoincareConjecture.ParallelImplementation.ForcingGraphBilinearProduct.exists_forcing_bilinear_product
        B T alpha a ha)
  let N : Y → X := fun z =>
    ⟨M (P z) (hP z) (Q z), by
      have hmem : M (P z) (hP z) (Q z) ∈ forcingGraph Z T alpha :=
        (hM (P z) (hP z)).2.2.2 (Q z) (hQ z)
      rw [← hX] at hmem
      exact hmem⟩
  refine ⟨N, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change M (P 0) (hP 0) (Q 0) = 0
    rw [Q.map_zero]
    exact (M (P 0) (hP 0)).map_zero
  · intro z p
    change (M (P z) (hP z) (Q z)).1 p = B ((P z).1 p) ((Q z).1 p)
    exact (hM (P z) (hP z)).2.1 (Q z) p
  · intro z w
    have hdP : P z - P w ∈ forcingGraph V T alpha := by
      rw [← P.map_sub]
      exact hP (z - w)
    have hPsub1 (p : Slab T) : (P z - P w).1 p = (P z).1 p - (P w).1 p := by
      change ((P z).1 - (P w).1) p = (P z).1 p - (P w).1 p
      rw [BoundedContinuousFunction.sub_apply]
    have hPsub2
        (p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T) :
        (P z - P w).2 p = (P z).2 p - (P w).2 p := by
      change ((P z).2 - (P w).2) p = (P z).2 p - (P w).2 p
      rw [BoundedContinuousFunction.sub_apply]
    have hQsub1 (p : Slab T) : (Q z - Q w).1 p = (Q z).1 p - (Q w).1 p := by
      change ((Q z).1 - (Q w).1) p = (Q z).1 p - (Q w).1 p
      rw [BoundedContinuousFunction.sub_apply]
    have hQsub2
        (p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T) :
        (Q z - Q w).2 p = (Q z).2 p - (Q w).2 p := by
      change ((Q z).2 - (Q w).2) p = (Q z).2 p - (Q w).2 p
      rw [BoundedContinuousFunction.sub_apply]
    have hidentity :
        M (P z) (hP z) (Q z) - M (P w) (hP w) (Q w) =
          M (P z) (hP z) (Q z - Q w) + M (P z - P w) hdP (Q w) := by
      apply Prod.ext
      · apply BoundedContinuousFunction.ext
        intro p
        change (M (P z) (hP z) (Q z)).1 p -
            (M (P w) (hP w) (Q w)).1 p =
          (M (P z) (hP z) (Q z - Q w)).1 p +
            (M (P z - P w) hdP (Q w)).1 p
        dsimp only [M]
        rw [(hM (P z) (hP z)).2.1 (Q z) p,
          (hM (P w) (hP w)).2.1 (Q w) p,
          (hM (P z) (hP z)).2.1 (Q z - Q w) p,
          (hM (P z - P w) hdP).2.1 (Q w) p, hQsub1 p]
        calc
          B ((P z).1 p) ((Q z).1 p) - B ((P w).1 p) ((Q w).1 p) =
              (B ((P z).1 p) ((Q z).1 p) - B ((P z).1 p) ((Q w).1 p)) +
                (B ((P z).1 p) ((Q w).1 p) - B ((P w).1 p) ((Q w).1 p)) := by abel
          _ = B ((P z).1 p) ((Q z).1 p - (Q w).1 p) +
              B ((P z).1 p - (P w).1 p) ((Q w).1 p) := by
                rw [← map_sub, ← B.map_sub₂]
      · apply BoundedContinuousFunction.ext
        intro p
        change (M (P z) (hP z) (Q z)).2 p -
            (M (P w) (hP w) (Q w)).2 p =
          (M (P z) (hP z) (Q z - Q w)).2 p +
            (M (P z - P w) hdP (Q w)).2 p
        dsimp only [M]
        rw [(hM (P z) (hP z)).2.2.1 (Q z) p,
          (hM (P w) (hP w)).2.2.1 (Q w) p,
          (hM (P z) (hP z)).2.2.1 (Q z - Q w) p,
          (hM (P z - P w) hdP).2.2.1 (Q w) p,
          hQsub2 p, hQsub1 p.1.2,
          hPsub1 p.1.1, hPsub2 p]
        simp only [map_sub, sub_apply]
        abel
    calc
      ‖N z - N w‖ =
          ‖M (P z) (hP z) (Q z - Q w) + M (P z - P w) hdP (Q w)‖ := by
            change ‖M (P z) (hP z) (Q z) - M (P w) (hP w) (Q w)‖ = _
            rw [hidentity]
      _ ≤ ‖M (P z) (hP z) (Q z - Q w)‖ +
            ‖M (P z - P w) hdP (Q w)‖ := norm_add_le _ _
      _ ≤ ‖M (P z) (hP z)‖ * ‖Q z - Q w‖ +
            ‖M (P z - P w) hdP‖ * ‖Q w‖ :=
          add_le_add ((M (P z) (hP z)).le_opNorm (Q z - Q w))
            ((M (P z - P w) hdP).le_opNorm (Q w))
      _ ≤ (2 * ‖B‖ * ‖P z‖) * ‖Q z - Q w‖ +
            (2 * ‖B‖ * ‖P z - P w‖) * ‖Q w‖ := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (hM (P z) (hP z)).1 (norm_nonneg _)
          · exact mul_le_mul_of_nonneg_right (hM (P z - P w) hdP).1 (norm_nonneg _)
      _ ≤ (2 * ‖B‖ * (‖P‖ * ‖z‖)) * (‖Q‖ * ‖z - w‖) +
            (2 * ‖B‖ * (‖P‖ * ‖z - w‖)) * (‖Q‖ * ‖w‖) := by
          apply add_le_add
          · gcongr
            · exact P.le_opNorm z
            · rw [← Q.map_sub]
              exact Q.le_opNorm (z - w)
          · gcongr
            · rw [← P.map_sub]
              exact P.le_opNorm (z - w)
            · exact Q.le_opNorm w
      _ = (2 * ‖B‖ * ‖P‖ * ‖Q‖) * (‖z‖ + ‖w‖) * ‖z - w‖ := by ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.MixedProjectedForcingBilinear
