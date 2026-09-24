import PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BoundedContinuousFunction
abbrev ForcingJet (V : Type*) [NormedAddCommGroup V] (T : ℝ) :=
  (Slab T →ᵇ V) × (Pair T →ᵇ V)
def forcingGraph (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T alpha : ℝ) : Set (ForcingJet V T) :=
  {z | ∀ p : Pair T, z.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
    (z.1 p.1.1-z.1 p.1.2)}
/-- The genuine forcing Holder graph is a complete linear input space. -/
theorem parabolic_forcing_submodule_complete
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (T alpha : ℝ) (ha : 0 < alpha) :
    ∃ S : Submodule ℝ (ForcingJet V T),
      (S : Set (ForcingJet V T)) = forcingGraph V T alpha ∧ CompleteSpace S ∧
      ∀ z ∈ forcingGraph V T alpha, ∀ p q : Slab T,
        ‖z.1 p-z.1 q‖ ≤ ‖z.2‖*parabolicRho p q ^ alpha :=
/- SWARM_PROOF_BEGIN -/
by
  let S : Submodule ℝ (ForcingJet V T) := {
    carrier := forcingGraph V T alpha
    zero_mem' := by
      intro p
      simp
    add_mem' := by
      intro z w hz hw p
      change z.2 p + w.2 p =
        (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          ((z.1 p.1.1 + w.1 p.1.1) - (z.1 p.1.2 + w.1 p.1.2))
      rw [hz p, hw p]
      simp [sub_eq_add_neg, smul_add]
      abel
    smul_mem' := by
      intro c z hz p
      change c • z.2 p =
        (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          ((c • z.1) p.1.1 - (c • z.1) p.1.2)
      rw [hz p]
      simp [smul_sub, smul_smul, mul_comm]
  }
  have firstEval (p : Slab T) :
      Continuous (fun z : ForcingJet V T => z.1 p) := by
    exact (ContinuousEvalConst.continuous_eval_const p).comp continuous_fst
  have secondEval (p : Pair T) :
      Continuous (fun z : ForcingJet V T => z.2 p) := by
    exact (ContinuousEvalConst.continuous_eval_const p).comp continuous_snd
  have graphPointClosed (p : Pair T) : IsClosed {z : ForcingJet V T |
      z.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (z.1 p.1.1-z.1 p.1.2)} := by
    apply isClosed_eq
    · exact secondEval p
    · exact ((firstEval p.1.1).sub (firstEval p.1.2)).const_smul
        ((parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹)
  have graphClosed : IsClosed (forcingGraph V T alpha) := by
    have heq : forcingGraph V T alpha =
        ⋂ p : Pair T, {z : ForcingJet V T |
          z.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
            (z.1 p.1.1-z.1 p.1.2)} := by
      ext z
      simp [forcingGraph]
    rw [heq]
    exact isClosed_iInter graphPointClosed
  haveI : CompleteSpace (ForcingJet V T) := by
    dsimp [ForcingJet]
    infer_instance
  have hcomplete : IsComplete (S : Set (ForcingJet V T)) := by
    exact graphClosed.isComplete
  refine ⟨S, rfl, hcomplete.completeSpace_coe, ?_⟩
  intro z hz p q
  by_cases hpq : p = q
  · subst q
    simp [parabolicRho, ha.ne']
  · let pq : Pair T := ⟨(p, q), hpq⟩
    have htimeOrSpace : (p.1 : ℝ) ≠ (q.1 : ℝ) ∨ p.2 ≠ q.2 := by
      by_contra h
      push Not at h
      apply hpq
      apply Prod.ext
      · exact Subtype.ext h.1
      · exact h.2
    have hrho : 0 < parabolicRho p q := by
      unfold parabolicRho
      rcases htimeOrSpace with ht | hx
      · exact add_pos_of_nonneg_of_pos (norm_nonneg _) <| Real.sqrt_pos.2 <|
          abs_pos.mpr (sub_ne_zero.mpr ht)
      · exact add_pos_of_pos_of_nonneg
          (norm_pos_iff.mpr (sub_ne_zero.mpr hx)) (Real.sqrt_nonneg _)
    have haRho : 0 < parabolicRho p q ^ alpha :=
      Real.rpow_pos_of_pos hrho alpha
    have hrel := hz pq
    have hdiff : z.1 p - z.1 q =
        parabolicRho p q ^ alpha • z.2 pq := by
      calc
        z.1 p - z.1 q = parabolicRho p q ^ alpha •
            ((parabolicRho p q ^ alpha)⁻¹ • (z.1 p-z.1 q)) := by
              rw [smul_smul, mul_inv_cancel₀ haRho.ne', one_smul]
        _ = parabolicRho p q ^ alpha • z.2 pq := by
              rw [← hrel]
    calc
      ‖z.1 p-z.1 q‖ = parabolicRho p q ^ alpha * ‖z.2 pq‖ := by
        rw [hdiff, norm_smul, Real.norm_of_nonneg haRho.le]
      _ ≤ parabolicRho p q ^ alpha * ‖z.2‖ :=
        mul_le_mul_of_nonneg_left (z.2.norm_coe_le_norm pq) haRho.le
      _ = ‖z.2‖ * parabolicRho p q ^ alpha := by ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
