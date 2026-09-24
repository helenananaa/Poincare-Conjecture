import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ForcingGraphHolderEstimate
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
/-- Recover the actual Holder inequality directly from the normalized increment graph. -/
theorem forcing_graph_holder_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T alpha : ℝ) (ha : 0 < alpha) (F : ForcingJet V T)
    (hF : F ∈ forcingGraph V T alpha) :
    ∀ p q : Slab T, ‖F.1 p-F.1 q‖ ≤ ‖F.2‖ * parabolicRho p q ^ alpha :=
/- SWARM_PROOF_BEGIN -/
by
  intro p q
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
    have hrel := hF pq
    have hdiff : F.1 p - F.1 q =
        parabolicRho p q ^ alpha • F.2 pq := by
      calc
        F.1 p - F.1 q = parabolicRho p q ^ alpha •
            ((parabolicRho p q ^ alpha)⁻¹ • (F.1 p-F.1 q)) := by
              rw [smul_smul, mul_inv_cancel₀ haRho.ne', one_smul]
        _ = parabolicRho p q ^ alpha • F.2 pq := by
              rw [← hrel]
    calc
      ‖F.1 p-F.1 q‖ = parabolicRho p q ^ alpha * ‖F.2 pq‖ := by
        rw [hdiff, norm_smul, Real.norm_of_nonneg haRho.le]
      _ ≤ parabolicRho p q ^ alpha * ‖F.2‖ :=
        mul_le_mul_of_nonneg_left (F.2.norm_coe_le_norm pq) haRho.le
      _ = ‖F.2‖ * parabolicRho p q ^ alpha := by ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ForcingGraphHolderEstimate
