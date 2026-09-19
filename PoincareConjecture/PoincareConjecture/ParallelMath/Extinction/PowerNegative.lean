import PoincareConjecture.ParallelMath.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath
open Set Function Filter
open scoped BigOperators Topology

/-- A positive forcing term makes the sublinear-growth comparison barrier eventually negative. -/
theorem powerBarrier_eventually_negative (alpha c a k : ℝ)
    (hc : 0 < c) (hk : 0 < k) (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → powerBarrier alpha c a k t < 0 :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  by_cases hbad : alpha ≤ 0
  · exact ((not_le_of_gt halpha0) hbad).elim
  ·
    have h1α : 0 < 1 - alpha := sub_pos.mpr halpha1
    have hB : 0 < k / (1 - alpha) := div_pos hk h1α
    have htend : Tendsto (fun t : ℝ => (t + c) ^ (1 - alpha)) atTop atTop :=
      (tendsto_rpow_atTop h1α).comp (tendsto_atTop_add_const_right atTop c tendsto_id)
    set A : ℝ := a / c ^ alpha
    set B : ℝ := k / (1 - alpha)
    set C : ℝ := c ^ (1 - alpha)
    obtain ⟨T0, hT0⟩ := (htend.eventually_gt_atTop (A / B + C)).exists_forall_of_atTop
    refine ⟨max (0 : ℝ) T0, le_max_left _ _, fun t ht => ?_⟩
    have ht0 : 0 ≤ t := (le_max_left (0 : ℝ) T0).trans ht
    have htT : T0 ≤ t := (le_max_right (0 : ℝ) T0).trans ht
    have htc : 0 < t + c := add_pos_of_nonneg_of_pos ht0 hc
    have hpre : 0 < (t + c) ^ alpha := Real.rpow_pos_of_pos htc _
    have hbr : A - B * ((t + c) ^ (1 - alpha) - C) < 0 := by
      refine sub_lt_zero.mpr ?_
      have hdiv : A / B < (t + c) ^ (1 - alpha) - C :=
        (lt_sub_iff_add_lt).mpr (hT0 t htT)
      have hmul : A < ((t + c) ^ (1 - alpha) - C) * B := (div_lt_iff₀ hB).mp hdiv
      rwa [mul_comm] at hmul
    simpa [powerBarrier, A, B, C] using mul_neg_of_pos_of_neg hpre hbr
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath
