import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmoothUnitBallCutoff
open scoped Topology BigOperators ContDiff BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance stdGroup0 : NormedAddCommGroup (E3 →L[ℝ] E6) := inferInstance
local instance stdSpace0 : NormedSpace ℝ (E3 →L[ℝ] E6) := inferInstance
local instance stdGroup1 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance stdSpace1 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance stdGroup2 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance stdSpace2 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
theorem exists_smooth_unit_ball_cutoff :

    ∃ χ : E3 → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x : E3, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x : E3, ‖x‖ ≤ 1 → χ x=1) ∧ (∀ x : E3, 2 ≤ ‖x‖ → χ x=0) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ (k : ℕ), k ≤ 3 → ∀ x : E3, ‖iteratedFDeriv ℝ k χ x‖ ≤ K :=
/- SWARM_PROOF_BEGIN -/
by
  let b : ContDiffBump (0 : E3) := ⟨1, 2, by norm_num, by norm_num⟩
  let χ : E3 → ℝ := b
  have hb_smooth : ContDiff ℝ ∞ χ := by
    simpa [χ] using b.contDiff
  have hb_compact : HasCompactSupport χ := by
    simpa [χ] using b.hasCompactSupport
  have hb_range : ∀ x : E3, 0 ≤ χ x ∧ χ x ≤ 1 := by
    intro x
    exact ⟨by simpa [χ] using b.nonneg (x := x),
      by simpa [χ] using b.le_one (x := x)⟩
  have hb_inner : ∀ x : E3, ‖x‖ ≤ 1 → χ x = 1 := by
    intro x hx
    exact b.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, dist_eq_norm] using hx)
  have hb_outer : ∀ x : E3, 2 ≤ ‖x‖ → χ x = 0 := by
    intro x hx
    apply b.zero_of_le_dist
    simpa using hx
  have hb_deriv : ∀ k : ℕ, k ≤ 3 → ∃ C : ℝ,
      ∀ x : E3, ‖iteratedFDeriv ℝ k χ x‖ ≤ C := by
    intro k hk
    exact (hb_compact.iteratedFDeriv k).exists_bound_of_continuous
      (hb_smooth.continuous_iteratedFDeriv (m := k)
        (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)))
  obtain ⟨C0, hC0⟩ := hb_deriv 0 (by norm_num)
  obtain ⟨C1, hC1⟩ := hb_deriv 1 (by norm_num)
  obtain ⟨C2, hC2⟩ := hb_deriv 2 (by norm_num)
  obtain ⟨C3, hC3⟩ := hb_deriv 3 (by norm_num)
  let K : ℝ := max 1 (max C0 (max C1 (max C2 C3)))
  have hK0 : C0 ≤ K := by
    dsimp [K]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hK1 : C1 ≤ K := by
    dsimp [K]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hK2 : C2 ≤ K := by
    dsimp [K]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hK3 : C3 ≤ K := by
    dsimp [K]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  refine ⟨χ, hb_smooth, hb_compact, hb_range, hb_inner, hb_outer, K, ?_, ?_⟩
  · dsimp [K]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro k hk x
    interval_cases k
    · exact (hC0 x).trans hK0
    · exact (hC1 x).trans hK1
    · exact (hC2 x).trans hK2
    · exact (hC3 x).trans hK3
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmoothUnitBallCutoff
