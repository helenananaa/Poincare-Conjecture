import PoincareConjecture.ProofContract.Refinement20260927.ExtinctionBarrier
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.RefinedWidthFiniteHorizon
open PoincareConjecture.ProofContract.Refinement20260927
theorem width_finite_horizon : WidthHorizonStatement :=
/- SWARM_PROOF_BEGIN -/
by
  intro a c w0 ha hc hw0
  let q := max (c ^ ((1 : ℝ) / 4)) (widthPotential a c 0 w0 / (4 * a)) + 1
  have hcroot : 0 < c ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hc _
  have hqroot : c ^ ((1 : ℝ) / 4) < q := by
    dsimp [q]
    linarith [le_max_left (c ^ ((1 : ℝ) / 4))
      (widthPotential a c 0 w0 / (4 * a))]
  have hqpot : widthPotential a c 0 w0 / (4 * a) < q := by
    dsimp [q]
    linarith [le_max_right (c ^ ((1 : ℝ) / 4))
      (widthPotential a c 0 w0 / (4 * a))]
  have hq : 0 < q := by linarith
  have hcidentity : (c ^ ((1 : ℝ) / 4)) ^ 4 = c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    norm_num
  have hc4 : c < q ^ 4 := by
    calc
      c = (c ^ ((1 : ℝ) / 4)) ^ 4 := hcidentity.symm
      _ < q ^ 4 := pow_lt_pow_left₀ hqroot hcroot.le (by norm_num)
  let T := q ^ 4 - c
  have hT : 0 < T := by dsimp [T]; linarith
  have hroot : (T + c) ^ ((1 : ℝ) / 4) = q := by
    rw [show T + c = q ^ 4 by dsimp [T]; ring]
    simpa using Real.pow_rpow_inv_natCast hq.le (by norm_num : (4 : ℕ) ≠ 0)
  have hscale : 0 < 4 * a := by positivity
  have hmain := (div_lt_iff₀ hscale).mp hqpot
  refine ⟨T, hT, ?_⟩
  rw [hroot]
  simpa [mul_comm] using hmain
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedWidthFiniteHorizon
