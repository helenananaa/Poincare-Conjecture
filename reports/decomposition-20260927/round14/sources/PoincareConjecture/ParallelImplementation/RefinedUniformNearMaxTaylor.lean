import PoincareConjecture.ProofContract.Refinement20260927.MinimaxComparison
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.RefinedUniformNearMaxTaylor
open PoincareConjecture.ProofContract.Refinement20260927
theorem uniform_near_max_taylor : UniformNearMaxTaylorStatement :=
/- SWARM_PROOF_BEGIN -/
by
  unfold UniformNearMaxTaylorStatement
  intro v velocity future m q W delta L Q K H J hdelta hH hL hQ hK hW hq hv hvelocity hnear hTaylor
  have hden : 0 < L + Q + 1 := by
    positivity
  let h0 : ℝ := min H (delta / (L + Q + 1))
  have hh0 : 0 < h0 := by
    dsimp [h0]
    exact lt_min hH (div_pos hdelta hden)
  have hh0H : h0 ≤ H := by
    dsimp [h0]
    exact min_le_left _ _
  refine ⟨h0, hh0, hh0H, ?_⟩
  intro j hj h hh hh0' x
  have hhH : h < H := lt_of_lt_of_le hh0' hh0H
  have hsmall : h < delta / (L + Q + 1) := by
    exact lt_of_lt_of_le hh0' (by dsimp [h0]; exact min_le_right _ _)
  have hprod : h * (L + Q + 1) < delta := (lt_div_iff₀ hden).mp hsmall
  have hfactor : L + Q ≤ L + Q + 1 := by linarith
  have hbound : h * (L + Q) ≤ delta := by
    calc
      h * (L + Q) ≤ h * (L + Q + 1) :=
        mul_le_mul_of_nonneg_left hfactor hh.le
      _ ≤ delta := hprod.le
  have hTaylor' := hTaylor j hj h hh hhH x
  by_cases hhigh : W - delta < v j x
  · have hvelq := hnear j hj x hhigh
    have hmul : h * velocity j x ≤ h * q j :=
      mul_le_mul_of_nonneg_left hvelq hh.le
    have hv' := hv j hj x
    calc
      future j h x ≤ v j x + h * velocity j x + K * h ^ 2 := hTaylor'
      _ ≤ m j + h * q j + K * h ^ 2 := by nlinarith
  · have hvlow : v j x ≤ W - delta := le_of_not_gt hhigh
    have hvelL := hvelocity j hj x
    have hmulL : h * velocity j x ≤ h * L :=
      mul_le_mul_of_nonneg_left hvelL hh.le
    have hmulq : h * (-Q) ≤ h * q j :=
      mul_le_mul_of_nonneg_left (hq j hj) hh.le
    have hWj := hW j hj
    have hLQ : h * L + h * Q ≤ delta := by
      nlinarith [hbound]
    calc
      future j h x ≤ v j x + h * velocity j x + K * h ^ 2 := hTaylor'
      _ ≤ m j + h * q j + K * h ^ 2 := by nlinarith
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedUniformNearMaxTaylor
