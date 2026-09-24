import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.RightInverseSmallPerturbation
/-- A genuine bounded right inverse persists under a small composed perturbation. -/
theorem right_inverse_small_perturbation
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (L R : Y →L[ℝ] X) (D : X →L[ℝ] Y)
    (hLD : L.comp D = ContinuousLinearMap.id ℝ X)
    (hsmall : ‖R.comp D‖ < 1) :
    ∃ E : X →L[ℝ] Y,
      (L-R).comp E = ContinuousLinearMap.id ℝ X ∧
      ‖E‖ ≤ ‖D‖ / (1-‖R.comp D‖) :=
/- SWARM_PROOF_BEGIN -/
by
  by_cases hX : Nontrivial X
  · letI : NontrivialTopology X :=
      nontrivialTopology_iff_exists_norm_ne_zero.mpr (by
        obtain ⟨x, hx⟩ := exists_ne (0 : X)
        exact ⟨x, ne_of_gt (norm_pos_iff.mpr hx)⟩)
    let B : X →L[ℝ] X := R.comp D
    have hB : ‖B‖ < 1 := by simpa [B] using hsmall
    let U : (X →L[ℝ] X)ˣ := Units.oneSub B hB
    let A : X →L[ℝ] X := (U⁻¹ : (X →L[ℝ] X)ˣ)
    let E : X →L[ℝ] Y := D.comp A
    have hbase : (L - R).comp D = ContinuousLinearMap.id ℝ X - B := by
      ext x
      simp only [ContinuousLinearMap.comp_apply, sub_apply,
        ContinuousLinearMap.id_apply]
      have hx : L (D x) = x := by
        simpa using congrArg (fun f : X →L[ℝ] X => f x) hLD
      rw [hx]
      rfl
    have hUA : (U : X →L[ℝ] X) * A = 1 := by
      simp [A]
    have hone : (1 : X →L[ℝ] X) = ContinuousLinearMap.id ℝ X := by
      ext x
      rfl
    have hA : (ContinuousLinearMap.id ℝ X - B).comp A = ContinuousLinearMap.id ℝ X := by
      have hU : (U : X →L[ℝ] X) = ContinuousLinearMap.id ℝ X - B := by
        calc
          (U : X →L[ℝ] X) = 1 - B := by simp [U, Units.val_oneSub]
          _ = ContinuousLinearMap.id ℝ X - B := by rw [hone]
      rw [← hU, ← ContinuousLinearMap.mul_def]
      rw [← hone]
      exact hUA
    have hAnorm : ‖A‖ ≤ (1 - ‖B‖)⁻¹ := by
      calc
        ‖A‖ = ‖∑' n : ℕ, B ^ n‖ := by simp [A, U, Units.oneSub]
        _ ≤ ‖(1 : X →L[ℝ] X)‖ - 1 + (1 - ‖B‖)⁻¹ :=
          tsum_geometric_le_of_norm_lt_one B hB
        _ = (1 - ‖B‖)⁻¹ := by simp
    refine ⟨E, ?_, ?_⟩
    · calc
        (L - R).comp E = ((L - R).comp D).comp A := by
          simp only [E, ← ContinuousLinearMap.comp_assoc]
        _ = (ContinuousLinearMap.id ℝ X - B).comp A := by rw [hbase]
        _ = ContinuousLinearMap.id ℝ X := hA
    · calc
        ‖E‖ ≤ ‖D‖ * ‖A‖ := D.opNorm_comp_le A
        _ ≤ ‖D‖ * (1 - ‖B‖)⁻¹ :=
          mul_le_mul_of_nonneg_left hAnorm (norm_nonneg D)
        _ = ‖D‖ / (1 - ‖R.comp D‖) := by simp [B, div_eq_mul_inv]
  · have hsub : Subsingleton X := not_nontrivial_iff_subsingleton.mp hX
    have hD : D = 0 := by
      ext x
      have hx : x = 0 := hsub.elim x 0
      subst x
      simp
    refine ⟨0, ?_, ?_⟩
    · ext x
      have hx : x = 0 := hsub.elim x 0
      subst x
      simp
    · simp [hD]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RightInverseSmallPerturbation
