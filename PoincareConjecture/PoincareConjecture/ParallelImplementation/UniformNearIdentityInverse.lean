import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.UniformNearIdentityInverse
theorem exists_uniform_near_identity_inverse
    {A P : Type*} [NormedRing A] [NormOneClass A] [CompleteSpace A]
    (a : P → A) (q : ℝ) (hq0 : 0 ≤ q) (hq : q < 1)
    (ha : ∀ p, ‖a p‖ ≤ q) :
    ∃ b : P → A,
      (∀ p, (1-a p)*b p = 1 ∧ b p*(1-a p) = 1) ∧
      (∀ p, ‖b p‖ ≤ 1/(1-q)) ∧
      (∀ p r, b p-b r = b p*(a p-a r)*b r) ∧
      (∀ p r, ‖b p-b r‖ ≤ (1/(1-q))^2*‖a p-a r‖) :=
/- SWARM_PROOF_BEGIN -/
by
  let b : P → A := fun p =>
    ↑((Units.oneSub (a p) ((ha p).trans_lt hq))⁻¹)
  let C : ℝ := 1 / (1 - q)
  have hleft (p : P) : (1 - a p) * b p = 1 := by
    simp [b, Units.val_oneSub]
  have hright (p : P) : b p * (1 - a p) = 1 := by
    simp [b, Units.val_oneSub]
  have hbound (p : P) : ‖b p‖ ≤ C := by
    have hnorm : ‖a p‖ < 1 := (ha p).trans_lt hq
    have hden : 1 - q ≤ 1 - ‖a p‖ := sub_le_sub_left (ha p) 1
    have hqpos : 0 < 1 - q := sub_pos.mpr hq
    calc
      ‖b p‖ = ‖∑' n : ℕ, a p ^ n‖ := by simp [b, Units.oneSub]
      _ ≤ (1 - ‖a p‖)⁻¹ := by
        simpa using tsum_geometric_le_of_norm_lt_one (a p) hnorm
      _ ≤ (1 - q)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hqpos hden
      _ = C := by simp [C, one_div]
  have hres (p r : P) : b p - b r = b p * (a p - a r) * b r := by
    calc
      b p - b r = b p * ((1 - a r) * b r) - (b p * (1 - a p)) * b r := by
        rw [hleft r, hright p]
        simp
      _ = b p * ((1 - a r) - (1 - a p)) * b r := by noncomm_ring
      _ = b p * (a p - a r) * b r := by
        rw [show (1 - a r) - (1 - a p) = a p - a r by abel]
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro p
    exact ⟨hleft p, hright p⟩
  · intro p
    simpa [C] using hbound p
  · exact hres
  · intro p r
    calc
      ‖b p - b r‖ = ‖b p * (a p - a r) * b r‖ := by rw [hres p r]
      _ ≤ (‖b p‖ * ‖a p - a r‖) * ‖b r‖ := by
        calc
          ‖b p * (a p - a r) * b r‖ ≤ ‖b p * (a p - a r)‖ * ‖b r‖ := norm_mul_le _ _
          _ ≤ (‖b p‖ * ‖a p - a r‖) * ‖b r‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ C * ‖a p - a r‖ * C := by
        gcongr <;> exact hbound _
      _ = (1 / (1 - q)) ^ 2 * ‖a p - a r‖ := by
        simp only [pow_two, C]
        ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.UniformNearIdentityInverse
