import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Explicit homotopy pushing the punctured half-ball out to radius one. -/
theorem radial_push_to_unit_complement :
    ∃ H : C(unitInterval × {x : Euclidean3 // (1/2 : ℝ) < ‖x‖}, Euclidean3),
      (∀ (t : unitInterval) (x : {x : Euclidean3 // (1/2 : ℝ) < ‖x‖}),
        H (t,x) = ((1-(t:ℝ)) + (t:ℝ)*max 1 (‖(x:Euclidean3)‖⁻¹)) • (x:Euclidean3)) ∧
      (∀ (x : {x : Euclidean3 // (1/2 : ℝ) < ‖x‖}), H (0,x) = (x:Euclidean3)) ∧
      (∀ (x : {x : Euclidean3 // (1/2 : ℝ) < ‖x‖}), 1 ≤ ‖H (1,x)‖) ∧
      (∀ (t : unitInterval) (x : {x : Euclidean3 // (1/2 : ℝ) < ‖x‖}),
        1 ≤ ‖(x:Euclidean3)‖ → H (t,x) = (x:Euclidean3)) ∧
      (∀ (t : unitInterval) (x : {x : Euclidean3 // (1/2 : ℝ) < ‖x‖}),
        (1/2 : ℝ) < ‖H (t,x)‖ ∧ ‖H (t,x)‖ ≤ max 1 ‖(x:Euclidean3)‖) :=
/- SWARM_PROOF_BEGIN -/
by
  let D := {x : Euclidean3 // (1/2 : ℝ) < ‖x‖}
  let a : unitInterval × D → ℝ := fun p =>
    (1 - (p.1 : ℝ)) + (p.1 : ℝ) * max 1 (‖(p.2 : Euclidean3)‖⁻¹)
  have hnorm : Continuous (fun p : unitInterval × D => ‖(p.2 : Euclidean3)‖) :=
    continuous_norm.comp (continuous_subtype_val.comp continuous_snd)
  have hnorm_pos : ∀ p : unitInterval × D, 0 < ‖(p.2 : Euclidean3)‖ := by
    intro p
    exact lt_trans (by norm_num) p.2.property
  have hinv : Continuous (fun p : unitInterval × D => ‖(p.2 : Euclidean3)‖⁻¹) :=
    hnorm.inv₀ (fun p => (hnorm_pos p).ne')
  have ha : Continuous a := by
    dsimp [a]
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_const.max hinv))
  let H : C(unitInterval × D, Euclidean3) := ContinuousMap.mk
    (fun p => a p • (p.2 : Euclidean3))
    (ha.smul (continuous_subtype_val.comp continuous_snd))
  refine ⟨H, ?_, ?_, ?_, ?_, ?_⟩
  · intro t x
    rfl
  · intro x
    simp [H, a]
  · intro x
    have hx : 0 < ‖(x : Euclidean3)‖ := hnorm_pos (1, x)
    have hmaxmul : max 1 (‖(x : Euclidean3)‖⁻¹) *
        ‖(x : Euclidean3)‖ = max 1 ‖(x : Euclidean3)‖ := by
      rcases le_total ‖(x : Euclidean3)‖ 1 with hcase | hcase
      · rw [max_eq_right ((one_le_inv₀ hx).mpr hcase),
          max_eq_left hcase, inv_mul_cancel₀ hx.ne']
      · rw [max_eq_left ((inv_le_one₀ hx).mpr hcase), max_eq_right hcase]
        simp
    have hnormH : ‖H (1, x)‖ = max 1 ‖(x : Euclidean3)‖ := by
      rw [show H (1, x) =
        ((1 - (1 : ℝ)) + (1 : ℝ) * max 1 (‖(x : Euclidean3)‖⁻¹)) •
          (x : Euclidean3) by rfl]
      rw [show (1 - (1 : ℝ)) + (1 : ℝ) *
          max 1 (‖(x : Euclidean3)‖⁻¹) = max 1 (‖(x : Euclidean3)‖⁻¹) by ring]
      have hmaxnonneg : 0 ≤ max 1 (‖(x : Euclidean3)‖⁻¹) :=
        le_trans (by norm_num) (le_max_left _ _)
      rw [norm_smul, Real.norm_of_nonneg hmaxnonneg]
      exact hmaxmul
    rw [hnormH]
    exact le_max_left _ _
  · intro t x hx
    have hxi : ‖(x : Euclidean3)‖⁻¹ ≤ 1 := by
      exact (inv_le_one₀ (by positivity)).mpr hx
    have hmax : max 1 (‖(x : Euclidean3)‖⁻¹) = 1 :=
      max_eq_left hxi
    rw [show H (t, x) =
      ((1 - (t : ℝ)) + (t : ℝ) * max 1 (‖(x : Euclidean3)‖⁻¹)) •
        (x : Euclidean3) by rfl, hmax]
    simp
  · intro t x
    have ht0 : 0 ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    have hr : 0 < ‖(x : Euclidean3)‖ := hnorm_pos (t, x)
    have hr0 : 0 ≤ ‖(x : Euclidean3)‖ := hr.le
    have hscalar : 0 ≤
        (1 - (t : ℝ)) + (t : ℝ) * max 1 (‖(x : Euclidean3)‖⁻¹) := by
      positivity
    have hnormH : ‖H (t, x)‖ =
        ((1 - (t : ℝ)) + (t : ℝ) * max 1 (‖(x : Euclidean3)‖⁻¹)) *
          ‖(x : Euclidean3)‖ := by
      rw [show H (t, x) =
        ((1 - (t : ℝ)) + (t : ℝ) * max 1 (‖(x : Euclidean3)‖⁻¹)) •
          (x : Euclidean3) by rfl]
      rw [norm_smul, Real.norm_of_nonneg hscalar]
    have hlow : ‖(x : Euclidean3)‖ ≤ ‖H (t, x)‖ := by
      have hcase : ‖(x : Euclidean3)‖ ≤ 1 ∨ 1 ≤ ‖(x : Euclidean3)‖ :=
        le_total _ _
      rcases hcase with hcase | hcase
      · have hinv_mul : ‖(x : Euclidean3)‖⁻¹ * ‖(x : Euclidean3)‖ = 1 :=
          inv_mul_cancel₀ hr.ne'
        have hmaxmul : max 1 (‖(x : Euclidean3)‖⁻¹) *
            ‖(x : Euclidean3)‖ = 1 := by
          rw [max_eq_right ((one_le_inv₀ hr).mpr hcase), hinv_mul]
        have hconv : ‖(x : Euclidean3)‖ ≤
            (1 - (t : ℝ)) * ‖(x : Euclidean3)‖ +
              (t : ℝ) * 1 := by
          calc
            ‖(x : Euclidean3)‖ =
                (1 - (t : ℝ)) * ‖(x : Euclidean3)‖ +
                  (t : ℝ) * ‖(x : Euclidean3)‖ := by ring
            _ ≤ (1 - (t : ℝ)) * ‖(x : Euclidean3)‖ + (t : ℝ) * 1 :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_left hcase ht0)
        rw [show ‖H (t, x)‖ =
          (1 - (t : ℝ)) * ‖(x : Euclidean3)‖ +
            (t : ℝ) * (max 1 (‖(x : Euclidean3)‖⁻¹) *
              ‖(x : Euclidean3)‖) by
                rw [hnormH]; ring]
        simpa [hmaxmul] using hconv
      · have hmaxmul : max 1 (‖(x : Euclidean3)‖⁻¹) *
            ‖(x : Euclidean3)‖ = ‖(x : Euclidean3)‖ := by
          rw [max_eq_left ((inv_le_one₀ hr).mpr hcase)]
          simp
        rw [show ‖H (t, x)‖ =
          (1 - (t : ℝ)) * ‖(x : Euclidean3)‖ +
            (t : ℝ) * (max 1 (‖(x : Euclidean3)‖⁻¹) *
              ‖(x : Euclidean3)‖) by
                rw [hnormH]; ring]
        rw [hmaxmul]
        have heq : (1 - (t : ℝ)) * ‖(x : Euclidean3)‖ +
            (t : ℝ) * ‖(x : Euclidean3)‖ = ‖(x : Euclidean3)‖ := by ring
        rw [heq]
    have hupp : ‖H (t, x)‖ ≤ max 1 ‖(x : Euclidean3)‖ := by
      have hcase : ‖(x : Euclidean3)‖ ≤ 1 ∨ 1 ≤ ‖(x : Euclidean3)‖ :=
        le_total _ _
      rcases hcase with hcase | hcase
      · have hinv_mul : ‖(x : Euclidean3)‖⁻¹ * ‖(x : Euclidean3)‖ = 1 :=
          inv_mul_cancel₀ hr.ne'
        have hmaxmul : max 1 (‖(x : Euclidean3)‖⁻¹) *
            ‖(x : Euclidean3)‖ = 1 := by
          rw [max_eq_right ((one_le_inv₀ hr).mpr hcase), hinv_mul]
        have hconv :
            (1 - (t : ℝ)) * ‖(x : Euclidean3)‖ + (t : ℝ) * 1 ≤
              max 1 ‖(x : Euclidean3)‖ := by
          rw [max_eq_left hcase]
          calc
            (1 - (t : ℝ)) * ‖(x : Euclidean3)‖ + (t : ℝ) * 1 ≤
                (1 - (t : ℝ)) * 1 + (t : ℝ) * 1 :=
              add_le_add (mul_le_mul_of_nonneg_left hcase
                (sub_nonneg.mpr ht1)) le_rfl
            _ = 1 := by ring
        rw [show ‖H (t, x)‖ =
          (1 - (t : ℝ)) * ‖(x : Euclidean3)‖ +
            (t : ℝ) * (max 1 (‖(x : Euclidean3)‖⁻¹) *
              ‖(x : Euclidean3)‖) by
                rw [hnormH]; ring]
        simpa [hmaxmul] using hconv
      · have hmaxmul : max 1 (‖(x : Euclidean3)‖⁻¹) *
            ‖(x : Euclidean3)‖ = ‖(x : Euclidean3)‖ := by
          rw [max_eq_left ((inv_le_one₀ hr).mpr hcase)]
          simp
        rw [show ‖H (t, x)‖ =
          (1 - (t : ℝ)) * ‖(x : Euclidean3)‖ +
            (t : ℝ) * (max 1 (‖(x : Euclidean3)‖⁻¹) *
              ‖(x : Euclidean3)‖) by
                rw [hnormH]; ring]
        rw [hmaxmul]
        rw [max_eq_right hcase]
        have heq : (1 - (t : ℝ)) * ‖(x : Euclidean3)‖ +
            (t : ℝ) * ‖(x : Euclidean3)‖ = ‖(x : Euclidean3)‖ := by ring
        rw [heq]
    exact ⟨lt_of_lt_of_le x.property hlow, hupp⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
