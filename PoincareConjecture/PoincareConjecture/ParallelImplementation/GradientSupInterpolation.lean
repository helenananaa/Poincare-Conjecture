import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.GradientSupInterpolation
open scoped ContDiff
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- A first derivative is controlled by the value and genuine second derivative on the full space. -/
theorem gradient_sup_interpolation
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (f : E3 → V) (hf : ContDiff ℝ 2 f) (A M r : ℝ)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hr : 0 < r)
    (hvalue : ∀ x, ‖f x‖ ≤ A)
    (hhess : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) :
    ∀ x, ‖fderiv ℝ f x‖ ≤ 2*A/r + M*r :=
/- SWARM_PROOF_BEGIN -/
by
  intro x
  let L : E3 →L[ℝ] V := fderiv ℝ f x
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hDf : Differentiable ℝ (fun z : E3 => fderiv ℝ f z) := by
    have h : ContDiff ℝ 1 (fun z : E3 => fderiv ℝ f z) :=
      hf.fderiv_right (by norm_num)
    exact h.differentiable_one
  have hfdiff : Differentiable ℝ f := hf1.differentiable_one
  have hLip (z : E3) :
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ M * ‖z - x‖ := by
    exact (convex_univ : Convex ℝ (Set.univ : Set E3)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hDf.differentiableAt)
      (fun z _ => hhess z)
      (Set.mem_univ x) (Set.mem_univ z)
  have hvar : ∀ z ∈ Metric.closedBall x r,
      ‖fderiv ℝ f z - L‖ ≤ M * r := by
    intro z hz
    have hz' : ‖z - x‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    calc
      ‖fderiv ℝ f z - L‖ ≤ M * ‖z - x‖ := by simpa [L] using hLip z
      _ ≤ M * r := mul_le_mul_of_nonneg_left hz' hM
  have hB : 0 ≤ 2 * A / r + M * r := by positivity
  have hunit (v : E3) (hv : ‖v‖ ≤ 1) : ‖L v‖ ≤ 2 * A / r + M * r := by
    let y : E3 := x + r • v
    have hydist : ‖y - x‖ ≤ r := by
      calc
        ‖y - x‖ = r * ‖v‖ := by
          simp [y, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        _ ≤ r := by nlinarith [mul_le_mul_of_nonneg_left hv hr.le]
    have hy : y ∈ Metric.closedBall x r := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact hydist
    have hrem : ‖f y - f x - L (y - x)‖ ≤ (M * r) * ‖y - x‖ := by
      exact (convex_closedBall x r).norm_image_sub_le_of_norm_fderiv_le'
        (fun z _ => hfdiff.differentiableAt)
        (fun z hz => by simpa [L] using hvar z hz)
        (Metric.mem_closedBall_self hr.le) hy
    have hrem' : ‖f y - f x - L (y - x)‖ ≤ M * r * r := by
      exact hrem.trans (mul_le_mul_of_nonneg_left hydist (mul_nonneg hM hr.le))
    have hval : ‖f y - f x‖ ≤ 2 * A := by
      calc
        ‖f y - f x‖ ≤ ‖f y‖ + ‖f x‖ := norm_sub_le _ _
        _ ≤ A + A := add_le_add (hvalue y) (hvalue x)
        _ = 2 * A := by ring
    have hsum : ‖L (y - x)‖ ≤ 2 * A + M * r * r := by
      calc
        ‖L (y - x)‖ = ‖(f y - f x) - (f y - f x - L (y - x))‖ := by
          congr 1; abel
        _ ≤ ‖f y - f x‖ + ‖f y - f x - L (y - x)‖ := norm_sub_le _ _
        _ ≤ 2 * A + M * r * r := add_le_add hval hrem'
    have hysub : y - x = r • v := by
      dsimp [y]
      exact add_sub_cancel_left _ _
    have hLnorm : ‖L (y - x)‖ = r * ‖L v‖ := by
      rw [hysub, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hrLv : r * ‖L v‖ ≤ 2 * A + M * r * r := by
      rw [← hLnorm]
      exact hsum
    apply (mul_le_mul_iff_left₀ hr).mp
    calc
      ‖L v‖ * r = r * ‖L v‖ := by ring
      _ ≤ 2 * A + M * r * r := hrLv
      _ = (2 * A / r + M * r) * r := by field_simp [ne_of_gt hr]
  have hLbound : ∀ v : E3, ‖L v‖ ≤ (2 * A / r + M * r) * ‖v‖ := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      let u : E3 := ‖v‖⁻¹ • v
      have hu : ‖u‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hvpos.le)]
        exact inv_mul_cancel₀ hvpos.ne'
      have hvu : ‖v‖ • u = v := by
        dsimp [u]
        rw [smul_smul, mul_inv_cancel₀ hvpos.ne', one_smul]
      calc
        ‖L v‖ = ‖L (‖v‖ • u)‖ := by rw [hvu]
        _ = ‖‖v‖ • L u‖ := by rw [map_smul]
        _ = ‖v‖ * ‖L u‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hvpos.le]
        _ ≤ ‖v‖ * (2 * A / r + M * r) :=
          mul_le_mul_of_nonneg_left (hunit u hu.le) (norm_nonneg v)
        _ = (2 * A / r + M * r) * ‖v‖ := by ring
  have hnorm : ‖L‖ ≤ 2 * A / r + M * r := L.opNorm_le_bound hB hLbound
  simpa [L] using hnorm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.GradientSupInterpolation
