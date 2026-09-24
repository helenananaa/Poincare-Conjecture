import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.GradientFiniteDifference
open scoped ContDiff
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Uniform first-order finite differences approximate actual derivative evaluations. -/
theorem gradient_finite_difference_error
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (f : E3 → V) (hf : ContDiff ℝ 2 f)
    (M r : ℝ) (hM : 0 ≤ M) (hr : 0 < r)
    (hbound : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) :
    ∀ (x : E3) (i : Fin 3),
      ‖fderiv ℝ f x (EuclideanSpace.single i 1) -
        r⁻¹ • (f (x+r • EuclideanSpace.single i 1)-f x)‖ ≤ M*r :=
/- SWARM_PROOF_BEGIN -/
by
  intro x i
  let e : E3 := EuclideanSpace.single i 1
  let y : E3 := x + r • e
  let g : E3 → E3 →L[ℝ] V := fun z => fderiv ℝ f z
  have he : ‖e‖ = 1 := by simp [e]
  have hgC1 : ContDiff ℝ 1 g := by
    dsimp [g]
    exact hf.fderiv_right (m := 1) (by norm_num)
  have hgDiff : Differentiable ℝ g := hgC1.differentiable (by norm_num)
  have hLip : ∀ u v : E3, ‖g v - g u‖ ≤ M * ‖v - u‖ := by
    intro u v
    exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (f := g) (C := M)
      (fun _ _ => hgDiff.differentiableAt)
      (fun z _ => hbound z)
      (Set.mem_univ u) (Set.mem_univ v)
  have hball : ∀ z ∈ Metric.closedBall x r, ‖g z - g x‖ ≤ M * r := by
    intro z hz
    have hzdist : ‖z - x‖ ≤ r := by
      simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hz)
    calc
      ‖g z - g x‖ ≤ M * ‖z - x‖ := hLip x z
      _ ≤ M * r := mul_le_mul_of_nonneg_left hzdist hM
  have hdir : y - x = r • e := by
    simp [y]
  have hdirnorm : ‖y - x‖ = r := by
    rw [hdir, norm_smul, Real.norm_eq_abs, abs_of_pos hr, he, mul_one]
  have hx : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr.le
  have hy : y ∈ Metric.closedBall x r := by
    rw [mem_closedBall_iff_norm, hdir]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, he, mul_one]
  have hrem :
      ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ (M * r) * ‖y - x‖ := by
    exact (convex_closedBall x r).norm_image_sub_le_of_norm_fderiv_le'
      (f := f) (φ := fderiv ℝ f x) (C := M * r)
      (fun _ _ => (hf.differentiable (by norm_num)).differentiableAt)
      (fun z hz => hball z hz)
      hx hy
  have hvec :
      fderiv ℝ f x e - r⁻¹ • (f y - f x) =
        - (r⁻¹ • (f y - f x - fderiv ℝ f x (y - x))) := by
    simp only [hdir, map_smul]
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul]
    abel
  calc
    ‖fderiv ℝ f x e - r⁻¹ • (f y - f x)‖ =
        ‖r⁻¹‖ * ‖f y - f x - fderiv ℝ f x (y - x)‖ := by
          rw [hvec, norm_neg, norm_smul]
    _ ≤ ‖r⁻¹‖ * ((M * r) * ‖y - x‖) :=
      mul_le_mul_of_nonneg_left hrem (norm_nonneg _)
    _ = M * r := by
      rw [norm_inv, Real.norm_eq_abs, abs_of_pos hr, hdirnorm]
      field_simp [ne_of_gt hr]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.GradientFiniteDifference
