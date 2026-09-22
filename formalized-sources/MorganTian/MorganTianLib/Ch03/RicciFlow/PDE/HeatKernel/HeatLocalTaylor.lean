import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SymmetricQuadraticDifferential
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GradientLinearRemainder
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursivePolynomialMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GaussianNormForm
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HeatTimeDerivativeL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatTimeEquation
import Mathlib
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Local uniform quadratic remainder for the actual Frechet derivatives. -/
theorem C2_local_quadratic_remainder (f : E3 → ℝ) (hf : ContDiff ℝ 2 f) (x : E3) :
    ∀ eta : ℝ, 0<eta → ∃ r : ℝ, 0<r ∧ ∀ y : E3, ‖y‖<r →
      |f (x-y)-f x+fderiv ℝ f x y-(1/2:ℝ)*
        (fderiv ℝ (fun z : E3 => fderiv ℝ f z) x y) y| ≤ eta*‖y‖^2 :=
/- SWARM_PROOF_BEGIN -/
by
  intro eta heta
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := fderiv ℝ (fun z : E3 => fderiv ℝ f z) x
  have hB : ∀ v w : E3, B v w = B w v := by
    intro v w
    exact hf.contDiffAt.isSymmSndFDerivAt (by norm_num) v w
  obtain ⟨r, hr, hrem⟩ := gradient_local_linear_remainder f hf x eta heta
  let g : E3 → ℝ := fun z =>
    f z - f x - fderiv ℝ f x (z - x) - (1 / 2 : ℝ) * B (z - x) (z - x)
  have hgderiv : ∀ z : E3,
      HasFDerivAt g (fderiv ℝ f z - fderiv ℝ f x - B (z - x)) z := by
    intro z
    have htranslated : HasFDerivAt (fun w : E3 => w - x)
        (ContinuousLinearMap.id ℝ E3) z :=
      (hasFDerivAt_id z).sub_const x
    have hfd : HasFDerivAt f (fderiv ℝ f z) z :=
      (hf.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt
    have hconst : HasFDerivAt (fun _ : E3 => f x) (0 : E3 →L[ℝ] ℝ) z :=
      hasFDerivAt_const (f x) z
    have hlin : HasFDerivAt (fun w : E3 => fderiv ℝ f x (w - x))
        (fderiv ℝ f x) z := by
      exact (hasFDerivAt_comp_sub (f := fun v : E3 => fderiv ℝ f x v)
        (f' := fderiv ℝ f x) (x := z) x).2 (fderiv ℝ f x).hasFDerivAt
    have hquad := symmetric_quadratic_differential B hB x z
    have hsub := (hfd.sub hconst).sub hlin
    have hsub' := hsub.sub hquad
    exact (hsub'.congr_fderiv (by simp only [sub_zero])).congr_of_eventuallyEq (by
      filter_upwards [] with w
      rfl)
  have hg_fderiv : ∀ z : E3,
      fderiv ℝ g z = fderiv ℝ f z - fderiv ℝ f x - B (z - x) := by
    intro z
    exact (hgderiv z).fderiv
  refine ⟨r, hr, ?_⟩
  intro y hy
  let s : Set E3 := segment ℝ x (x - y)
  have hs : Convex ℝ s := convex_segment x (x - y)
  have hxs : x ∈ s := left_mem_segment ℝ x (x - y)
  have hys : x - y ∈ s := right_mem_segment ℝ x (x - y)
  have hbound : ∀ z ∈ s, ‖fderiv ℝ g z - (0 : E3 →L[ℝ] ℝ)‖ ≤ eta * ‖y‖ := by
    intro z hz
    have hzy : ‖z - x‖ ≤ ‖y‖ := by
      have h := norm_sub_le_of_mem_segment hz
      have hxy : (x - y) - x = -y := by abel
      rw [hxy, norm_neg] at h
      exact h
    rw [hg_fderiv z]
    rw [sub_zero]
    exact (hrem z (lt_of_le_of_lt hzy hy)).trans
      (mul_le_mul_of_nonneg_left hzy (le_of_lt heta))
  have hmv := hs.norm_image_sub_le_of_norm_fderiv_le'
    (f := g) (φ := (0 : E3 →L[ℝ] ℝ))
    (fun z hz => (hgderiv z).differentiableAt) hbound hxs hys
  have hgx : g x = 0 := by
    dsimp [g]
    simp only [sub_self, map_zero, mul_zero]
  have hxy : (x - y) - x = -y := by abel
  have hleft : g (x - y) =
      f (x - y) - f x + fderiv ℝ f x y - (1 / 2 : ℝ) * B y y := by
    dsimp [g]
    rw [hxy]
    rw [map_neg]
    have hBneg : B (-y) = -B y := map_neg B y
    rw [hBneg]
    have hBquad : (-B y) (-y) = (B y) y := by
      rw [neg_apply, map_neg, neg_neg]
    rw [hBquad]
    ring
  have hright : (eta * ‖y‖) * ‖(x - y) - x‖ = eta * ‖y‖ ^ 2 := by
    rw [hxy, norm_neg]
    ring
  rw [show ‖g (x - y) - g x - (0 : E3 →L[ℝ] ℝ) ((x - y) - x)‖ =
      ‖g (x - y)‖ by rw [hgx]; simp]
    at hmv
  rw [hleft, Real.norm_eq_abs, hright] at hmv
  exact hmv
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
