import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.HessianOperatorDifference
open scoped ContDiff BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Coordinate Hessian differences control the actual bilinear operator norm. -/
theorem hessian_opNorm_difference_of_components
    (f g : E3 → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x z : E3) (D : ℝ) (hD : 0 ≤ D)
    (hcomponents : ∀ i j : Fin 3,
      |fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1) -
       fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) z
          (EuclideanSpace.single j 1)| ≤ D) :
    ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) z‖ ≤ 9 * D :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let e : Fin 3 → E3 := fun i => EuclideanSpace.single i 1
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) z
  have heval (k : E3 → ℝ) (hk : ContDiff ℝ 2 k) (a v w : E3) :
      fderiv ℝ (fun y => fderiv ℝ k y v) a w = fderiv ℝ (fderiv ℝ k) a w v := by
    have hd : DifferentiableAt ℝ (fderiv ℝ k) a :=
      ((hk.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) a
    have hh := fderiv_clm_apply hd (differentiableAt_const (c := v) (x := a))
    simpa using congrArg (fun L : E3 →L[ℝ] ℝ => L w) hh
  have hb (i j : Fin 3) : |B (e i) (e j)| ≤ D := by
    have h := hcomponents j i
    change |fderiv ℝ (fun y => fderiv ℝ f y (e j)) x (e i) -
      fderiv ℝ (fun y => fderiv ℝ g y (e j)) z (e i)| ≤ D at h
    rw [heval f hf x (e j) (e i), heval g hg z (e j) (e i)] at h
    simpa [B] using h
  have hdec (v : E3) : v = ∑ i : Fin 3, v i • e i := by
    simpa [e, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v).symm
  have hcoord (v : E3) (i : Fin 3) : |v i| ≤ ‖v‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v i
  have hexpand (v w : E3) : B v w =
      ∑ i : Fin 3, ∑ j : Fin 3, v i * w j * B (e i) (e j) := by
    calc
      B v w = B (∑ i : Fin 3, v i • e i) (∑ j : Fin 3, w j • e j) := by
        rw [← hdec v, ← hdec w]
      _ = _ := by
        simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hvalue (v w : E3) : ‖B v w‖ ≤ (9 * D * ‖v‖) * ‖w‖ := by
    rw [hexpand]
    calc
      ‖∑ i : Fin 3, ∑ j : Fin 3, v i * w j * B (e i) (e j)‖ ≤
          ∑ i : Fin 3, ∑ j : Fin 3, ‖v i * w j * B (e i) (e j)‖ := by
        exact (norm_sum_le _ _).trans
          (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖v‖ * ‖w‖ * D := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        have hcoef : |v i * w j| ≤ ‖v‖ * ‖w‖ := by
          rw [abs_mul]
          exact mul_le_mul (hcoord v i) (hcoord w j) (abs_nonneg _) (norm_nonneg _)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul hcoef (hb i j) (abs_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (9 * D * ‖v‖) * ‖w‖ := by simp; ring
  change ‖B‖ ≤ 9 * D
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  exact hvalue v w
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.HessianOperatorDifference
