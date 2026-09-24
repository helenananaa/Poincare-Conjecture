import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SixComponentHessianNorm
open scoped ContDiff BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Scalar component Hessian operator bounds control the genuine vector-valued Hessian. -/
theorem six_component_hessian_norm_difference
    (f g : E3 → E6) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x z : E3) (D : ℝ) (hD : 0 ≤ D)
    (hcomp : ∀ k : Fin 6,
      ‖fderiv ℝ (fderiv ℝ (fun y => f y k)) x -
        fderiv ℝ (fderiv ℝ (fun y => g y k)) z‖ ≤ D) :
    ‖fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ g) z‖ ≤ 6*D :=
/- SWARM_PROOF_BEGIN -/
by
  let P (k : Fin 6) : E6 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 6 => ℝ) k
  let C (k : Fin 6) : (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] ℝ) :=
    ContinuousLinearMap.compL ℝ E3 E6 ℝ (P k)
  have hproj_apply (k : Fin 6) (a : E6) : P k a = a k := by
    simp [P, PiLp.proj]
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have hgderiv : DifferentiableAt ℝ (fderiv ℝ g) z :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) z
  have hsecondF (k : Fin 6) :
      fderiv ℝ (fun y => fderiv ℝ (fun u => f u k) y) x =
        (C k).comp (fderiv ℝ (fun y => fderiv ℝ f y) x) := by
    have hprojfun : (fun u : E6 => u k) = P k := by
      funext u
      simp [P, PiLp.proj]
    have hfirst (y : E3) :
        fderiv ℝ (fun u => f u k) y = (P k).comp (fderiv ℝ f y) := by
      have h := fderiv_comp (g := P k) (f := f) (x := y)
        (P k).differentiableAt (hf.differentiable (by norm_num) y)
      have hcompfun : (fun u => f u k) = (P k) ∘ f := by
        funext u
        simpa [Function.comp_def] using congrFun hprojfun (f u)
      rw [hcompfun]
      simpa [Function.comp_def] using h
    have hfun :
        (fun y => fderiv ℝ (fun u => f u k) y) = fun y => C k (fderiv ℝ f y) := by
      funext y
      rw [hfirst y]
      simp [C, ContinuousLinearMap.compL_apply]
    change fderiv ℝ (fun y => fderiv ℝ (fun u => f u k) y) x = _
    rw [hfun]
    have h := fderiv_comp (g := C k) (f := fderiv ℝ f) (x := x)
      (C k).differentiableAt hfderiv
    simpa [Function.comp_def] using h
  have hsecondG (k : Fin 6) :
      fderiv ℝ (fun y => fderiv ℝ (fun u => g u k) y) z =
        (C k).comp (fderiv ℝ (fun y => fderiv ℝ g y) z) := by
    have hprojfun : (fun u : E6 => u k) = P k := by
      funext u
      simp [P, PiLp.proj]
    have hfirst (y : E3) :
        fderiv ℝ (fun u => g u k) y = (P k).comp (fderiv ℝ g y) := by
      have h := fderiv_comp (g := P k) (f := g) (x := y)
        (P k).differentiableAt (hg.differentiable (by norm_num) y)
      have hcompfun : (fun u => g u k) = (P k) ∘ g := by
        funext u
        simpa [Function.comp_def] using congrFun hprojfun (g u)
      rw [hcompfun]
      simpa [Function.comp_def] using h
    have hfun :
        (fun y => fderiv ℝ (fun u => g u k) y) = fun y => C k (fderiv ℝ g y) := by
      funext y
      rw [hfirst y]
      simp [C, ContinuousLinearMap.compL_apply]
    change fderiv ℝ (fun y => fderiv ℝ (fun u => g u k) y) z = _
    rw [hfun]
    have h := fderiv_comp (g := C k) (f := fderiv ℝ g) (x := z)
      (C k).differentiableAt hgderiv
    simpa [Function.comp_def] using h
  have hcoordF (k : Fin 6) (v w : E3) :
      fderiv ℝ (fderiv ℝ (fun y => f y k)) x v w =
        (fderiv ℝ (fderiv ℝ f) x v w) k := by
    simpa [C, ContinuousLinearMap.compL_apply, P] using
      congrArg (fun T : E3 →L[ℝ] E3 →L[ℝ] ℝ => T v w) (hsecondF k)
  have hcoordG (k : Fin 6) (v w : E3) :
      fderiv ℝ (fderiv ℝ (fun y => g y k)) z v w =
        (fderiv ℝ (fderiv ℝ g) z v w) k := by
    simpa [C, ContinuousLinearMap.compL_apply, P] using
      congrArg (fun T : E3 →L[ℝ] E3 →L[ℝ] ℝ => T v w) (hsecondG k)
  have hnorm_sum (a : E6) : ‖a‖ ≤ ∑ k : Fin 6, ‖a k‖ := by
    rw [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact Finset.sum_nonneg fun k hk => norm_nonneg _
    · simpa using
        (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
          (f := fun k : Fin 6 => ‖a k‖) (by intro k hk; exact norm_nonneg _))
  let H : E3 →L[ℝ] E3 →L[ℝ] E6 :=
    fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) z
  have hscalar (k : Fin 6) (v w : E3) :
      ‖(H v w) k‖ ≤ D * ‖v‖ * ‖w‖ := by
    rw [← hproj_apply k (H v w)]
    simp only [H, sub_apply]
    rw [map_sub, hproj_apply, hproj_apply]
    rw [← hcoordF k v w, ← hcoordG k v w]
    let S : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
      fderiv ℝ (fderiv ℝ (fun y => f y k)) x -
        fderiv ℝ (fderiv ℝ (fun y => g y k)) z
    have hv : ‖S v‖ ≤ D * ‖v‖ := (S.le_of_opNorm_le (hcomp k)) v
    change ‖S v w‖ ≤ D * ‖v‖ * ‖w‖
    calc
      ‖S v w‖ ≤ ‖S v‖ * ‖w‖ := (S v).le_opNorm w
      _ ≤ (D * ‖v‖) * ‖w‖ := mul_le_mul_of_nonneg_right hv (norm_nonneg _)
  have hEval (v w : E3) : ‖H v w‖ ≤ (6 * D * ‖v‖) * ‖w‖ := by
    calc
      ‖H v w‖ ≤ ∑ k : Fin 6, ‖(H v w) k‖ := hnorm_sum _
      _ ≤ ∑ k : Fin 6, D * ‖v‖ * ‖w‖ := Finset.sum_le_sum fun k _ => hscalar k v w
      _ = (6 * D * ‖v‖) * ‖w‖ := by simp [Finset.sum_const, mul_assoc]
  have hInner (v : E3) : ‖H v‖ ≤ (6 * D) * ‖v‖ := by
    apply ContinuousLinearMap.opNorm_le_bound (H v) (by positivity)
    intro w
    calc
      ‖H v w‖ ≤ (6 * D * ‖v‖) * ‖w‖ := hEval v w
      _ = (6 * D) * ‖v‖ * ‖w‖ := by ring
  calc
    ‖H‖ ≤ 6 * D := by
      apply ContinuousLinearMap.opNorm_le_bound H (by positivity)
      exact hInner
    _ = 6 * D := rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SixComponentHessianNorm
