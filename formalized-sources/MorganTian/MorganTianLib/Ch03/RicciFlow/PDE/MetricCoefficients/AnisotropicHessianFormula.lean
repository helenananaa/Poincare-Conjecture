import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.AnisotropicHeatKernel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LinearPullbackSecondDerivative
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** anisotropic hessian formula. -/
theorem anisotropic_hessian_formula 
    (B : E3 ≃L[ℝ] E3) (t : ℝ) (ht : 0 < t) (x v w : E3) :
    fderiv ℝ (fun y : E3 => fderiv ℝ (anisotropicHeatKernel B t) y v) x w =
      |LinearMap.det B.toLinearEquiv.toLinearMap|⁻¹ *
        fderiv ℝ (fun y : E3 => fderiv ℝ (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t) y
          (B.symm v)) (B.symm x) (B.symm w) :=
/- SWARM_PROOF_BEGIN -/
by
  let c : ℝ := |LinearMap.det B.toLinearEquiv.toLinearMap|⁻¹
  let f : E3 → ℝ := fun y => MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t y
  let g : E3 → ℝ := fun y => f (B.symm y)
  have hgauss := MorganTianLib.ParabolicPDE.gaussianHeatKernel_derivatives ht
  have hf : ContDiff ℝ ∞ f := by
    unfold f MorganTianLib.ParabolicPDE.euclideanHeatKernel
    exact contDiff_prod (fun i _ => hgauss.1.comp (by fun_prop))
  have hg (y : E3) : ContDiffAt ℝ 2 g y := by
    have hbase : ContDiffAt ℝ 2 f (B.symm y) := by
      intro n hn
      exact hf.contDiffAt (x := B.symm y) n (by simp)
    have hmap : ContDiffAt ℝ 2 (fun z : E3 => B.symm z) y := by
      fun_prop
    have hcomp := hbase.comp y hmap
    have hcomp' : ContDiffAt ℝ 2 g y := by
      simpa [g, Function.comp_def] using hcomp
    exact hcomp'
  have hfun : anisotropicHeatKernel B t = (fun y : E3 => c * g y) := by
    funext y
    rfl
  have hfirst : (fun y : E3 => fderiv ℝ (anisotropicHeatKernel B t) y v) =
      (fun y : E3 => c * fderiv ℝ g y v) := by
    funext y
    rw [hfun, fderiv_const_mul ((hg y).differentiableAt (by norm_num))]
    simp only [smul_apply, smul_eq_mul]
  have hgderiv : ContDiffAt ℝ 1 (fderiv ℝ g) x :=
    (hg x).fderiv_right (by norm_num)
  have hsecondDiff : DifferentiableAt ℝ (fun y : E3 => fderiv ℝ g y v) x := by
    have hcont : ContDiffAt ℝ 1 (fun y : E3 => fderiv ℝ g y v) x := by
      simpa only using hgderiv.clm_apply (contDiffAt_const)
    exact hcont.differentiableAt (by norm_num)
  rw [hfirst, fderiv_const_mul hsecondDiff]
  simp only [smul_apply, smul_eq_mul]
  have hfAt : ContDiffAt ℝ 2 f (B.symm x) := by
    intro n hn
    exact hf.contDiffAt (x := B.symm x) n (by simp)
  have hpull : fderiv ℝ (fun y : E3 => fderiv ℝ g y v) x w =
      fderiv ℝ (fun y : E3 => fderiv ℝ f y (B.symm v))
        (B.symm x) (B.symm w) := by
    simpa [g, f] using
      (linear_pullback_second_derivative f B.symm.toContinuousLinearMap x v w hfAt)
  simpa [c, f] using congrArg (fun z : ℝ => c * z) hpull
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
