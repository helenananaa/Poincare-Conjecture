import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.GaussianShiftedThirdMajorant
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.WeightedTranslationControl
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveJointSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** gaussian hessian weighted translation. -/
theorem gaussian_hessian_weighted_translation 
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ), 0 < t → ∀ (h : E3), ‖h‖ ≤ Real.sqrt t → ∀ i j : Fin 3,
      Integrable (fun y : E3 => |heatHessian3 t i j (y+h)-heatHessian3 t i j y| * ‖y‖^alpha) volume ∧
      (∫ y : E3, |heatHessian3 t i j (y+h)-heatHessian3 t i j y| * ‖y‖^alpha) ≤
        C*‖h‖*t^(alpha/2-3/2) :=
/- SWARM_PROOF_BEGIN -/
by
  rcases gaussian_shifted_third_majorant alpha ha ha1 with ⟨C, hC, hmajorant⟩
  refine ⟨C, hC, ?_⟩
  intro t ht h hh i j
  have hkernel : ContDiff ℝ ∞
      (fun x : E3 => MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t x) := by
    apply contDiffOn_univ.mp
    have hslice : ContDiffOn ℝ ∞ (fun x : E3 => (t, x)) univ :=
      contDiffOn_const.prodMk contDiffOn_id
    have hmap : MapsTo (fun x : E3 => (t, x)) univ
        (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
      intro x hx
      exact ⟨ht, mem_univ x⟩
    simpa only [Function.comp_def] using
      (MorganTianLib.ParabolicPDE.euclideanHeatKernel_joint_smooth 3).comp hslice hmap
  have hfirst : ContDiff ℝ 2
      (fun x : E3 => fderiv ℝ (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t)
        x (EuclideanSpace.single i 1)) := by
    have hfd : ContDiff ℝ 2
        (fderiv ℝ (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t)) :=
      hkernel.fderiv_right (m := 2) (by
        norm_num
        exact WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
    exact hfd.clm_apply contDiff_const
  have hsmooth : ContDiff ℝ 1 (heatHessian3 t i j) := by
    have hfd : ContDiff ℝ 1
        (fderiv ℝ (fun x : E3 =>
          fderiv ℝ (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t) x
            (EuclideanSpace.single i 1))) :=
      hfirst.fderiv_right (m := 1) (by norm_num)
    change ContDiff ℝ 1 (fun x : E3 =>
      fderiv ℝ (fun x : E3 =>
        fderiv ℝ (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t) x
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
    exact hfd.clm_apply contDiff_const
  rcases hmajorant t ht with ⟨D, hDi, hDnonneg, hDint, hder⟩
  have hctrl := weighted_translation_control
    (f := heatHessian3 t i j) hsmooth alpha (Real.sqrt t) ha
    (Real.sqrt_nonneg t) D hDi hDnonneg
    (by
      intro y u v hu
      exact hder y u v hu i j)
    h hh
  rcases hctrl with ⟨hIntegrable, hBound⟩
  refine ⟨hIntegrable, ?_⟩
  calc
    (∫ y : E3, |heatHessian3 t i j (y + h) - heatHessian3 t i j y| * ‖y‖^alpha)
        ≤ ‖h‖ * (∫ y : E3, D y) := hBound
    _ ≤ ‖h‖ * (C * t^(alpha/2-3/2)) :=
      mul_le_mul_of_nonneg_left hDint (norm_nonneg h)
    _ = C * ‖h‖ * t^(alpha/2-3/2) := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
