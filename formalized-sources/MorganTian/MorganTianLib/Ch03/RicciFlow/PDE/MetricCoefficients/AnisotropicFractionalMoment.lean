import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.AnisotropicHeatKernel
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalMoment
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** anisotropic fractional moment. -/
theorem anisotropic_fractional_moment 
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : E3 ≃L[ℝ] E3) (t : ℝ), 0 < t →
      Integrable (fun y : E3 => anisotropicHeatKernel B t y*‖y‖^alpha) volume ∧
      (∫ y : E3, anisotropicHeatKernel B t y*‖y‖^alpha) ≤
        C*‖B.toContinuousLinearMap‖^alpha*t^(alpha/2) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C, hC, hmoment⟩ :=
    MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_fractional_moment
      alpha ha ha1
  refine ⟨C, hC, ?_⟩
  intro B t ht
  have hfrac := hmoment t ht
  let f : E3 → E3 := fun y => B.symm y
  let L : E3 →L[ℝ] E3 := B.symm.toContinuousLinearMap
  have hdet : LinearMap.det B.toLinearEquiv.toLinearMap ≠ 0 :=
    (LinearEquiv.isUnit_det' B.toLinearEquiv).ne_zero
  have hdet_symm :
      LinearMap.det (B.symm.toContinuousLinearMap.toLinearMap) =
        (LinearMap.det B.toLinearEquiv.toLinearMap)⁻¹ := by
    simpa using LinearEquiv.det_coe_symm B.toLinearEquiv
  have hcoeff : |B.symm.toContinuousLinearMap.det| =
      |LinearMap.det B.toLinearEquiv.toLinearMap|⁻¹ := by
    rw [ContinuousLinearMap.det, hdet_symm, abs_inv]
  have hf' : ∀ y ∈ (Set.univ : Set E3),
      HasFDerivWithinAt f L Set.univ y := by
    intro y hy
    simpa [f, L] using
      (ContinuousLinearMap.hasFDerivAt L (x := y)).hasFDerivWithinAt (s := Set.univ)
  have hf : Set.InjOn f (Set.univ : Set E3) := by
    intro x hx y hy hxy
    exact B.symm.injective hxy
  let g : E3 → ℝ := fun z =>
    MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t z * ‖B z‖ ^ alpha
  have hweight (z : E3) : ‖B z‖ ^ alpha ≤
      ‖B.toContinuousLinearMap‖ ^ alpha * ‖z‖ ^ alpha := by
    calc
      ‖B z‖ ^ alpha ≤ (‖B.toContinuousLinearMap‖ * ‖z‖) ^ alpha :=
        Real.rpow_le_rpow (norm_nonneg _) (B.toContinuousLinearMap.le_opNorm z) ha.le
      _ = ‖B.toContinuousLinearMap‖ ^ alpha * ‖z‖ ^ alpha := by
        rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  have hkernel_cont : Continuous
      (fun z : E3 => MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t z) := by
    unfold MorganTianLib.ParabolicPDE.euclideanHeatKernel
    exact (contDiff_prod (fun i _ =>
      (MorganTianLib.ParabolicPDE.gaussianHeatKernel_derivatives ht).1.comp
        (by fun_prop))).continuous
  have hweight_cont : Continuous (fun z : E3 => ‖B z‖ ^ alpha) := by
    exact (continuous_norm.comp B.toContinuousLinearMap.continuous).rpow_const
      (fun _ => Or.inr ha.le)
  have hg_cont : Continuous g := by
    dsimp [g]
    exact hkernel_cont.mul hweight_cont
  have hdomInt : Integrable
      (fun z : E3 => ‖B.toContinuousLinearMap‖ ^ alpha *
        (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t z * ‖z‖ ^ alpha))
      volume := hfrac.1.const_mul _
  have hgInt : Integrable g volume := by
    refine hdomInt.mono' hg_cont.measurable.aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · dsimp [g]
      calc
        MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t z * ‖B z‖ ^ alpha ≤
            MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t z *
              (‖B.toContinuousLinearMap‖ ^ alpha * ‖z‖ ^ alpha) :=
          mul_le_mul_of_nonneg_left (hweight z)
            (MorganTianLib.ParabolicPDE.euclideanHeatKernel_pos 3 ht z).le
        _ = ‖B.toContinuousLinearMap‖ ^ alpha *
            (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t z * ‖z‖ ^ alpha) := by
          ring
    exact mul_nonneg
      (MorganTianLib.ParabolicPDE.euclideanHeatKernel_pos 3 ht z).le
      (Real.rpow_nonneg (norm_nonneg _) _)
  have hchangeInt :=
    MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      volume MeasurableSet.univ hf' hf g
  have hgImage : IntegrableOn g (f '' (Set.univ : Set E3)) volume := by
    simpa [f, Set.image_univ_of_surjective B.symm.surjective] using hgInt
  have hscaledOn : IntegrableOn
      (fun y : E3 => |L.det| • g (f y)) (Set.univ : Set E3) volume :=
    hchangeInt.mp hgImage
  have hscaled : Integrable
      (fun y : E3 => |L.det| • g (f y)) volume :=
    integrableOn_univ.mp hscaledOn
  have hfun : (fun y : E3 => anisotropicHeatKernel B t y * ‖y‖ ^ alpha) =
      (fun y : E3 => |L.det| • g (f y)) := by
    funext y
    change |LinearMap.det B.toLinearEquiv.toLinearMap|⁻¹ *
        MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t (B.symm y) * ‖y‖ ^ alpha =
      |L.det| *
        (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t (B.symm y) *
          ‖B (B.symm y)‖ ^ alpha)
    rw [ContinuousLinearMap.det, hcoeff]
    simp
    ring
  have htargetInt : Integrable
      (fun y : E3 => anisotropicHeatKernel B t y * ‖y‖ ^ alpha) volume := by
    rw [hfun]
    exact hscaled
  have hchangeMass :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      volume MeasurableSet.univ hf' hf g
  have hchangeIntegral :
      (∫ y : E3, anisotropicHeatKernel B t y * ‖y‖ ^ alpha) =
        ∫ z : E3, g z := by
    rw [hfun]
    calc
      (∫ y : E3, |L.det| • g (f y)) =
          ∫ y in (Set.univ : Set E3), |L.det| • g (f y) := by simp
      _ =
          ∫ z in f '' (Set.univ : Set E3), g z := hchangeMass.symm
      _ = ∫ z : E3, g z := by
          simp [f, Set.image_univ_of_surjective B.symm.surjective]
  have hpoint (z : E3) : g z ≤
      ‖B.toContinuousLinearMap‖ ^ alpha *
        (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t z * ‖z‖ ^ alpha) := by
    dsimp [g]
    calc
      MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t z * ‖B z‖ ^ alpha ≤
          MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t z *
            (‖B.toContinuousLinearMap‖ ^ alpha * ‖z‖ ^ alpha) :=
        mul_le_mul_of_nonneg_left (hweight z)
          (MorganTianLib.ParabolicPDE.euclideanHeatKernel_pos 3 ht z).le
      _ = ‖B.toContinuousLinearMap‖ ^ alpha *
          (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t z * ‖z‖ ^ alpha) := by
        ring
  have hbound : (∫ z : E3, g z) ≤
      ‖B.toContinuousLinearMap‖ ^ alpha *
        (∫ z : E3, MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t z *
          ‖z‖ ^ alpha) := by
    calc
      (∫ z : E3, g z) ≤
          ∫ z : E3, ‖B.toContinuousLinearMap‖ ^ alpha *
            (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t z * ‖z‖ ^ alpha) :=
        integral_mono hgInt hdomInt hpoint
      _ = ‖B.toContinuousLinearMap‖ ^ alpha *
          (∫ z : E3, MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t z *
            ‖z‖ ^ alpha) := by rw [integral_const_mul]
  refine ⟨htargetInt, ?_⟩
  rw [hchangeIntegral]
  calc
    (∫ z : E3, g z) ≤
        ‖B.toContinuousLinearMap‖ ^ alpha *
          (∫ z : E3, MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t z *
            ‖z‖ ^ alpha) := hbound
    _ ≤ ‖B.toContinuousLinearMap‖ ^ alpha *
        (C * t ^ (alpha / 2)) :=
      mul_le_mul_of_nonneg_left hfrac.2 (Real.rpow_nonneg (norm_nonneg _) _)
    _ = C * ‖B.toContinuousLinearMap‖ ^ alpha * t ^ (alpha / 2) := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
