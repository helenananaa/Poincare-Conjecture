import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.AnisotropicConvolutionPullback
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.AnisotropicDuhamelIdentity
open MorganTianLib.MetricCoefficient Set MeasureTheory
open scoped Topology BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** The actual anisotropic Duhamel integral is a linear pullback of the isotropic one. -/
theorem anisotropic_duhamel_eq_pullback
    (B : E3 ≃L[ℝ] E3) (F : (ℝ × E3) →ᵇ ℝ)
    (T : ℝ) (hT : 0 ≤ T) (x : E3) :
    (∫ s in (0:ℝ)..T, ∫ y : E3,
      anisotropicHeatKernel B (T-s) (x-y) * F (s,y)) =
    (∫ s in (0:ℝ)..T, ∫ z : E3,
      MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (T-s) (B.symm x-z) * F (s,B z)) :=
/- SWARM_PROOF_BEGIN -/
by
  by_cases hzero : T = 0
  · subst T
    simp
  ·
    have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hzero)
    let slice (s : ℝ) : E3 →ᵇ ℝ :=
      BoundedContinuousFunction.mk
        (ContinuousMap.mk (fun y : E3 => F (s, y)) (by fun_prop))
        ⟨2 * ‖F‖, by
          intro y z
          calc
            dist (F (s, y)) (F (s, z)) ≤ ‖F (s, y)‖ + ‖F (s, z)‖ :=
              dist_le_norm_add_norm _ _
            _ ≤ ‖F‖ + ‖F‖ :=
              add_le_add (BoundedContinuousFunction.norm_coe_le_norm F (s, y))
                (BoundedContinuousFunction.norm_coe_le_norm F (s, z))
            _ = 2 * ‖F‖ := by ring⟩
    let leftSlice (s : ℝ) : ℝ :=
      ∫ y : E3, anisotropicHeatKernel B (T - s) (x - y) * F (s, y)
    let rightSlice (s : ℝ) : ℝ :=
      ∫ z : E3,
        MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (T - s) (B.symm x - z) *
          F (s, B z)
    have hneq : ∀ᵐ s : ℝ ∂(volume : Measure ℝ), s ≠ T := by
      rw [ae_iff]
      simp
    have hEq : ∀ᵐ s : ℝ ∂(volume : Measure ℝ),
        s ∈ Set.uIoc (0 : ℝ) T → leftSlice s = rightSlice s := by
      filter_upwards [hneq] with s hsne
      intro hsI
      have hsIoc : s ∈ Set.Ioc (0 : ℝ) T := by
        simpa [Set.uIoc_of_le hT] using hsI
      have hst : s < T := lt_of_le_of_ne hsIoc.2 hsne
      have hlag : 0 < T - s := sub_pos.mpr hst
      have hpull := anisotropic_convolution_pullback B (T - s) hlag (slice s) x
      simpa [leftSlice, rightSlice, slice] using hpull.2
    have hOuter :
        (∫ s in (0 : ℝ)..T, leftSlice s) = (∫ s in (0 : ℝ)..T, rightSlice s) :=
      intervalIntegral.integral_congr_ae hEq
    simpa [leftSlice, rightSlice] using hOuter
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.AnisotropicDuhamelIdentity
