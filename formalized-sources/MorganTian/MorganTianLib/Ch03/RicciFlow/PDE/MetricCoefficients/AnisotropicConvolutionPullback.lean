import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.AnisotropicHeatKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** anisotropic convolution pullback. -/
theorem anisotropic_convolution_pullback 
    (B : E3 ≃L[ℝ] E3) (t : ℝ) (ht : 0 < t) (f : E3 →ᵇ ℝ) (x : E3) :
    Integrable (fun y : E3 => anisotropicHeatKernel B t (x-y)*f y) volume ∧
      (∫ y : E3, anisotropicHeatKernel B t (x-y)*f y) =
        ∫ z : E3, MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t (B.symm x-z)*f (B z) :=
/- SWARM_PROOF_BEGIN -/
by
  let L : E3 →L[ℝ] E3 := B.toContinuousLinearMap
  let g : E3 → ℝ := fun y => anisotropicHeatKernel B t (x - y) * f y
  let q : E3 → ℝ := fun z =>
    MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t (B.symm x - z) * f (B z)
  have hK := (MorganTianLib.ParabolicPDE.euclideanHeatKernel_mass_semigroup 3).1 t ht
  have hKshift : Integrable
      (fun z : E3 => MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t (B.symm x - z))
      volume := by
    have hcomp : Integrable
        (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t ∘ fun z : E3 => B.symm x - z)
        volume :=
      ((volume.measurePreserving_sub_left (B.symm x)).integrable_comp
        hK.1.aestronglyMeasurable).2 hK.1
    exact hcomp.congr (Filter.Eventually.of_forall fun z => rfl)
  have hsource : Integrable q volume := by
    apply hKshift.mul_bdd
    · exact (f.continuous.comp B.continuous).aestronglyMeasurable
    · filter_upwards [] with z
      exact f.norm_coe_le_norm (B z)
  have hdet : LinearMap.det B.toLinearEquiv.toLinearMap ≠ 0 :=
    (LinearEquiv.isUnit_det' B.toLinearEquiv).ne_zero
  have hcoeff : |L.det| = |LinearMap.det B.toLinearEquiv.toLinearMap| := by
    rfl
  have hmap (z : E3) : B.symm (x - B z) = B.symm x - z := by
    rw [map_sub, B.symm_apply_apply]
  have hpoint : ∀ z : E3, |L.det| • g (B z) = q z := by
    intro z
    simp only [g, q, anisotropicHeatKernel, smul_eq_mul]
    rw [hcoeff, hmap]
    have habs : |LinearMap.det B.toLinearEquiv.toLinearMap| ≠ 0 :=
      abs_ne_zero.mpr hdet
    field_simp [habs]
  have hscaled : Integrable (fun z : E3 => |L.det| • g (B z)) volume := by
    rw [show (fun z : E3 => |L.det| • g (B z)) = q from funext hpoint]
    exact hsource
  have hf' : ∀ z ∈ (Set.univ : Set E3),
      HasFDerivWithinAt (fun z : E3 => B z) L Set.univ z := by
    intro z hz
    simpa [L] using
      (ContinuousLinearMap.hasFDerivAt L (x := z)).hasFDerivWithinAt
        (s := (Set.univ : Set E3))
  have hf : Set.InjOn (fun z : E3 => B z) (Set.univ : Set E3) := by
    intro z hz w hw hzw
    exact B.injective hzw
  have hchangeInt :=
    MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      volume MeasurableSet.univ hf' hf g
  have hgOn : IntegrableOn g (Set.univ : Set E3) volume := by
    have himage := hchangeInt.mpr (integrableOn_univ.mpr hscaled)
    simpa [Set.image_univ_of_surjective B.surjective] using himage
  have hg : Integrable g volume := integrableOn_univ.mp hgOn
  have hchangeIntg :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      volume MeasurableSet.univ hf' hf g
  have hintegral : (∫ y : E3, g y) = ∫ z : E3, q z := by
    calc
      (∫ y : E3, g y) = ∫ y in B '' (Set.univ : Set E3), g y := by
        simp [Set.image_univ_of_surjective B.surjective]
      _ = ∫ z in (Set.univ : Set E3), |L.det| • g (B z) := hchangeIntg
      _ = ∫ z : E3, q z := by
        rw [show (fun z : E3 => |L.det| • g (B z)) = q from funext hpoint]
        simp
  exact ⟨hg, hintegral⟩
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
