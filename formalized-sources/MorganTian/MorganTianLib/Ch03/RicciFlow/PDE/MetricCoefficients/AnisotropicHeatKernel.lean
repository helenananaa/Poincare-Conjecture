import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local notation "J3" => (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)
local notation "JBg" => J3 × (T3 × (Fin 3 → T3))
local notation "E9" => EuclideanSpace ℝ (Fin 3 × Fin 3)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
def anisotropicHeatKernel (B : E3 ≃L[ℝ] E3) (t : ℝ) (x : E3) : ℝ :=
  |LinearMap.det B.toLinearEquiv.toLinearMap|⁻¹ *
    MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t (B.symm x)

/-- **Math.** anisotropic heat kernel mass. -/
theorem anisotropic_heat_kernel_mass (B : E3 ≃L[ℝ] E3) (t : ℝ) (ht : 0 < t) :
    Integrable (anisotropicHeatKernel B t) volume ∧
      (∫ x : E3, anisotropicHeatKernel B t x) = 1 ∧ ∀ x : E3, 0 ≤ anisotropicHeatKernel B t x :=
/- SWARM_PROOF_BEGIN -/
by
  have hK := (MorganTianLib.ParabolicPDE.euclideanHeatKernel_mass_semigroup 3).1 t ht
  have hdet : LinearMap.det B.toLinearEquiv.toLinearMap ≠ 0 :=
    (LinearEquiv.isUnit_det' B.toLinearEquiv).ne_zero
  have hdet_symm :
      LinearMap.det (B.symm.toContinuousLinearMap.toLinearMap) =
        (LinearMap.det B.toLinearEquiv.toLinearMap)⁻¹ := by
    simpa using LinearEquiv.det_coe_symm B.toLinearEquiv
  have hcoeff : |B.symm.toContinuousLinearMap.det| =
      |LinearMap.det B.toLinearEquiv.toLinearMap|⁻¹ := by
    rw [ContinuousLinearMap.det, hdet_symm, abs_inv]
  have hcoeff_pos : 0 < |LinearMap.det B.toLinearEquiv.toLinearMap|⁻¹ :=
    inv_pos.mpr (abs_pos.mpr hdet)
  let f : E3 → E3 := fun x => B.symm x
  let L : E3 →L[ℝ] E3 := B.symm.toContinuousLinearMap
  have hf' : ∀ x ∈ (Set.univ : Set E3),
      HasFDerivWithinAt f L Set.univ x := by
    intro x hx
    simpa [f, L] using
      (ContinuousLinearMap.hasFDerivAt L (x := x)).hasFDerivWithinAt (s := Set.univ)
  have hf : Set.InjOn f (Set.univ : Set E3) := by
    intro x hx y hy hxy
    exact B.symm.injective hxy
  have hchangeInt :=
    MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      volume MeasurableSet.univ hf' hf (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t)
  have hKImage : IntegrableOn (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t)
      (f '' (Set.univ : Set E3)) volume := by
    simpa [f, Set.image_univ_of_surjective B.symm.surjective] using hK.1
  have hscaledOn : IntegrableOn
      (fun x : E3 => |L.det| • MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t (f x))
      Set.univ volume := hchangeInt.mp hKImage
  have hscaled : Integrable
      (fun x : E3 => |L.det| • MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t (f x))
      volume := integrableOn_univ.mp hscaledOn
  have hfun : anisotropicHeatKernel B t =
      (fun x : E3 => |L.det| • MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t (f x)) := by
    funext x
    change |LinearMap.det B.toLinearEquiv.toLinearMap|⁻¹ *
        MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t (B.symm x) =
      |B.symm.toContinuousLinearMap.det| *
        MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t (B.symm x)
    rw [← hcoeff]
  have hanisInt : Integrable (anisotropicHeatKernel B t) volume := by
    rw [hfun]
    exact hscaled
  have hchangeMass :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      volume MeasurableSet.univ hf' hf (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t)
  have hanisMass : (∫ x : E3, anisotropicHeatKernel B t x) = 1 := by
    calc
      (∫ x : E3, anisotropicHeatKernel B t x) =
          ∫ x in Set.univ, |L.det| •
            MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t (f x) := by
          rw [hfun]
          simp
      _ = ∫ x in f '' (Set.univ : Set E3),
            MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t x := hchangeMass.symm
      _ = 1 := by
          simpa [f, Set.image_univ_of_surjective B.symm.surjective] using hK.2
  refine ⟨hanisInt, hanisMass, ?_⟩
  intro x
  rw [anisotropicHeatKernel]
  exact mul_nonneg (le_of_lt hcoeff_pos)
    (le_of_lt (MorganTianLib.ParabolicPDE.euclideanHeatKernel_pos 3 ht (B.symm x)))
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
