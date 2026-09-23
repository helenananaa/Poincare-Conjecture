import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.AnisotropicHeatKernel
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

/-- **Math.** anisotropic heat kernel semigroup. -/
theorem anisotropic_heat_kernel_semigroup (B : E3 ≃L[ℝ] E3) (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (x : E3) :
    Integrable (fun y : E3 => anisotropicHeatKernel B t (x-y)*anisotropicHeatKernel B s y) volume ∧
      (∫ y : E3, anisotropicHeatKernel B t (x-y)*anisotropicHeatKernel B s y) =
        anisotropicHeatKernel B (t+s) x :=
/- SWARM_PROOF_BEGIN -/
by
  have hK :=
    (MorganTianLib.ParabolicPDE.euclideanHeatKernel_mass_semigroup 3).2
      t s ht hs (B.symm x)
  have hdet : LinearMap.det B.toLinearEquiv.toLinearMap ≠ 0 :=
    (LinearEquiv.isUnit_det' B.toLinearEquiv).ne_zero
  have hdet_symm :
      LinearMap.det (B.symm.toContinuousLinearMap.toLinearMap) =
        (LinearMap.det B.toLinearEquiv.toLinearMap)⁻¹ := by
    simpa using LinearEquiv.det_coe_symm B.toLinearEquiv
  have hcoeff : |B.symm.toContinuousLinearMap.det| =
      |LinearMap.det B.toLinearEquiv.toLinearMap|⁻¹ := by
    rw [ContinuousLinearMap.det, hdet_symm, abs_inv]
  let c : ℝ := |LinearMap.det B.toLinearEquiv.toLinearMap|⁻¹
  let f : E3 → E3 := fun y => B.symm y
  let L : E3 →L[ℝ] E3 := B.symm.toContinuousLinearMap
  let G : E3 → ℝ := fun z =>
    MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t (B.symm x - z) *
      MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 s z
  have hf' : ∀ y ∈ (Set.univ : Set E3),
      HasFDerivWithinAt f L Set.univ y := by
    intro y hy
    simpa [f, L] using
      (ContinuousLinearMap.hasFDerivAt L (x := y)).hasFDerivWithinAt (s := Set.univ)
  have hf : Set.InjOn f (Set.univ : Set E3) := by
    intro y hy z hz hyz
    exact B.symm.injective hyz
  have hchangeInt :=
    MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      volume MeasurableSet.univ hf' hf G
  have hGImage : IntegrableOn G (f '' (Set.univ : Set E3)) volume := by
    simpa [f, Set.image_univ_of_surjective B.symm.surjective] using hK.1
  have hscaledOn : IntegrableOn
      (fun y : E3 => |L.det| • G (f y)) Set.univ volume := hchangeInt.mp hGImage
  have hscaled : Integrable
      (fun y : E3 => |L.det| • G (f y)) volume :=
    integrableOn_univ.mp hscaledOn
  have hchangeMass :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      volume MeasurableSet.univ hf' hf G
  have hfun :
      (fun y : E3 => anisotropicHeatKernel B t (x-y) *
        anisotropicHeatKernel B s y) =
      (fun y : E3 => c * (|L.det| • G (f y))) := by
    funext y
    change
      (c * MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t
          (B.symm (x-y))) *
        (c * MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 s (B.symm y)) =
      c * (|L.det| •
        (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t
            (B.symm x - f y) *
          MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 s (f y)))
    rw [map_sub, hcoeff]
    dsimp [c, f]
    ring
  have hInt : Integrable
      (fun y : E3 => anisotropicHeatKernel B t (x-y) *
        anisotropicHeatKernel B s y) volume := by
    rw [hfun]
    exact hscaled.const_mul c
  refine ⟨hInt, ?_⟩
  calc
    (∫ y : E3, anisotropicHeatKernel B t (x-y) * anisotropicHeatKernel B s y) =
        ∫ y : E3, c * (|L.det| • G (f y)) := by rw [hfun]
    _ = c * ∫ y in Set.univ, |L.det| • G (f y) := by
      rw [integral_const_mul]
      simp
    _ = c * ∫ z in f '' (Set.univ : Set E3), G z := by
      congr 1
      exact hchangeMass.symm
    _ = c * ∫ z : E3, G z := by
      simp [f, Set.image_univ_of_surjective B.symm.surjective]
    _ = c * MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (t+s) (B.symm x) := by
      rw [hK.2]
    _ = anisotropicHeatKernel B (t+s) x := by
      simp [anisotropicHeatKernel, c]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
