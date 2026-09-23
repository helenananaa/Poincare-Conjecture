import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.AnisotropicHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HessianCancellationThree
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** anisotropic hessian cancellation. -/
theorem anisotropic_hessian_cancellation 
    (B : E3 ≃L[ℝ] E3) (t : ℝ) (ht : 0 < t) (i j : Fin 3) :
    let H := fun y : E3 => fderiv ℝ (fun z : E3 => fderiv ℝ (anisotropicHeatKernel B t) z
      (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1);
    Integrable H volume ∧ (∫ y : E3, H y) = 0 :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let K : E3 → ℝ := MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t
  let H : E3 → ℝ := fun y =>
    fderiv ℝ (fun z : E3 => fderiv ℝ (anisotropicHeatKernel B t) z
      (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)
  change Integrable H volume ∧ (∫ y : E3, H y) = 0
  let U : E3 := B.symm (EuclideanSpace.single i 1)
  let V : E3 := B.symm (EuclideanSpace.single j 1)
  let e : Fin 3 → E3 := fun k => EuclideanSpace.single k 1
  let C : Fin 3 → Fin 3 → E3 → ℝ := fun a b y =>
    fderiv ℝ (fun z : E3 => fderiv ℝ K z (e a)) y (e b)
  let G : E3 → ℝ := fun y =>
    fderiv ℝ (fun z : E3 => fderiv ℝ K z U) y V
  have hK : ContDiff ℝ ∞ K := by
    dsimp [K]
    exact (MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_heat_equation ht).1
  have hcomp (a b : Fin 3) :=
    MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_hessian_cancellation ht a b
  have hU : U = ∑ a : Fin 3, U a • e a := by
    simpa [U, e, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr
        (B.symm (EuclideanSpace.single i 1))).symm
  have hV : V = ∑ b : Fin 3, V b • e b := by
    simpa [V, e, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr
        (B.symm (EuclideanSpace.single j 1))).symm
  have hEval (y u v : E3) :
      fderiv ℝ (fun z : E3 => fderiv ℝ K z u) y v =
        (fderiv ℝ (fderiv ℝ K) y) v u := by
    have hK2 : ContDiffAt ℝ 2 K y := by
      intro n hn
      exact hK.contDiffAt (x := y) n (by simp)
    have hdiff : DifferentiableAt ℝ (fderiv ℝ K) y :=
      (hK2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have h := fderiv_clm_apply hdiff (differentiableAt_const (c := u) (x := y))
    have h' := congrArg (fun L : E3 →L[ℝ] ℝ => L v) h
    simpa using h'
  have hGexpand (y : E3) :
      G y = ∑ a : Fin 3, ∑ b : Fin 3,
        (U a * V b) * C a b y := by
    let T : E3 →L[ℝ] E3 →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ K) y
    have hVa (a : Fin 3) :
        T V (e a) = ∑ b : Fin 3, V b * T (e b) (e a) := by
      calc
        T V (e a) = T (∑ b : Fin 3, V b • e b) (e a) := by
          exact congrArg (fun w : E3 => T w (e a)) hV
        _ = (∑ b : Fin 3, V b • T (e b)) (e a) := by
          simp only [map_sum, map_smul]
        _ = ∑ b : Fin 3, V b * T (e b) (e a) := by
          rw [ContinuousLinearMap.sum_apply]
          simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hUa : T V U = T V (∑ a : Fin 3, U a • e a) := by
      exact congrArg (fun w : E3 => T V w) hU
    calc
      G y = T V U := hEval y U V
      _ = T V (∑ a : Fin 3, U a • e a) := by
        exact hUa
      _ = ∑ a : Fin 3, U a * T V (e a) := by
        simp only [map_sum, map_smul, smul_eq_mul]
      _ = ∑ a : Fin 3, U a * ∑ b : Fin 3, V b * C a b y := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hVa a]
        congr 1
        apply Finset.sum_congr rfl
        intro b hb
        apply congrArg (fun z : ℝ => V b * z)
        exact (hEval y (e a) (e b)).symm
      _ = ∑ a : Fin 3, ∑ b : Fin 3, (U a * V b) * C a b y := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        ring
  have hGint : Integrable G volume := by
    rw [show G = (fun y : E3 =>
        ∑ a : Fin 3, ∑ b : Fin 3, (U a * V b) * C a b y) by
      funext y
      exact hGexpand y]
    apply integrable_finsetSum (Finset.univ : Finset (Fin 3))
    intro a ha
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (by
      intro b hb
      exact (hcomp a b).1.const_mul (U a * V b))
  have hCmass (a b : Fin 3) : (∫ y : E3, C a b y) = 0 := by
    simpa [C, K] using (hcomp a b).2
  have hGmass : (∫ y : E3, G y) = 0 := by
    rw [show G = (fun y : E3 =>
        ∑ a : Fin 3, ∑ b : Fin 3, (U a * V b) * C a b y) by
      funext y
      exact hGexpand y]
    rw [integral_finsetSum (Finset.univ : Finset (Fin 3)) (by
      intro a ha
      exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (by
        intro b hb
        exact (hcomp a b).1.const_mul (U a * V b)))]
    apply Finset.sum_eq_zero
    intro a ha
    rw [integral_finsetSum (Finset.univ : Finset (Fin 3)) (by
      intro b hb
      exact (hcomp a b).1.const_mul (U a * V b))]
    simp_rw [integral_const_mul]
    simp [hCmass]
  have hdet : LinearMap.det B.toLinearEquiv.toLinearMap ≠ 0 :=
    (LinearEquiv.isUnit_det' B.toLinearEquiv).ne_zero
  have hdet_symm :
      LinearMap.det (B.symm.toContinuousLinearMap.toLinearMap) =
        (LinearMap.det B.toLinearEquiv.toLinearMap)⁻¹ := by
    simpa using LinearEquiv.det_coe_symm B.toLinearEquiv
  let f : E3 → E3 := fun x => B.symm x
  let L : E3 →L[ℝ] E3 := B.symm.toContinuousLinearMap
  have hcoeff : |L.det| = |LinearMap.det B.toLinearEquiv.toLinearMap|⁻¹ := by
    rw [ContinuousLinearMap.det, hdet_symm, abs_inv]
  have hf' : ∀ x ∈ (Set.univ : Set E3),
      HasFDerivWithinAt f L Set.univ x := by
    intro x hx
    simpa [f, L] using
      (ContinuousLinearMap.hasFDerivAt L (x := x)).hasFDerivWithinAt (s := Set.univ)
  have hf : Set.InjOn f (Set.univ : Set E3) := by
    intro x hx y hy hxy
    exact B.symm.injective hxy
  have hfun (x : E3) : H x = |L.det| • G (f x) := by
    dsimp [H, G, U, V, f]
    rw [anisotropic_hessian_formula B t ht x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1)]
    change |LinearMap.det B.toLinearEquiv.toLinearMap|⁻¹ *
        fderiv ℝ (fun z : E3 => fderiv ℝ K z (B.symm (EuclideanSpace.single i 1)))
          (B.symm x) (B.symm (EuclideanSpace.single j 1)) =
      |L.det| *
        fderiv ℝ (fun z : E3 => fderiv ℝ K z (B.symm (EuclideanSpace.single i 1)))
          (B.symm x) (B.symm (EuclideanSpace.single j 1))
    rw [← hcoeff]
  have hchangeInt :=
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      volume MeasurableSet.univ hf' hf G
  have hGImage : IntegrableOn G (f '' (Set.univ : Set E3)) volume := by
    simpa [f, Set.image_univ_of_surjective B.symm.surjective] using hGint
  have hscaledOn : IntegrableOn
      (fun x : E3 => |L.det| • G (f x)) Set.univ volume := hchangeInt.mp hGImage
  have hscaled : Integrable (fun x : E3 => |L.det| • G (f x)) volume :=
    integrableOn_univ.mp hscaledOn
  have hchangeMass :=
    integral_image_eq_integral_abs_det_fderiv_smul
      volume MeasurableSet.univ hf' hf G
  refine ⟨?_, ?_⟩
  · have hHeq : H = (fun x : E3 => |L.det| • G (f x)) := by
      funext x
      exact hfun x
    rw [hHeq]
    exact hscaled
  · calc
      (∫ x : E3, H x) = ∫ x : E3, |L.det| • G (f x) := by
        congr 1
        funext x
        exact hfun x
      _ = ∫ x in Set.univ, |L.det| • G (f x) := by simp
      _ = ∫ x in f '' (Set.univ : Set E3), G x := hchangeMass.symm
      _ = ∫ x : E3, G x := by
        simpa [f, Set.image_univ_of_surjective B.symm.surjective]
      _ = 0 := hGmass
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
