import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.AnisotropicHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.AnisotropicHessianCancellation
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BoundedLinearPullback
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideBoundedHessianIdentification
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** anisotropic hessian identification. -/
theorem anisotropic_hessian_identification 
    (B : E3 ≃L[ℝ] E3) (t : ℝ) (ht : 0 < t) (f : E3 →ᵇ ℝ) :
    let u : E3 → ℝ := fun x => ∫ y : E3, anisotropicHeatKernel B t y*f (x-y);
    ContDiff ℝ 2 u ∧ ∀ (x : E3) (i j : Fin 3),
      fderiv ℝ (fun z : E3 => fderiv ℝ u z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1) = ∫ y : E3,
          fderiv ℝ (fun z : E3 => fderiv ℝ (anisotropicHeatKernel B t) z
            (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)*f (x-y) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let u : E3 → ℝ := fun x => ∫ y : E3, anisotropicHeatKernel B t y * f (x-y)
  change ContDiff ℝ 2 u ∧ ∀ (x : E3) (i j : Fin 3),
    fderiv ℝ (fun z : E3 => fderiv ℝ u z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single j 1) = ∫ y : E3,
        fderiv ℝ (fun z : E3 => fderiv ℝ (anisotropicHeatKernel B t) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) * f (x-y)
  obtain ⟨P, hP, _, _⟩ := bounded_linear_pullback B
  let g : E3 →ᵇ ℝ := P f
  have hg (y : E3) : g y = f (B y) := hP f y
  let K : E3 → ℝ := MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t
  let v : E3 → ℝ := fun w => ∫ z : E3, K (w-z) * g z
  have hv : ContDiff ℝ 2 v ∧ ∀ (w : E3) (a b : Fin 3),
      fderiv ℝ (fun z : E3 => fderiv ℝ v z (EuclideanSpace.single a 1)) w
        (EuclideanSpace.single b 1) = ∫ z : E3,
          fderiv ℝ (fun q : E3 => fderiv ℝ K q (EuclideanSpace.single a 1)) z
            (EuclideanSpace.single b 1) * g (w-z) := by
    simpa [v, K] using
      (MorganTianLib.ParabolicPDE.euclideanHeatKernel_bounded_hessian_identification g ht)
  let T : E3 → E3 := fun x => B.symm x
  let L : E3 →L[ℝ] E3 := B.symm.toContinuousLinearMap
  let c : ℝ := |LinearMap.det B.toLinearEquiv.toLinearMap|⁻¹
  have hdet : LinearMap.det B.toLinearEquiv.toLinearMap ≠ 0 :=
    (LinearEquiv.isUnit_det' B.toLinearEquiv).ne_zero
  have hdet_symm :
      LinearMap.det (B.symm.toContinuousLinearMap.toLinearMap) =
        (LinearMap.det B.toLinearEquiv.toLinearMap)⁻¹ := by
    simpa using LinearEquiv.det_coe_symm B.toLinearEquiv
  have hcoeff : |L.det| = c := by
    rw [ContinuousLinearMap.det, hdet_symm, abs_inv]
  have hT' : ∀ x ∈ (Set.univ : Set E3),
      HasFDerivWithinAt T L Set.univ x := by
    intro x hx
    simpa [T, L] using
      (ContinuousLinearMap.hasFDerivAt L (x := x)).hasFDerivWithinAt (s := Set.univ)
  have hT : Set.InjOn T (Set.univ : Set E3) := by
    intro x hx y hy hxy
    exact B.symm.injective hxy
  have hImage : T '' (Set.univ : Set E3) = Set.univ := by
    simpa [T] using (Set.image_univ_of_surjective B.symm.surjective)
  have hchange (G : E3 → ℝ) :
      (∫ z : E3, G z) = ∫ y : E3, |L.det| • G (T y) := by
    have h := integral_image_eq_integral_abs_det_fderiv_smul
      volume MeasurableSet.univ hT' hT G
    calc
      (∫ z : E3, G z) = ∫ z in T '' (Set.univ : Set E3), G z := by
        rw [hImage]
        simp
      _ = ∫ y in (Set.univ : Set E3), |L.det| • G (T y) := h
      _ = ∫ y : E3, |L.det| • G (T y) := by simp
  have hconv (x : E3) : u x = v (T x) := by
    let G : E3 → ℝ := fun z => K z * f (x - B z)
    have htarget : u x = ∫ z : E3, G z := by
      calc
        u x = ∫ y : E3, |L.det| • G (T y) := by
          change (∫ y : E3, anisotropicHeatKernel B t y * f (x-y)) = _
          congr 1
          funext y
          rw [anisotropicHeatKernel]
          rw [hcoeff]
          simp only [G, T, B.apply_symm_apply, smul_eq_mul, c]
          ring
        _ = ∫ z : E3, G z := (hchange G).symm
    have htrans :
        (∫ z : E3, K (T x-z) * g z) = ∫ z : E3, K z * g (T x-z) := by
      rw [← integral_sub_left_eq_self
        (fun z : E3 => K z * g (T x-z)) volume (T x)]
      congr 1
      funext z
      congr 2
      abel
    calc
      u x = ∫ z : E3, G z := htarget
      _ = ∫ z : E3, K z * g (T x-z) := by
        congr 1
        funext z
        change K z * f (x - B z) = K z * g (T x-z)
        rw [hg (T x-z)]
        congr 1
        simp [T]
      _ = ∫ z : E3, K (T x-z) * g z := htrans.symm
      _ = v (T x) := rfl
  have huFun : u = fun x : E3 => v (T x) := by
    funext x
    exact hconv x
  have huC2 : ContDiff ℝ 2 u := by
    rw [huFun]
    exact hv.1.comp (by fun_prop)
  let e : Fin 3 → E3 := fun k => EuclideanSpace.single k 1
  have hK : ContDiff ℝ ∞ K := by
    dsimp [K]
    exact (MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_heat_equation ht).1
  have hessExpand (F : E3 → ℝ) (hF : ContDiff ℝ 2 F)
      (w U V : E3) :
      fderiv ℝ (fun z : E3 => fderiv ℝ F z U) w V =
        ∑ a : Fin 3, ∑ b : Fin 3,
          (U a * V b) *
            fderiv ℝ (fun z : E3 => fderiv ℝ F z (e a)) w (e b) := by
    let Q : E3 →L[ℝ] E3 →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ F) w
    have hU : U = ∑ a : Fin 3, U a • e a := by
      simpa [e, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
        ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr U).symm
    have hV : V = ∑ b : Fin 3, V b • e b := by
      simpa [e, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
        ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr V).symm
    have hEval (y p q : E3) :
        fderiv ℝ (fun z : E3 => fderiv ℝ F z p) y q =
          (fderiv ℝ (fderiv ℝ F) y) q p := by
      have hF2 : ContDiffAt ℝ 2 F y := hF.contDiffAt
      have hdiff : DifferentiableAt ℝ (fderiv ℝ F) y :=
        (hF2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
      have h := fderiv_clm_apply hdiff
        (differentiableAt_const (c := p) (x := y))
      have h' := congrArg
        (fun M : E3 →L[ℝ] ℝ => M q) h
      simpa using h'
    have hVa (a : Fin 3) : Q V (e a) =
        ∑ b : Fin 3, V b * Q (e b) (e a) := by
      calc
        Q V (e a) = Q (∑ b : Fin 3, V b • e b) (e a) := by
          exact congrArg (fun Z : E3 => Q Z (e a)) hV
        _ = (∑ b : Fin 3, V b • Q (e b)) (e a) := by
          simp only [map_sum, map_smul]
        _ = ∑ b : Fin 3, V b * Q (e b) (e a) := by
          rw [ContinuousLinearMap.sum_apply]
          simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hUa : Q V U = Q V (∑ a : Fin 3, U a • e a) :=
      congrArg (fun Z : E3 => Q V Z) hU
    calc
      fderiv ℝ (fun z : E3 => fderiv ℝ F z U) w V = Q V U := hEval w U V
      _ = Q V (∑ a : Fin 3, U a • e a) := hUa
      _ = ∑ a : Fin 3, U a * Q V (e a) := by
        simp only [map_sum, map_smul, smul_eq_mul]
      _ = ∑ a : Fin 3, U a * ∑ b : Fin 3, V b * Q (e b) (e a) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hVa a]
      _ = ∑ a : Fin 3, ∑ b : Fin 3, (U a * V b) *
          fderiv ℝ (fun z : E3 => fderiv ℝ F z (e a)) w (e b) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [← hEval w (e a) (e b)]
        ring
  have hBasisInt (a b : Fin 3) : Integrable
      (fun y : E3 => fderiv ℝ (fun z : E3 => fderiv ℝ K z (e a)) y (e b)) volume := by
    simpa [K, e] using
      (MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_hessian_cancellation ht a b).1
  have hIso (w U V : E3) :
      fderiv ℝ (fun z : E3 => fderiv ℝ v z U) w V =
        ∫ y : E3, fderiv ℝ (fun z : E3 => fderiv ℝ K z U) y V * g (w-y) := by
    let C : Fin 3 → Fin 3 → E3 → ℝ := fun a b y =>
      fderiv ℝ (fun z : E3 => fderiv ℝ K z (e a)) y (e b)
    have hcomponent (a b : Fin 3) :
        fderiv ℝ (fun z : E3 => fderiv ℝ v z (e a)) w (e b) =
          ∫ y : E3, C a b y * g (w-y) := by
      simpa [v, K, C, e] using hv.2 w a b
    have htermInt (a b : Fin 3) :
        Integrable (fun y : E3 => C a b y * g (w-y)) volume := by
      apply (hBasisInt a b).mul_bdd
      · exact (g.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      · filter_upwards [] with y
        exact g.norm_coe_le_norm (w-y)
    have hsumInt :
        (∫ y : E3, (∑ a : Fin 3, ∑ b : Fin 3,
            (U a * V b) * C a b y) * g (w-y)) =
          ∑ a : Fin 3, ∑ b : Fin 3,
            (U a * V b) * ∫ y : E3, C a b y * g (w-y) := by
      have hinner (a : Fin 3) : Integrable
          (fun y : E3 => ∑ b : Fin 3,
            (U a * V b) * (C a b y * g (w-y))) volume := by
        apply integrable_finsetSum (Finset.univ : Finset (Fin 3))
        intro b hb
        exact (htermInt a b).const_mul (U a * V b)
      have hpoint :
          (fun y : E3 => (∑ a : Fin 3, ∑ b : Fin 3,
              (U a * V b) * C a b y) * g (w-y)) =
            (fun y : E3 => ∑ a : Fin 3, ∑ b : Fin 3,
              (U a * V b) * (C a b y * g (w-y))) := by
        funext y
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        ring
      rw [hpoint]
      rw [integral_finsetSum (Finset.univ : Finset (Fin 3)) (by
        intro a ha
        exact hinner a)]
      apply Finset.sum_congr rfl
      intro a ha
      rw [integral_finsetSum (Finset.univ : Finset (Fin 3)) (by
        intro b hb
        exact (htermInt a b).const_mul (U a * V b))]
      simp_rw [integral_const_mul]
    calc
      fderiv ℝ (fun z : E3 => fderiv ℝ v z U) w V =
          ∑ a : Fin 3, ∑ b : Fin 3, (U a * V b) *
            fderiv ℝ (fun z : E3 => fderiv ℝ v z (e a)) w (e b) :=
        hessExpand v hv.1 w U V
      _ = ∑ a : Fin 3, ∑ b : Fin 3,
            (U a * V b) * ∫ y : E3, C a b y * g (w-y) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        exact congrArg (fun r : ℝ => (U a * V b) * r) (hcomponent a b)
      _ = ∫ y : E3, (∑ a : Fin 3, ∑ b : Fin 3,
            (U a * V b) * C a b y) * g (w-y) := hsumInt.symm
      _ = ∫ y : E3, fderiv ℝ (fun z : E3 => fderiv ℝ K z U) y V * g (w-y) := by
        congr 1
        funext y
        rw [← hessExpand K
          (hK.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))) y U V]
  have hkernelChange (x a b : E3) :
      (∫ y : E3, fderiv ℝ (fun z : E3 => fderiv ℝ (anisotropicHeatKernel B t) z a) y b
          * f (x-y)) =
        ∫ z : E3, fderiv ℝ (fun q : E3 => fderiv ℝ K q (B.symm a)) z (B.symm b)
          * g (T x-z) := by
    let H : E3 → ℝ := fun z =>
      fderiv ℝ (fun q : E3 => fderiv ℝ K q (B.symm a)) z (B.symm b)
    let G : E3 → ℝ := fun z => H z * f (x - B z)
    calc
      (∫ y : E3, fderiv ℝ (fun z : E3 =>
          fderiv ℝ (anisotropicHeatKernel B t) z a) y b * f (x-y)) =
          ∫ y : E3, |L.det| • G (T y) := by
        congr 1
        funext y
        rw [anisotropic_hessian_formula B t ht y a b]
        rw [hcoeff]
        simp only [H, G, T, B.apply_symm_apply, smul_eq_mul]
        ring
      _ = ∫ z : E3, G z := (hchange G).symm
      _ = ∫ z : E3, H z * g (T x-z) := by
        congr 1
        funext z
        change H z * f (x - B z) = H z * g (T x-z)
        rw [hg (T x-z)]
        congr 1
        simp [T]
  refine ⟨huC2, ?_⟩
  intro x i j
  rw [huFun]
  let ei : E3 := EuclideanSpace.single i 1
  let ej : E3 := EuclideanSpace.single j 1
  let U : E3 := B.symm ei
  let V : E3 := B.symm ej
  calc
    fderiv ℝ (fun z : E3 => fderiv ℝ (fun q : E3 => v (T q)) z ei) x ej =
        fderiv ℝ (fun z : E3 => fderiv ℝ v z (B.symm ei)) (T x) (B.symm ej) := by
      exact linear_pullback_second_derivative v B.symm.toContinuousLinearMap x ei ej
        (hv.1.contDiffAt (x := T x))
    _ = ∫ y : E3, fderiv ℝ (fun z : E3 => fderiv ℝ K z U) y V * g (T x-y) := by
      simpa [U, V, T] using hIso (T x) (B.symm ei) (B.symm ej)
    _ = ∫ y : E3, fderiv ℝ (fun z : E3 =>
          fderiv ℝ (anisotropicHeatKernel B t) z ei) y ej * f (x-y) := by
      simpa [U, V, T] using (hkernelChange x ei ej).symm
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
