import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualDuhamelSpatialSchauder
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.AnisotropicConvolutionPullback
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LinearHessianHolderTransport
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LinearPullbackSecondDerivative
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** anisotropic duhamel spatial schauder. -/
theorem anisotropic_duhamel_spatial_schauder 
    (B : E3 ≃L[ℝ] E3) (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (ℝ × E3) →ᵇ ℝ) (L T : ℝ), 0 ≤ L → 0 < T →
      (∀ s ∈ Icc (0:ℝ) T, ∀ x z : E3, |F (s,x)-F (s,z)| ≤ L*‖x-z‖^alpha) →
      let u : E3 → ℝ := fun x => ∫ s in (0:ℝ)..T, ∫ y : E3,
        anisotropicHeatKernel B (T-s) (x-y)*F (s,y);
      ContDiff ℝ 2 u ∧ (∀ (x : E3) (i j : Fin 3),
        |fderiv ℝ (fun z => fderiv ℝ u z (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)| ≤ C*L*T^(alpha/2)) ∧
      ∀ (x z : E3) (i j : Fin 3),
        |fderiv ℝ (fun w => fderiv ℝ u w (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)-
         fderiv ℝ (fun w => fderiv ℝ u w (EuclideanSpace.single i 1)) z (EuclideanSpace.single j 1)| ≤ C*L*‖x-z‖^alpha :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C₀, hC₀, hiso⟩ := actual_duhamel_spatial_schauder alpha ha ha1
  let A : E3 →L[ℝ] E3 := B.toContinuousLinearMap
  let S : E3 →L[ℝ] E3 := B.symm.toContinuousLinearMap
  let Ksup : ℝ := 9 * C₀ * ‖A‖^alpha * ‖S‖^2
  let Khol : ℝ := 9 * C₀ * ‖A‖^alpha * ‖S‖^2 * ‖S‖^alpha
  let C : ℝ := 1 + Ksup + Khol
  have hKsup : 0 ≤ Ksup := by dsimp [Ksup]; positivity
  have hKhol : 0 ≤ Khol := by dsimp [Khol]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hKsupC : Ksup ≤ C := by dsimp [C]; linarith
  have hKholC : Khol ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro F L T hL hT hholder
  let L' : ℝ := L * ‖A‖^alpha
  have hL' : 0 ≤ L' := by dsimp [L']; positivity
  let Ψ : ContinuousMap (ℝ × E3) (ℝ × E3) :=
    ⟨fun p => (p.1, B p.2),
      continuous_fst.prodMk (B.continuous.comp continuous_snd)⟩
  let G : (ℝ × E3) →ᵇ ℝ := BoundedContinuousFunction.compContinuous F Ψ
  have hG (s : ℝ) (z : E3) : G (s,z) = F (s, B z) := by
    simp [G, Ψ, BoundedContinuousFunction.compContinuous_apply]
  have hdisp (x z : E3) : ‖B x - B z‖ ≤ ‖A‖ * ‖x-z‖ := by
    calc
      ‖B x - B z‖ = ‖A (x-z)‖ := by
        change ‖A x - A z‖ = ‖A (x-z)‖
        rw [← map_sub]
      _ ≤ ‖A‖ * ‖x-z‖ := A.le_opNorm (x-z)
  have hGholder : ∀ s ∈ Icc (0:ℝ) T, ∀ x z : E3,
      |G (s,x)-G (s,z)| ≤ L' * ‖x-z‖^alpha := by
    intro s hs x z
    rw [hG, hG]
    calc
      |F (s,B x)-F (s,B z)| ≤ L * ‖B x-B z‖^alpha := hholder s hs (B x) (B z)
      _ ≤ L * (‖A‖ * ‖x-z‖)^alpha := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) (hdisp x z) ha.le) hL
      _ = L' * ‖x-z‖^alpha := by
        rw [Real.mul_rpow (norm_nonneg A) (norm_nonneg (x-z))]
        dsimp [L']
        ring
  have hIso := hiso G L' T hL' hT hGholder
  let v : E3 → ℝ := fun q => ∫ s in (0:ℝ)..T, ∫ z : E3,
    MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (T-s) (q-z)*G (s,z)
  change ContDiff ℝ 2 v ∧
    (∀ (x : E3) (i j : Fin 3),
      |fderiv ℝ (fun z => fderiv ℝ v z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1)| ≤ C₀*L'*T^(alpha/2)) ∧
    ∀ (x z : E3) (i j : Fin 3),
      |fderiv ℝ (fun w => fderiv ℝ v w (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1)-
       fderiv ℝ (fun w => fderiv ℝ v w (EuclideanSpace.single i 1)) z
          (EuclideanSpace.single j 1)| ≤ C₀*L'*‖x-z‖^alpha at hIso
  have hv := hIso
  let u : E3 → ℝ := fun x => ∫ s in (0:ℝ)..T, ∫ y : E3,
    anisotropicHeatKernel B (T-s) (x-y)*F (s,y)
  have hpullInner (x : E3) (s : ℝ) (hs : s ∈ Ioc (0:ℝ) T) (hst : s < T) :
      (∫ y : E3, anisotropicHeatKernel B (T-s) (x-y)*F (s,y)) =
        ∫ z : E3, MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (T-s)
          (B.symm x-z)*G (s,z) := by
    let fs : E3 →ᵇ ℝ := F.compContinuous
      ⟨fun y : E3 => (s,y), continuous_const.prodMk continuous_id⟩
    have hp := anisotropic_convolution_pullback B (T-s) (sub_pos.mpr hst) fs x
    simpa [fs, hG, BoundedContinuousFunction.compContinuous_apply] using hp.2
  let uIsoPull : E3 → ℝ := fun x => v (S x)
  have huEq : u = uIsoPull := by
    funext x
    dsimp [u, uIsoPull, v]
    apply intervalIntegral.integral_congr_ae
    have hEq : ∀ᵐ s : ℝ, s ∈ uIoc (0:ℝ) T →
        (∫ y : E3, anisotropicHeatKernel B (T-s) (x-y)*F (s,y)) =
          ∫ z : E3, MorganTianLib.ParabolicPDE.euclideanHeatKernel 3
            (T-s) (B.symm x-z)*G (s,z) := by
      filter_upwards [volume.ae_ne T] with s hst hs
      rw [uIoc_of_le hT.le] at hs
      exact hpullInner x s hs (lt_of_le_of_ne hs.2 hst)
    exact hEq
  have huEqFun :
      (fun x : E3 => ∫ s in (0:ℝ)..T, ∫ y : E3,
        anisotropicHeatKernel B (T-s) (x-y)*F (s,y)) =
      (fun x => v (S x)) := by
    simpa [u, uIsoPull] using huEq
  have huC : ContDiff ℝ 2 u := by
    rw [huEq]
    exact hv.1.comp S.contDiff
  let e : Fin 3 → E3 := fun i => EuclideanSpace.single i (1 : ℝ)
  let K : E3 → E3 → E3 → ℝ := fun q w z => fderiv ℝ (fderiv ℝ v) q w z
  have hdecomp (w : E3) : w = ∑ i : Fin 3, w i • e i := by
    simpa [e, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w).symm
  have h_eval (q u w : E3) :
      fderiv ℝ (fun y => fderiv ℝ v y u) q w = K q w u := by
    have hvAt : ContDiffAt ℝ 2 v q := by simpa using hv.1.contDiffAt
    have hfd : ContDiffAt ℝ 1 (fderiv ℝ v) q := hvAt.fderiv_right (by norm_num)
    have hd : DifferentiableAt ℝ (fderiv ℝ v) q := hfd.differentiableAt (by norm_num)
    have h := fderiv_clm_apply hd (differentiableAt_const (c := u) (x := q))
    have h' := congrArg (fun M : E3 →L[ℝ] ℝ => M w) h
    simpa [K] using h'
  have hbilin (q w u : E3) :
      K q w u = ∑ r : Fin 3, ∑ s : Fin 3,
        w r * u s * K q (e r) (e s) := by
    calc
      K q w u = ∑ r : Fin 3, (w r) • K q (e r) u := by
        rw [hdecomp w]
        simp only [K, map_sum, map_smul]
        simp [e, Pi.single_apply]
      _ = ∑ r : Fin 3, w r * (∑ s : Fin 3, u s * K q (e r) (e s)) := by
        congr 1
        funext r
        rw [hdecomp u]
        simp only [K, map_sum, map_smul, smul_eq_mul]
        simp [e, Pi.single_apply]
      _ = ∑ r : Fin 3, ∑ s : Fin 3, w r * u s * K q (e r) (e s) := by
        simp_rw [Finset.mul_sum, mul_assoc]
  have hcoord (w : E3) (i : Fin 3) : |w i| ≤ ‖w‖ := by
    have hnorm : ‖w i‖ ≤ ‖w‖ := by
      rw [EuclideanSpace.norm_eq]
      have hnonneg : 0 ≤ ∑ r : Fin 3, ‖w.ofLp r‖ ^ 2 :=
        Finset.sum_nonneg (fun r _ => sq_nonneg _)
      apply (Real.le_sqrt (norm_nonneg _) hnonneg).2
      exact Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 3)))
        (f := fun r : Fin 3 => ‖w.ofLp r‖ ^ 2)
        (fun r _ => sq_nonneg _) (Finset.mem_univ i)
    simpa [Real.norm_eq_abs] using hnorm
  have hScoord (i r : Fin 3) : |(S (e i)) r| ≤ ‖S‖ := by
    calc
      |(S (e i)) r| ≤ ‖S (e i)‖ := hcoord _ _
      _ ≤ ‖S‖ * ‖e i‖ := S.le_opNorm _
      _ = ‖S‖ := by simp [e]
  have hcomponent (q : E3) (k l : Fin 3) :
      |K q (e l) (e k)| ≤ C₀ * L' * T^(alpha/2) := by
    rw [← h_eval q (e k) (e l)]
    exact hv.2.1 q k l
  have hterm (q : E3) (i j r s : Fin 3) :
      |(S (e j)) r * (S (e i)) s * K q (e r) (e s)| ≤
        ‖S‖^2 * (C₀ * L' * T^(alpha/2)) := by
    rw [abs_mul, abs_mul]
    calc
      |(S (e j)) r| * |(S (e i)) s| * |K q (e r) (e s)| ≤
          (‖S‖ * ‖S‖) * |K q (e r) (e s)| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (hScoord j r) (hScoord i s)
            (abs_nonneg _) (norm_nonneg _)) (abs_nonneg _)
      _ ≤ (‖S‖ * ‖S‖) * (C₀ * L' * T^(alpha/2)) :=
        mul_le_mul_of_nonneg_left (hcomponent q s r) (by positivity)
      _ = ‖S‖^2 * (C₀ * L' * T^(alpha/2)) := by rw [pow_two]
  have hbound (q : E3) (i j : Fin 3) :
      |K q (S (e j)) (S (e i))| ≤
        9 * ‖S‖^2 * (C₀ * L' * T^(alpha/2)) := by
    rw [hbilin]
    calc
      |∑ r : Fin 3, ∑ s : Fin 3,
          (S (e j)) r * (S (e i)) s * K q (e r) (e s)| ≤
        ∑ r : Fin 3, ∑ s : Fin 3,
          |(S (e j)) r * (S (e i)) s * K q (e r) (e s)| := by
          calc
            |∑ r : Fin 3, ∑ s : Fin 3, _| ≤
                ∑ r : Fin 3, |∑ s : Fin 3,
                  (S (e j)) r * (S (e i)) s * K q (e r) (e s)| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ r : Fin 3, ∑ s : Fin 3,
                |(S (e j)) r * (S (e i)) s * K q (e r) (e s)| := by
              apply Finset.sum_le_sum
              intro r _
              exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r : Fin 3, ∑ s : Fin 3,
          (‖S‖^2 * (C₀ * L' * T^(alpha/2))) := by
          apply Finset.sum_le_sum
          intro r _
          apply Finset.sum_le_sum
          intro s _
          exact hterm q i j r s
      _ = 9 * ‖S‖^2 * (C₀ * L' * T^(alpha/2)) := by simp; ring
  have hpullDeriv (x : E3) (i j : Fin 3) :
      fderiv ℝ (fun z => fderiv ℝ u z (e i)) x (e j) =
        fderiv ℝ (fun y => fderiv ℝ v y (S (e i))) (S x) (S (e j)) := by
    rw [huEq]
    have hvAt : ContDiffAt ℝ 2 v (S x) := by simpa using hv.1.contDiffAt
    exact linear_pullback_second_derivative v S x (e i) (e j) hvAt
  have hH : 0 ≤ C₀ * L' := mul_nonneg (le_of_lt hC₀) hL'
  have hholdV : ∀ x z : E3, ∀ i j : Fin 3,
      |fderiv ℝ (fun y => fderiv ℝ v y (e i)) x (e j)-
       fderiv ℝ (fun y => fderiv ℝ v y (e i)) z (e j)| ≤
        (C₀ * L') * ‖x-z‖^alpha := by
    intro x z i j
    exact hv.2.2 x z i j
  have htransport := linear_hessian_holder_transport v hv.1 S alpha
    (C₀ * L') ha hH hholdV
  refine ⟨huC, ?_, ?_⟩
  · intro x i j
    rw [hpullDeriv x i j]
    rw [h_eval (S x) (S (e i)) (S (e j))]
    calc
      |K (S x) (S (e j)) (S (e i))| ≤
          9 * ‖S‖^2 * (C₀ * L' * T^(alpha/2)) := hbound (S x) i j
      _ = Ksup * L * T^(alpha/2) := by dsimp [Ksup, L']; ring
      _ ≤ C * L * T^(alpha/2) := by
        calc
          Ksup * L * T^(alpha/2) = Ksup * (L * T^(alpha/2)) := by ring
          _ ≤ C * (L * T^(alpha/2)) :=
            mul_le_mul_of_nonneg_right hKsupC
              (mul_nonneg hL (Real.rpow_nonneg hT.le _))
          _ = C * L * T^(alpha/2) := by ring
  · intro x z i j
    have htrans := htransport x z i j
    rw [← huEqFun] at htrans
    calc
      |fderiv ℝ (fun y => fderiv ℝ (fun w =>
          ∫ s in (0:ℝ)..T, ∫ y : E3,
            anisotropicHeatKernel B (T-s) (w-y)*F (s,y)) y (e i)) x (e j)-
       fderiv ℝ (fun y => fderiv ℝ (fun w =>
          ∫ s in (0:ℝ)..T, ∫ y : E3,
            anisotropicHeatKernel B (T-s) (w-y)*F (s,y)) y (e i)) z (e j)| ≤
        (9 * (C₀ * L') * ‖S‖^2 * ‖S‖^alpha) * ‖x-z‖^alpha :=
          htrans
      _ = Khol * L * ‖x-z‖^alpha := by dsimp [Khol, L']; ring
      _ ≤ C * L * ‖x-z‖^alpha := by
        calc
          Khol * L * ‖x-z‖^alpha = Khol * (L * ‖x-z‖^alpha) := by ring
          _ ≤ C * (L * ‖x-z‖^alpha) :=
            mul_le_mul_of_nonneg_right hKholC
              (mul_nonneg hL (Real.rpow_nonneg (norm_nonneg _) _))
          _ = C * L * ‖x-z‖^alpha := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
