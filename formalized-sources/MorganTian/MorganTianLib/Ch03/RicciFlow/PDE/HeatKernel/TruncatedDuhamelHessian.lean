import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.TruncatedDuhamelFirstDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.TruncatedDuhamelGradientDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.TruncatedDuhamelHessianContinuous
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideDuhamelHessianThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.TimeDerivativeDominator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatGradientFDeriv
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatHessianContinuous
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
theorem truncated_duhamel_hessian (F : (ℝ × E3) →ᵇ ℝ) (T eps : ℝ)
    (heps : 0<eps) (hT : eps≤T) :
    let v : E3 → ℝ := fun x => ∫ s in (0:ℝ)..(T-eps),
      ∫ y : E3, euclideanHeatKernel 3 (T-s) (x-y)*F (s,y)
    ContDiff ℝ 2 v ∧ ∀ (x : E3) (i j : Fin 3),
      fderiv ℝ (fun z : E3 => fderiv ℝ v z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1) =
      ∫ s in (0:ℝ)..(T-eps), ∫ y : E3,
        fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)*F (s,x-y) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  dsimp
  let b : ℝ := T - eps
  let v : E3 → ℝ := fun x => ∫ s in (0 : ℝ)..b,
    ∫ y : E3, euclideanHeatKernel 3 (T-s) (x-y)*F (s,y)
  change ContDiff ℝ 2 v ∧ ∀ (x : E3) (i j : Fin 3),
    fderiv ℝ (fun z : E3 => fderiv ℝ v z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1) =
      ∫ s in (0:ℝ)..b, ∫ y : E3,
        fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)*F (s,x-y)
  let P : Fin 3 → E3 →L[ℝ] ℝ := fun i =>
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i
  let q : Fin 3 → E3 → ℝ := fun i x =>
    ∫ s in (0 : ℝ)..b, ∫ y : E3,
      fderiv ℝ (euclideanHeatKernel 3 (T-s)) (x-y)
        (EuclideanSpace.single i 1) * F (s,y)
  let r : Fin 3 → Fin 3 → E3 → ℝ := fun i j x =>
    ∫ s in (0 : ℝ)..b, ∫ y : E3,
      fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
        (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1) * F (s,y)
  let A : E3 → E3 →L[ℝ] ℝ := fun x =>
    ∑ i : Fin 3, (q i x) • P i
  let B : Fin 3 → E3 → E3 →L[ℝ] ℝ := fun i x =>
    ∑ j : Fin 3, (r i j x) • P j
  have hq : ∀ i : Fin 3, ContDiff ℝ 1 (q i) := by
    intro i
    apply contDiff_one_iff_hasFDerivAt.2
    refine ⟨B i, ?_, ?_⟩
    · dsimp [B]
      apply continuous_finsetSum
      intro j hj
      exact (truncated_duhamel_hessian_continuous F T eps heps hT i j).smul
        continuous_const
    · intro x
      simpa [q, r, B, b] using
        (truncated_duhamel_gradient_derivative F T eps heps hT x i)
  have hA : ContDiff ℝ 1 A := by
    dsimp [A]
    apply ContDiff.sum
    intro i hi
    exact (hq i).smul_const (P i)
  have hv_deriv (x : E3) : fderiv ℝ v x = A x := by
    simpa [v, q, A, P, b] using
      (truncated_duhamel_first_derivative F T eps heps hT x).fderiv
  have hv_diff : Differentiable ℝ v := by
    intro x
    exact (truncated_duhamel_first_derivative F T eps heps hT x).differentiableAt
  have hv2 : ContDiff ℝ 2 v := by
    rw [show (2 : ℕ∞ω) = (1 : ℕ∞ω) + 1 by norm_num,
      contDiff_succ_iff_fderiv_apply]
    refine ⟨hv_diff, ?_, ?_⟩
    · intro htop
      simp at htop
    · intro w
      rw [show (fun x : E3 => fderiv ℝ v x w) = (fun x : E3 => A x w) by
        funext x
        rw [hv_deriv]]
      exact hA.clm_apply contDiff_const
  have hgrad (i : Fin 3) (x : E3) :
      fderiv ℝ v x (EuclideanSpace.single i 1) = q i x := by
    rw [hv_deriv]
    dsimp [A]
    simp [P, PiLp.proj_apply]
  have hsecond (i j : Fin 3) (x : E3) :
      fderiv ℝ (fun z : E3 => fderiv ℝ v z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1) = r i j x := by
    rw [show (fun z : E3 => fderiv ℝ v z (EuclideanSpace.single i 1)) = q i by
      funext z
      exact hgrad i z]
    have h := (truncated_duhamel_gradient_derivative F T eps heps hT x i).fderiv
    have hj := congrArg (fun L : E3 →L[ℝ] ℝ => L (EuclideanSpace.single j 1)) h
    simpa [r, B, b] using hj
  have hchange (i j : Fin 3) (x : E3) (s : ℝ) :
      (∫ y : E3, fderiv ℝ (fun z : E3 => fderiv ℝ
        (euclideanHeatKernel 3 (T-s)) z (EuclideanSpace.single i 1))
        (x-y) (EuclideanSpace.single j 1) * F (s,y)) =
      ∫ y : E3, fderiv ℝ (fun z : E3 => fderiv ℝ
        (euclideanHeatKernel 3 (T-s)) z (EuclideanSpace.single i 1))
        y (EuclideanSpace.single j 1) * F (s,x-y) := by
    let h : E3 → ℝ := fun y =>
      fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
        (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)
    rw [← integral_sub_left_eq_self (fun z : E3 => h z * F (s,x-z)) volume x]
    congr 1
    funext y
    congr 2
    abel
  refine ⟨hv2, ?_⟩
  intro x i j
  rw [hsecond i j x]
  dsimp [r]
  apply intervalIntegral.integral_congr_ae
  exact Eventually.of_forall (fun s hs => hchange i j x s)
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
