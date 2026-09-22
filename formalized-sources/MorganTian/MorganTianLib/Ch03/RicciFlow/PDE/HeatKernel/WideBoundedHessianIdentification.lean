import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatFirstFDeriv
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatGradientFDeriv
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatHessianContinuous
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveJointSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursivePolynomialMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderHessianConvolutionThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHolderControl
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Identify actual convolution derivatives, not only formal differentiated-kernel integrals. -/
theorem euclideanHeatKernel_bounded_hessian_identification (f : E3 →ᵇ ℝ)
    {t : ℝ} (ht : 0 < t) :
    let u : E3 → ℝ := fun x => ∫ y : E3, euclideanHeatKernel 3 t (x-y)*f y
    ContDiff ℝ 2 u ∧ ∀ (x : E3) (i j : Fin 3),
      fderiv ℝ (fun z : E3 => fderiv ℝ u z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1) =
      ∫ y : E3, fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
        (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) * f (x-y) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  dsimp
  let u : E3 → ℝ := fun x => ∫ y : E3,
    euclideanHeatKernel 3 t (x-y) * f y
  let q : Fin 3 → E3 → ℝ := fun i x => ∫ y : E3,
    fderiv ℝ (euclideanHeatKernel 3 t) (x-y)
      (EuclideanSpace.single i 1) * f y
  let r : Fin 3 → Fin 3 → E3 → ℝ := fun i j x => ∫ y : E3,
    fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
      (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1) * f y
  let P : Fin 3 → E3 →L[ℝ] ℝ := fun i =>
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i
  let A : E3 → E3 →L[ℝ] ℝ := fun x => ∑ i : Fin 3, q i x • P i
  have hq (i : Fin 3) : ContDiff ℝ 1 (q i) := by
    apply contDiff_one_iff_hasFDerivAt.2
    refine ⟨fun x => ∑ j : Fin 3, r i j x • P j, ?_, ?_⟩
    · apply continuous_finsetSum
      intro j hj
      exact (bounded_heat_hessian_continuous f ht i j).smul continuous_const
    · intro x
      simpa [q, r, P] using (bounded_heat_gradient_fderiv f ht x i)
  have hA : ContDiff ℝ 1 A := by
    dsimp [A]
    apply ContDiff.sum
    intro i hi
    exact (hq i).smul_const (P i)
  have hu_deriv (x : E3) : fderiv ℝ u x = A x := by
    have h := (bounded_heat_first_fderiv f ht x).fderiv
    simpa [u, A, q, P] using h
  have hu_diff : Differentiable ℝ u := by
    intro x
    exact (bounded_heat_first_fderiv f ht x).differentiableAt
  have hu2 : ContDiff ℝ 2 u := by
    rw [show (2 : ℕ∞ω) = (1 : ℕ∞ω) + 1 by norm_num,
      contDiff_succ_iff_fderiv_apply]
    refine ⟨hu_diff, ?_, ?_⟩
    · intro htop
      simp at htop
    · intro v
      rw [show (fun x => fderiv ℝ u x v) = (fun x => A x v) by
        funext x
        rw [hu_deriv]]
      exact hA.clm_apply contDiff_const
  refine ⟨hu2, ?_⟩
  intro x i j
  have hgrad_eq (k : Fin 3) (z : E3) :
      fderiv ℝ u z (EuclideanSpace.single k 1) = q k z := by
    rw [hu_deriv]
    dsimp [A]
    have hcoord :
        (∑ l : Fin 3, q l z • P l) (EuclideanSpace.single k 1) = q k z := by
      simp [P, PiLp.proj_apply]
    rw [hcoord]
  have hgrad_fun (k : Fin 3) :
      (fun z : E3 => fderiv ℝ u z (EuclideanSpace.single k 1)) = q k := by
    funext z
    exact hgrad_eq k z
  rw [hgrad_fun i]
  have happly : fderiv ℝ (q i) x (EuclideanSpace.single j 1) =
      r i j x := by
    simpa [q, r] using
      congrArg (fun L : E3 →L[ℝ] ℝ => L (EuclideanSpace.single j 1))
        (bounded_heat_gradient_fderiv f ht x i).fderiv
  rw [happly]
  let h : E3 → ℝ := fun y =>
    fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
      (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)
  have hchange : (∫ y : E3, h (x-y) * f y) =
      ∫ y : E3, h y * f (x-y) := by
    rw [← integral_sub_left_eq_self (fun z : E3 => h z * f (x-z)) volume x]
    congr 1
    funext y
    congr 2
    abel
  simpa [r, h] using hchange
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
