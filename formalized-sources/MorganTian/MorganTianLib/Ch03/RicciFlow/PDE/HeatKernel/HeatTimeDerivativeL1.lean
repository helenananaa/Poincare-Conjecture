import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveJointSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursivePolynomialMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideHessianUnweighted
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The actual time derivative has a common integrable positive-time bound. -/
theorem euclideanHeatKernel_three_time_derivative_L1 :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      Integrable (fun y : E3 => deriv (fun s => euclideanHeatKernel 3 s y) t) volume ∧
      (∫ y : E3, |deriv (fun s => euclideanHeatKernel 3 s y) t|) ≤ C/t :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C, hC, hH⟩ := euclideanHeatKernel_three_hessian_L1
  refine ⟨3 * C, by positivity, ?_⟩
  intro t ht
  have hgauss := gaussianHeatKernel_derivatives ht
  have hiter (f : ℝ → ℝ) :
      iteratedDeriv 2 f = deriv (deriv f) := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  have hspaceFactor (y : ℝ) :
      HasDerivAt (gaussianHeatKernel t) (deriv (gaussianHeatKernel t) y) y :=
    (hgauss.1.differentiable (by simp) y).hasDerivAt
  have hspaceSecond (y : ℝ) :
      HasDerivAt (deriv (gaussianHeatKernel t))
        (gaussianHeatHessian t y) y := by
    have hsecond : deriv (deriv (gaussianHeatKernel t)) y =
        gaussianHeatHessian t y := by
      rw [← congr_fun (hiter (gaussianHeatKernel t)) y]
      exact (hgauss.2 y).2.1
    have hd := (contDiff_infty_iff_deriv.mp hgauss.1).2.differentiable (by simp) y
    exact hd.hasDerivAt.congr_deriv hsecond
  have hcoord (x : E3) (i : Fin 3) :
      iteratedDeriv 2
          (fun z : ℝ => euclideanHeatKernel 3 t
            (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i z))) (x i) =
        gaussianHeatHessian t (x i) *
          ∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t (x j) := by
    have hcurve (i : Fin 3) :
        (fun z : ℝ => euclideanHeatKernel 3 t
          (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i z))) =
          (fun z : ℝ => gaussianHeatKernel t z *
            ∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t (x j)) := by
      funext z
      unfold euclideanHeatKernel
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j : Fin 3 => gaussianHeatKernel t
          ((Function.update (WithLp.ofLp x) i z) j)) (Finset.mem_univ i)]
      rw [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [hcurve i, hiter]
    have hderiv :
        deriv (fun z : ℝ => gaussianHeatKernel t z *
          ∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t (x j)) =
          (fun z : ℝ => deriv (gaussianHeatKernel t) z *
            ∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t (x j)) := by
      funext z
      have hp := (hspaceFactor z).mul
        (hasDerivAt_const z (∏ j ∈ (Finset.univ.erase i),
          gaussianHeatKernel t (x j)))
      simpa using hp.deriv
    rw [hderiv]
    have hp := (hspaceSecond (x i)).mul
      (hasDerivAt_const (x i) (∏ j ∈ (Finset.univ.erase i),
        gaussianHeatKernel t (x j)))
    change HasDerivAt
      (fun z : ℝ => deriv (gaussianHeatKernel t) z *
        ∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t (x j))
      (gaussianHeatHessian t (x i) *
          ∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t (x j) +
        deriv (gaussianHeatKernel t) (x i) * 0) (x i) at hp
    simpa only [Pi.mul_apply, mul_zero, add_zero] using hp.deriv
  let H : Fin 3 → E3 → ℝ := fun i y =>
    fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
      (EuclideanSpace.single i 1)) y (EuclideanSpace.single i 1)
  have hbridge (x : E3) (i : Fin 3) :
      iteratedDeriv 2
          (fun z : ℝ => euclideanHeatKernel 3 t
            (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i z))) (x i) =
        H i x := by
    rw [hcoord x i]
    dsimp [H]
    rw [euclideanHeatKernel_three_hessian_formula ht x i i]
    simp only [ite_true]
    unfold euclideanHeatKernel
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j : Fin 3 => gaussianHeatKernel t (x j)) (Finset.mem_univ i)]
    unfold gaussianHeatHessian
    ring
  have hHi (i : Fin 3) : Integrable (H i) volume ∧
      (∫ y : E3, |H i y|) ≤ C / t := by
    simpa [H] using hH t ht i i
  have hsum : Integrable (fun y : E3 => ∑ i : Fin 3, H i y) volume := by
    refine integrable_finsetSum Finset.univ ?_
    intro i hi
    exact (hHi i).1
  have hsum_abs : Integrable (fun y : E3 => ∑ i : Fin 3, |H i y|) volume := by
    refine integrable_finsetSum Finset.univ ?_
    intro i hi
    exact (hHi i).1.norm
  have htime (x : E3) :
      deriv (fun s => euclideanHeatKernel 3 s x) t = ∑ i : Fin 3, H i x := by
    rw [(euclideanHeatKernel_three_heat_equation ht).2 x]
    apply Finset.sum_congr rfl
    intro i hi
    exact hbridge x i
  refine ⟨?_, ?_⟩
  · simpa only [htime] using hsum
  · have hle :
        (∫ y : E3, |∑ i : Fin 3, H i y|) ≤
          ∫ y : E3, ∑ i : Fin 3, |H i y| := by
      apply integral_mono hsum.norm hsum_abs
      intro y
      simpa only [Real.norm_eq_abs] using Finset.abs_sum_le_sum_abs (s := Finset.univ)
        (f := fun i : Fin 3 => H i y)
    have hsum_integral :
        (∫ y : E3, ∑ i : Fin 3, |H i y|) =
          ∑ i : Fin 3, ∫ y : E3, |H i y| := by
      simpa only [Real.norm_eq_abs] using
        (integral_finsetSum (μ := (volume : Measure E3)) Finset.univ
          (fun i hi => (hHi i).1.norm))
    calc
      (∫ y : E3, |deriv (fun s => euclideanHeatKernel 3 s y) t|) =
          ∫ y : E3, |∑ i : Fin 3, H i y| := by
            congr 1
            funext y
            rw [htime y]
      _ ≤ ∑ i : Fin 3, ∫ y : E3, |H i y| := hle.trans_eq hsum_integral
      _ ≤ ∑ i : Fin 3, C / t := Finset.sum_le_sum (fun i hi => (hHi i).2)
      _ = (3 * C) / t := by
        simp
        ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
