import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanBasic
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Semigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Equation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderTimeKernel
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators
noncomputable section
namespace MorganTianLib.ParabolicPDE
/-- **Math.** The explicit 3D product Gaussian solves the coordinate Laplace heat equation. -/
theorem euclideanHeatKernel_three_heat_equation {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (euclideanHeatKernel 3 t) ∧
      ∀ x : EuclideanSpace ℝ (Fin 3),
        deriv (fun s => euclideanHeatKernel 3 s x) t =
          ∑ i : Fin 3, iteratedDeriv 2
            (fun z : ℝ => euclideanHeatKernel 3 t
              (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i z))) (x i) := by
/- SWARM_PROOF_BEGIN -/
  classical
  have hgauss := gaussianHeatKernel_derivatives ht
  have htime_ne : t ≠ 0 := ne_of_gt ht
  have htime_pos : 0 < 4 * Real.pi * t := by positivity
  have hsqrt_pos : 0 < Real.sqrt (4 * Real.pi * t) :=
    Real.sqrt_pos.2 htime_pos
  have hsqrt_ne : Real.sqrt (4 * Real.pi * t) ≠ 0 := ne_of_gt hsqrt_pos
  have htimeDiff (y : ℝ) :
      DifferentiableAt ℝ (fun s : ℝ => gaussianHeatKernel s y) t := by
    have hargDiff : DifferentiableAt ℝ (fun s : ℝ => 4 * Real.pi * s) t := by
      fun_prop
    have hsqrtDiff : DifferentiableAt ℝ (fun s : ℝ =>
        Real.sqrt (4 * Real.pi * s)) t :=
      hargDiff.sqrt htime_pos.ne'
    have hnormDiff : DifferentiableAt ℝ (fun s : ℝ =>
        (Real.sqrt (4 * Real.pi * s))⁻¹) t :=
      hsqrtDiff.inv hsqrt_ne
    have hEtimeDiff : DifferentiableAt ℝ
        (fun s : ℝ => -(y ^ 2) / (4 * s)) t := by
      have hinv : DifferentiableAt ℝ (fun s : ℝ => s⁻¹) t :=
        differentiableAt_inv_iff.mpr htime_ne
      have htmp := hinv.const_mul (-(y ^ 2) / 4)
      exact htmp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => by ring))
    unfold gaussianHeatKernel
    exact hnormDiff.mul
      (Real.differentiableAt_exp.comp t hEtimeDiff)
  have htimeFactor (y : ℝ) :
      HasDerivAt (fun s : ℝ => gaussianHeatKernel s y)
        (gaussianHeatHessian t y) t := by
    exact (htimeDiff y).hasDerivAt.congr_deriv (hgauss.2 y).2.2
  have hspaceFactor (y : ℝ) :
      HasDerivAt (gaussianHeatKernel t) (deriv (gaussianHeatKernel t) y) y :=
    (hgauss.1.differentiable (by simp) y).hasDerivAt
  have hiter (f : ℝ → ℝ) :
      iteratedDeriv 2 f = deriv (deriv f) := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  have hspaceSecond (y : ℝ) :
      HasDerivAt (deriv (gaussianHeatKernel t))
        (gaussianHeatHessian t y) y := by
    have hsecond : deriv (deriv (gaussianHeatKernel t)) y =
        gaussianHeatHessian t y := by
      rw [← congr_fun (hiter (gaussianHeatKernel t)) y]
      exact (hgauss.2 y).2.1
    have hd := (contDiff_infty_iff_deriv.mp hgauss.1).2.differentiable (by simp) y
    exact hd.hasDerivAt.congr_deriv hsecond
  refine ⟨?_, ?_⟩
  · unfold euclideanHeatKernel
    exact contDiff_prod (fun i _ => hgauss.1.comp (by fun_prop))
  · intro x
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
    have hcoord (i : Fin 3) :
        iteratedDeriv 2
            (fun z : ℝ => euclideanHeatKernel 3 t
              (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i z))) (x i) =
          gaussianHeatHessian t (x i) *
            ∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t (x j) := by
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
    have htime :
        HasDerivAt (fun s : ℝ => ∏ i : Fin 3, gaussianHeatKernel s (x i))
          (∑ i : Fin 3,
            (∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t (x j)) *
              gaussianHeatHessian t (x i)) t := by
      have hp := HasDerivAt.finsetProd (u := Finset.univ)
          (f := fun i : Fin 3 => fun s : ℝ => gaussianHeatKernel s (x i))
          (f' := fun i : Fin 3 => gaussianHeatHessian t (x i))
          (fun i _ => htimeFactor (x i))
      have heq :
          (∏ i : Fin 3, fun s : ℝ => gaussianHeatKernel s (x i)) =
            (fun s : ℝ => ∏ i : Fin 3, gaussianHeatKernel s (x i)) := by
        funext s
        simp only [Finset.prod_apply]
      rw [heq] at hp
      simpa only [smul_eq_mul] using hp
    calc
      deriv (fun s => euclideanHeatKernel 3 s x) t =
          ∑ i : Fin 3,
            (∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t (x j)) *
              gaussianHeatHessian t (x i) := by
        simpa [euclideanHeatKernel] using htime.deriv
      _ = ∑ i : Fin 3, iteratedDeriv 2
          (fun z : ℝ => euclideanHeatKernel 3 t
            (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i z))) (x i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hcoord i]
        ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
