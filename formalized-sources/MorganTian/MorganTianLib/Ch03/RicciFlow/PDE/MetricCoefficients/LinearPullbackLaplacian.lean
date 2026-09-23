import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LinearPullbackSecondDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LinearHessianContraction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** linear pullback laplacian. -/
theorem linear_pullback_laplacian (f : E3 → ℝ) (B : E3 →L[ℝ] E3) (x : E3) (hf : ContDiffAt ℝ 2 f (B x)) :
    let e := fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ);
    (∑ k : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun z => f (B z)) y (e k)) x (e k)) =
      ∑ i : Fin 3, ∑ j : Fin 3, (∑ k : Fin 3, (B (e k)) i*(B (e k)) j) *
        fderiv ℝ (fun y => fderiv ℝ f y (e j)) (B x) (e i) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  dsimp only
  let e : Fin 3 → E3 := fun i => EuclideanSpace.single i (1 : ℝ)
  let H : E3 →L[ℝ] E3 →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ f) (B x)
  have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ f) (B x) :=
    hf.fderiv_right (by norm_num)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) (B x) :=
    hfderiv.differentiableAt (by norm_num)
  have h_eval_plain (v w : E3) :
      fderiv ℝ (fun y => fderiv ℝ f y v) (B x) w = H w v := by
    have h := fderiv_clm_apply hdiff
      (differentiableAt_const (c := v) (x := B x))
    have h' := congrArg (fun L : E3 →L[ℝ] ℝ => L w) h
    simpa [H] using h'
  have h_eval (v w : E3) :
      fderiv ℝ (fun y => fderiv ℝ f y (B v)) (B x) (B w) =
        H (B w) (B v) := by
    exact h_eval_plain (B v) (B w)
  have hterm (k : Fin 3) :
      fderiv ℝ (fun y => fderiv ℝ (fun z => f (B z)) y (e k)) x (e k) =
        H (B (e k)) (B (e k)) := by
    rw [linear_pullback_second_derivative f B x (e k) (e k) hf]
    exact h_eval (e k) (e k)
  calc
    (∑ k : Fin 3,
        fderiv ℝ (fun y => fderiv ℝ (fun z => f (B z)) y (e k)) x (e k)) =
        ∑ k : Fin 3, H (B (e k)) (B (e k)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact hterm k
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
        (∑ k : Fin 3, (B (e k)) i * (B (e k)) j) *
          H (e i) (e j) := by
      exact linear_hessian_contraction B H
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
        (∑ k : Fin 3, (B (e k)) i * (B (e k)) j) *
          fderiv ℝ (fun y => fderiv ℝ f y (e j)) (B x) (e i) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← h_eval_plain (e j) (e i)]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
