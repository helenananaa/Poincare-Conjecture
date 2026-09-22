import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.TimeDerivativeDominator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatFirstFDeriv
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatGradientFDeriv
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatHessianContinuous
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHessianTerminalTail
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientL1
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction RealInnerProductSpace
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Uniform convergence of two actual Frechet derivative levels preserves C2 regularity. -/
theorem contDiff_two_of_uniform_derivative_limits
    (f : ℕ → E3 → ℝ) (v : E3 → ℝ)
    (g : E3 → (E3 →L[ℝ] ℝ)) (h : E3 → (E3 →L[ℝ] (E3 →L[ℝ] ℝ)))
    (hf : ∀ n, ContDiff ℝ 2 (f n)) (hv : TendstoUniformly f v atTop)
    (hg : TendstoUniformly (fun n => fderiv ℝ (f n)) g atTop)
    (hh : TendstoUniformly (fun n => fderiv ℝ (fderiv ℝ (f n))) h atTop) :
    ContDiff ℝ 2 v ∧ fderiv ℝ v=g ∧ fderiv ℝ g=h :=
/- SWARM_PROOF_BEGIN -/
by
  have hfn_diff : ∀ n, Differentiable ℝ (f n) := by
    intro n
    exact (hf n).differentiable (by norm_num)
  have hfn_deriv : ∀ n x, HasFDerivAt (f n) (fderiv ℝ (f n) x) x := by
    intro n x
    exact (hfn_diff n x).hasFDerivAt
  have hderiv_cont : ∀ n, ContDiff ℝ 1 (fderiv ℝ (f n)) := by
    intro n
    have hn : ContDiff ℝ ((1 : ℕ∞ω) + 1) (f n) := by
      convert hf n using 1 <;> norm_num
    exact (contDiff_succ_iff_fderiv.mp hn).2.2
  have hv_at : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (v x)) := by
    intro x
    exact hv.tendstoUniformlyOnFilter.tendsto_at le_top
  have hg_at : ∀ x, Tendsto (fun n => fderiv ℝ (f n) x) atTop (𝓝 (g x)) := by
    intro x
    exact hg.tendstoUniformlyOnFilter.tendsto_at le_top
  have hvg : ∀ x, HasFDerivAt v (g x) x := by
    intro x
    exact hasFDerivAt_of_tendstoUniformly hg hfn_deriv hv_at x
  have hv_deriv : fderiv ℝ v = g := by
    funext x
    exact (hvg x).fderiv
  have hgg : ∀ x, HasFDerivAt g (h x) x := by
    intro x
    apply hasFDerivAt_of_tendstoUniformly hh
    · intro n x
      exact (hderiv_cont n).differentiable_one x |>.hasFDerivAt
    · exact hg_at
  have hh_cont : Continuous h := by
    apply hh.continuous
    exact Filter.Frequently.of_forall fun n =>
      (hderiv_cont n).continuous_fderiv one_ne_zero
  have hg_contDiff : ContDiff ℝ 1 g := by
    apply contDiff_one_iff_hasFDerivAt.2
    exact ⟨h, hh_cont, hgg⟩
  have hv_diff : Differentiable ℝ v := by
    intro x
    exact (hvg x).differentiableAt
  have hv2 : ContDiff ℝ 2 v := by
    rw [show (2 : ℕ∞ω) = (1 : ℕ∞ω) + 1 by norm_num,
      contDiff_succ_iff_fderiv]
    refine ⟨hv_diff, ?_, ?_⟩
    · intro htop
      simp at htop
    · simpa [hv_deriv] using hg_contDiff
  have hg_deriv : fderiv ℝ g = h := by
    funext x
    exact (hgg x).fderiv
  exact ⟨hv2, hv_deriv, hg_deriv⟩
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
