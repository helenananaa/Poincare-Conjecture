import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearMildRightTimeDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearMildJointHessian
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ContinuousRightDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HistoryHessianJointContinuity
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHessianTerminalTail
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideDuhamelHessianThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HeatGeneratorC2
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearMildRestart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.ParabolicPDE
open Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual local classical semilinear heat IVP for bounded uniformly continuous initial data. -/
theorem semilinear_local_classical_ivp (f : E3 →ᵇ ℝ) (hf : UniformContinuous f)
    (N : ℝ → ℝ) (L : ℝ) (hL : 0≤L) (hN : ∀ a b : ℝ, |N a-N b|≤L*|a-b|) :
    ∃ T : ℝ, 0<T ∧ ∃ u : (ℝ × E3) →ᵇ ℝ,
      (∀ x, u (0,x)=f x) ∧ TendstoUniformly (fun t x => u (t,x)) f (𝓝[>] (0:ℝ)) ∧
      ∀ t∈Ioo (0:ℝ) T,
        ContDiff ℝ 2 (fun x : E3 => u (t,x)) ∧ ∀ x : E3,
        HasDerivAt (fun s : ℝ => u (s,x))
          ((∑ i : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ (fun w : E3 => u (t,w)) z
            (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1))+N (u (t,x))) t :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨T, hT, u, hu0, htrace, hu⟩ := semilinear_local_mild_ivp f hf N L hL hN
  have hNlip : LipschitzWith L.toNNReal N :=
    LipschitzWith.of_dist_le_mul (fun a b : ℝ => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL]
      exact hN a b)
  have hNcont : Continuous N := hNlip.continuous
  refine ⟨T, hT, u, hu0, htrace, ?_⟩
  intro t ht
  have hC2 := semilinear_mild_spatial_C2 f N L T hL hT.le hN u hu t ht.1 ht.2.le
  refine ⟨hC2, ?_⟩
  intro x
  have hHcont (i : Fin 3) :
      ContinuousOn (fun s : ℝ => fderiv ℝ (fun z : E3 =>
        fderiv ℝ (fun w : E3 => u (s,w)) z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) (Ioo (0 : ℝ) T) := by
    have h := semilinear_mild_joint_hessian_continuity f N L T hL hT hN u hu i i
    have hmap : ContinuousOn (fun s : ℝ => (s, x)) (Ioo (0 : ℝ) T) :=
      continuousOn_id.prodMk
        (continuousOn_const : ContinuousOn (fun _ : ℝ => x) (Ioo (0 : ℝ) T))
    have hc := h.comp' hmap
      (fun s hs => ⟨hs, mem_univ _⟩)
    simpa using hc
  have hsumcont :
      ContinuousOn (fun s : ℝ => ∑ i : Fin 3, fderiv ℝ (fun z : E3 =>
        fderiv ℝ (fun w : E3 => u (s,w)) z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) (Ioo (0 : ℝ) T) := by
    exact continuousOn_finsetSum Finset.univ (fun i hi => hHcont i)
  have hux : Continuous (fun s : ℝ => u (s,x)) :=
    u.continuous.comp (continuous_id.prodMk continuous_const)
  have hNux : Continuous (fun s : ℝ => N (u (s,x))) := hNcont.comp hux
  have hfu : ContinuousOn (fun s : ℝ => u (s,x)) (Ioo (0 : ℝ) T) := hux.continuousOn
  have hgu : ContinuousOn (fun s : ℝ =>
      (∑ i : Fin 3, fderiv ℝ (fun z : E3 =>
        fderiv ℝ (fun w : E3 => u (s,w)) z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) + N (u (s,x))) (Ioo (0 : ℝ) T) :=
    hsumcont.add hNux.continuousOn
  have hd := continuous_right_derivative_is_derivative
    (fun s : ℝ => u (s,x))
    (fun s : ℝ =>
      (∑ i : Fin 3, fderiv ℝ (fun z : E3 =>
        fderiv ℝ (fun w : E3 => u (s,w)) z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) + N (u (s,x)))
    0 T hfu hgu (by
      intro s hs
      exact semilinear_mild_right_time_derivative f N L T hL hT hN u hu s hs x)
  exact hd t ht
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
