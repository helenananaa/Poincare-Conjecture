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
/-- Actual right time derivative of a mild solution, with no assumed generator or derivative. -/
theorem semilinear_mild_right_time_derivative (f : E3 →ᵇ ℝ) (N : ℝ → ℝ)
    (L T : ℝ) (hL : 0≤L) (hT : 0<T)
    (hN : ∀ a b : ℝ, |N a-N b|≤L*|a-b|) (u : (ℝ × E3) →ᵇ ℝ)
    (hu : ∀ t : ℝ, 0<t → t≤T → ∀ x : E3,
      u (t,x)=(∫ y : E3, euclideanHeatKernel 3 t y*f (x-y))+
        ∫ s in (0:ℝ)..t, ∫ y : E3, euclideanHeatKernel 3 (t-s) y*N (u (s,x-y))) :
    ∀ S∈Ioo (0:ℝ) T, ∀ x : E3,
      HasDerivWithinAt (fun s : ℝ => u (s,x))
        ((∑ i : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ (fun w : E3 => u (S,w)) z
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1))+N (u (S,x))) (Ici S) S :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  intro S hS x
  obtain ⟨B, hB, -, -⟩ := bounded_nemytskii_operator N L hL hN
  let F : (ℝ × E3) →ᵇ ℝ := B u
  have hF (s : ℝ) (y : E3) : F (s, y) = N (u (s, y)) := by
    dsimp [F]
    exact hB u (s, y)
  let uS : E3 →ᵇ ℝ := u.compContinuous
    ⟨fun y : E3 => (S, y), continuous_const.prodMk continuous_id⟩
  have huS (y : E3) : uS y = u (S, y) := rfl
  have huS_fun : (uS : E3 → ℝ) = fun y : E3 => u (S, y) := by
    funext y
    exact huS y
  have hC2 : ContDiff ℝ 2 (fun y : E3 => u (S, y)) := by
    exact semilinear_mild_spatial_C2 f N L T hL hT.le hN u hu S hS.1 hS.2.le
  have hheat := heat_generator_at_C2_initial_data uS hC2 x
  have hduhamel := duhamel_terminal_quotient F S x
  have hsum : Tendsto
      (fun h : ℝ =>
        h⁻¹ * ((∫ y : E3, euclideanHeatKernel 3 h y * uS (x-y))-uS x) +
          h⁻¹ * ∫ s in S..(S+h), ∫ y : E3,
            euclideanHeatKernel 3 (S+h-s) y * F (s,x-y))
      (𝓝[>] (0:ℝ))
      (𝓝 ((∑ i : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ
          (fun w : E3 => u (S,w)) z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) + N (u (S,x)))) := by
    have h := hheat.add hduhamel
    simpa [huS_fun, hF] using h
  have hquot : Tendsto
      (fun h : ℝ => h⁻¹ * (u (S+h,x)-u (S,x)))
      (𝓝[>] (0:ℝ))
      (𝓝 ((∑ i : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ
          (fun w : E3 => u (S,w)) z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) + N (u (S,x)))) := by
    apply hsum.congr'
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hS.2)] with h hh
    have hrestart := semilinear_mild_restart f N L T hL hN u hu
      S h hS.1 hh.1 (by linarith [hh.2]) x
    rw [hrestart]
    simp_rw [hF]
    rw [huS]
    dsimp [uS]
    ring
  have htrans : Tendsto (fun s : ℝ => s-S) (𝓝[>] S) (𝓝[>] (0:ℝ)) := by
    apply (tendsto_nhdsWithin_iff).2
    constructor
    · have hbase : Tendsto (fun s : ℝ => s-S) (𝓝 S) (𝓝 (0:ℝ)) := by
        simpa using (tendsto_id.sub
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => S) (𝓝 S) (𝓝 S)))
      exact tendsto_nhdsWithin_of_tendsto_nhds hbase
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change S < s at hs
      exact sub_pos.mpr hs
  have hslope : Tendsto (slope (fun s : ℝ => u (s,x)) S)
      (𝓝[>] S)
      (𝓝 ((∑ i : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ
          (fun w : E3 => u (S,w)) z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) + N (u (S,x)))) := by
    apply (hquot.comp htrans).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [slope_def_field]
    dsimp
    ring_nf
  apply (hasDerivWithinAt_iff_tendsto_slope).2
  rw [Ici_sdiff_left]
  exact hslope
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
