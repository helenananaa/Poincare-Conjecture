import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.CompactSpatialDerivativeDominator
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
/-- The actual truncated Hessian integrals are continuous in their spatial parameter. -/
theorem truncated_duhamel_hessian_continuous (F : (ℝ × E3) →ᵇ ℝ) (T eps : ℝ)
    (heps : 0<eps) (hT : eps≤T) (i j : Fin 3) :
    Continuous (fun x : E3 => ∫ s in (0:ℝ)..(T-eps), ∫ y : E3,
      fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
        (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1)*F (s,y)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  rw [continuous_iff_continuousAt]
  intro x₀
  let b : ℝ := T - eps
  let S : Set E3 := Metric.closedBall 0 (‖x₀‖ + 1)
  have hTpos : 0 < T := lt_of_lt_of_le heps hT
  have hb : 0 ≤ b := sub_nonneg.mpr hT
  have hball (x : E3) (hx : x ∈ S) : ‖x‖ ≤ ‖x₀‖ + 1 := by
    simpa [S, Metric.mem_closedBall, dist_eq_norm] using hx
  have hx₀ : x₀ ∈ S := by
    rw [show S = Metric.closedBall 0 (‖x₀‖ + 1) by rfl,
      Metric.mem_closedBall]
    simpa [dist_eq_norm] using
      (le_add_of_nonneg_right (norm_nonneg x₀))
  have hS_nhds : S ∈ 𝓝 x₀ := by
    apply Metric.mem_nhds_iff.2
    refine ⟨1, one_pos, ?_⟩
    intro z hz
    change dist z x₀ < 1 at hz
    rw [show S = Metric.closedBall 0 (‖x₀‖ + 1) by rfl,
      Metric.mem_closedBall]
    calc
      dist z 0 ≤ dist z x₀ + dist x₀ 0 := dist_triangle _ _ _
      _ ≤ 1 + ‖x₀‖ := by
        rw [dist_zero_right]
        simpa [add_comm] using (add_le_add_right hz.le ‖x₀‖)
      _ ≤ ‖x₀‖ + 1 := by simpa [add_comm]
  obtain ⟨g, hg, hg_nonneg, hdom⟩ :=
    compact_time_spatial_derivative_dominator eps T (‖x₀‖ + 1)
      heps hT (by positivity)
  let K : (ℝ × E3) → ℝ := fun p =>
    fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 p.1) z
      (EuclideanSpace.single i 1)) p.2 (EuclideanSpace.single j 1)
  have hK_formula (p : ℝ × E3) (hp : p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set E3)) :
      K p = (p.2 i * p.2 j / (4 * p.1 ^ 2) -
        (if i = j then 1 / (2 * p.1) else 0)) *
          euclideanHeatKernel 3 p.1 p.2 := by
    dsimp [K]
    exact euclideanHeatKernel_three_hessian_formula hp.1 p.2 i j
  have hK_formula_cont : ContinuousOn
      (fun p : ℝ × E3 =>
        (p.2 i * p.2 j / (4 * p.1 ^ 2) -
          (if i = j then 1 / (2 * p.1) else 0)) *
            euclideanHeatKernel 3 p.1 p.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
    have hkernel : ContinuousOn
        (fun p : ℝ × E3 => euclideanHeatKernel 3 p.1 p.2)
        (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) :=
      (euclideanHeatKernel_joint_smooth 3).continuousOn
    have hA : ContinuousOn
        (fun p : ℝ × E3 => p.2 i * p.2 j / (4 * p.1 ^ 2))
        (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro p hp
        have hp0 : 0 < p.1 := hp.1
        positivity
    have hB : ContinuousOn
        (fun p : ℝ × E3 => 1 / (2 * p.1))
        (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro p hp
        have hp0 : 0 < p.1 := hp.1
        positivity
    have hdiag : ContinuousOn
        (fun p : ℝ × E3 => if i = j then 1 / (2 * p.1) else 0)
        (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
      by_cases hij : i = j
      · simp only [if_pos hij]
        simpa [div_eq_mul_inv, mul_comm] using hB
      · simp only [if_neg hij]
        exact continuousOn_const
    exact (hA.sub hdiag).mul hkernel
  have hK_cont : ContinuousOn K
      (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
    exact hK_formula_cont.congr (fun p hp => hK_formula p hp)
  have htime (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) b) : T - s ∈ Icc eps T := by
    rw [uIcc_of_le hb] at hs
    constructor <;> linarith [hs.1, hs.2]
  let I : E3 → ℝ → ℝ := fun x s => ∫ y : E3,
    K (T - s, x - y) * F (s, y)
  have hQ_meas (x : E3) (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) b) :
      AEStronglyMeasurable (fun y : E3 =>
        K (T - s, x - y) * F (s, y)) volume := by
    have hline : Continuous (fun y : E3 => (T - s, x - y)) := by
      fun_prop
    have hlineOn : ContinuousOn (fun y : E3 => (T - s, x - y))
        (univ : Set E3) := hline.continuousOn
    have hmap : MapsTo (fun y : E3 => (T - s, x - y)) (univ : Set E3)
        (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
      intro y hy
      exact ⟨lt_of_lt_of_le heps (htime s hs).1, mem_univ _⟩
    have hKlineOn := hK_cont.comp hlineOn hmap
    have hKline : Continuous (fun y : E3 => K (T - s, x - y)) := by
      simpa only [continuousOn_univ, Function.comp_def] using hKlineOn
    have hFline : Continuous (fun y : E3 => F (s, y)) := by
      exact F.continuous.comp (continuous_const.prodMk continuous_id)
    exact (hKline.mul hFline).aestronglyMeasurable
  have hQ_bound (x : E3) (hx : x ∈ S) (s : ℝ)
      (hs : s ∈ uIcc (0 : ℝ) b) : ∀ᵐ y ∂volume, ‖K (T - s, x - y) * F (s, y)‖ ≤
        ‖F‖ * g y := by
    filter_upwards [] with y
    have hxy := hball x hx
    have hh := hdom (T - s) (htime s hs) x y hxy
    have hK : |K (T - s, x - y)| ≤ g y := hh.2.2 i j
    have hF : |F (s, y)| ≤ ‖F‖ := by
      simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (s, y)
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |K (T - s, x - y)| * |F (s, y)| ≤ g y * ‖F‖ :=
        mul_le_mul hK hF (abs_nonneg _) (hg_nonneg y)
      _ = ‖F‖ * g y := by ring
  have hI_contOn (x : E3) (hx : x ∈ S) :
      ContinuousOn (I x) (uIcc (0 : ℝ) b) := by
    let Q : ℝ → E3 → ℝ := fun s y => K (T - s, x - y) * F (s, y)
    have hQ_meas' : ∀ s ∈ uIcc (0 : ℝ) b,
        AEStronglyMeasurable (Q s) volume := by
      intro s hs
      simpa [Q] using hQ_meas x s hs
    have hQ_bound' : ∀ s ∈ uIcc (0 : ℝ) b,
        ∀ᵐ y ∂volume, ‖Q s y‖ ≤ ‖F‖ * g y := by
      intro s hs
      simpa [Q] using hQ_bound x hx s hs
    have hQ_cont' : ∀ᵐ y ∂volume,
        ContinuousOn (fun s : ℝ => Q s y) (uIcc (0 : ℝ) b) := by
      filter_upwards [] with y
      have hline : ContinuousOn (fun s : ℝ => (T - s, x - y))
          (uIcc (0 : ℝ) b) := by
        fun_prop
      have hmap : MapsTo (fun s : ℝ => (T - s, x - y))
          (uIcc (0 : ℝ) b) (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
        intro s hs
        exact ⟨lt_of_lt_of_le heps (htime s hs).1, mem_univ _⟩
      have hKline := hK_cont.comp hline hmap
      have hFline : ContinuousOn (fun s : ℝ => F (s, y))
          (uIcc (0 : ℝ) b) := by
        exact (F.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
      exact (hKline.mul hFline).congr (fun s hs => rfl)
    have hQint : Integrable (fun y : E3 => ‖F‖ * g y) volume :=
      hg.const_mul ‖F‖
    have h := continuousOn_of_dominated (s := uIcc (0 : ℝ) b)
      (F := Q) (bound := fun y : E3 => ‖F‖ * g y)
      hQ_meas' hQ_bound' hQint hQ_cont'
    simpa [I, Q] using h
  have hI_meas : ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable (I x) (volume.restrict (uIoc (0 : ℝ) b)) := by
    filter_upwards [hS_nhds] with x hx
    have hcont := (hI_contOn x hx).mono uIoc_subset_uIcc
    exact hcont.aestronglyMeasurable measurableSet_uIoc
  have hI_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ s ∂volume,
      s ∈ uIoc (0 : ℝ) b → ‖I x s‖ ≤ ∫ y : E3, ‖F‖ * g y := by
    filter_upwards [hS_nhds] with x hx
    filter_upwards [] with s
    intro hs
    have hs' : s ∈ uIcc (0 : ℝ) b := uIoc_subset_uIcc hs
    have hmajor : Integrable (fun y : E3 => ‖F‖ * g y) volume :=
      hg.const_mul ‖F‖
    have hnorm := norm_integral_le_of_norm_le hmajor (hQ_bound x hx s hs')
    simpa [I] using hnorm
  have hI_cont_slice (s : ℝ) (hs : s ∈ uIoc (0 : ℝ) b) :
      Continuous (fun x : E3 => I x s) := by
    have hs' : s ∈ uIcc (0 : ℝ) b := uIoc_subset_uIcc hs
    have ht : 0 < T - s := lt_of_lt_of_le heps (htime s hs').1
    let f : E3 →ᵇ ℝ :=
      BoundedContinuousFunction.ofNormedAddCommGroup
        (fun y : E3 => F (s, y))
        (F.continuous.comp (continuous_const.prodMk continuous_id))
        ‖F‖ (fun y => F.norm_coe_le_norm (s, y))
    have h := bounded_heat_hessian_continuous f ht i j
    simpa [I, K, f] using h
  have houter := intervalIntegral.continuousAt_of_dominated_interval
    (μ := (volume : Measure ℝ)) (x₀ := x₀)
    (F := I) (bound := fun _ : ℝ => ∫ y : E3, ‖F‖ * g y)
    hI_meas hI_bound intervalIntegrable_const ?_
  · simpa [I, b] using houter
  · filter_upwards [] with s hs
    exact (hI_cont_slice s hs).continuousAt
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
