import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelRestart
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelTerminalQuotient
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearMildSpatialC2
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FullDuhamelSpatialC2
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.CompactSpatialDerivativeDominator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHessianTerminalTail
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedNemytskiiOperator
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.ParabolicPDE
open Set Function Filter MeasureTheory
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- A fixed, truncated source history has jointly continuous actual Hessian integrals. -/
theorem history_hessian_joint_continuity (F : (ℝ × E3) →ᵇ ℝ)
    (b : ℝ) (hb : 0≤b) (i j : Fin 3) :
    ContinuousOn (fun p : ℝ × E3 => ∫ s in (0:ℝ)..b, ∫ y : E3,
      fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (p.1-s)) z
        (EuclideanSpace.single i 1)) (p.2-y) (EuclideanSpace.single j 1)*F (s,y))
      (Ioi b ×ˢ (univ : Set E3)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  intro p hp
  by_cases hb0 : b = 0
  · simpa [hb0] using
      (continuousAt_const : ContinuousAt (fun _ : ℝ × E3 => (0 : ℝ)) p).continuousWithinAt
  have hp1 : b < p.1 := hp.1
  let δ : ℝ := (p.1 - b) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  let R : ℝ := ‖p.2‖ + 1
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  let S : Set E3 := Metric.closedBall 0 R
  have hball (x : E3) (hx : x ∈ S) : ‖x‖ ≤ R := by
    simpa [S, Metric.mem_closedBall, dist_eq_norm] using hx
  have hpS : p.2 ∈ S := by
    rw [show S = Metric.closedBall 0 R by rfl, Metric.mem_closedBall]
    dsimp [R]
    simpa [dist_eq_norm] using (le_add_of_nonneg_right (norm_nonneg p.2))
  have hS_nhds : S ∈ 𝓝 p.2 := by
    apply Metric.mem_nhds_iff.2
    refine ⟨1, one_pos, ?_⟩
    intro z hz
    change dist z p.2 < 1 at hz
    rw [show S = Metric.closedBall 0 R by rfl, Metric.mem_closedBall]
    calc
      dist z 0 ≤ dist z p.2 + dist p.2 0 := dist_triangle _ _ _
      _ ≤ 1 + ‖p.2‖ := by
        rw [dist_zero_right]
        simpa [add_comm] using (add_le_add_right hz.le ‖p.2‖)
      _ ≤ R := by
        dsimp [R]
        simpa [add_comm]
  let P : Set (ℝ × E3) := Icc (p.1 - δ) (p.1 + δ) ×ˢ S
  have hpP : p ∈ P := by
    refine ⟨?_, hpS⟩
    constructor <;> linarith [hδ]
  have hP_nhds : P ∈ 𝓝 p := by
    apply prod_mem_nhds
    · apply Icc_mem_nhds <;> linarith
    · exact hS_nhds
  have hδle : δ ≤ p.1 + δ := by linarith
  obtain ⟨g, hg, hg_nonneg, hdom⟩ :=
    compact_time_spatial_derivative_dominator δ (p.1 + δ) R hδ hδle hR
  have htime (q : ℝ × E3) (hq : q ∈ P) (s : ℝ)
      (hs : s ∈ uIcc (0 : ℝ) b) : q.1 - s ∈ Icc δ (p.1 + δ) := by
    rw [uIcc_of_le hb] at hs
    dsimp [P] at hq
    constructor
    · calc
        δ = p.1 - δ - b := by dsimp [δ]; ring
        _ ≤ q.1 - s := sub_le_sub hq.1.1 hs.2
    · calc
        q.1 - s ≤ (p.1 + δ) - 0 := sub_le_sub hq.1.2 hs.1
        _ = p.1 + δ := by ring
  let K : (ℝ × E3) → ℝ := fun q =>
    fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 q.1) z
      (EuclideanSpace.single i 1)) q.2 (EuclideanSpace.single j 1)
  have hK_formula (q : ℝ × E3)
      (hq : q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set E3)) :
      K q = (q.2 i * q.2 j / (4 * q.1 ^ 2) -
        (if i = j then 1 / (2 * q.1) else 0)) *
          euclideanHeatKernel 3 q.1 q.2 := by
    dsimp [K]
    exact euclideanHeatKernel_three_hessian_formula hq.1 q.2 i j
  have hK_formula_cont : ContinuousOn
      (fun q : ℝ × E3 =>
        (q.2 i * q.2 j / (4 * q.1 ^ 2) -
          (if i = j then 1 / (2 * q.1) else 0)) *
            euclideanHeatKernel 3 q.1 q.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
    have hkernel : ContinuousOn
        (fun q : ℝ × E3 => euclideanHeatKernel 3 q.1 q.2)
        (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) :=
      (euclideanHeatKernel_joint_smooth 3).continuousOn
    have hA : ContinuousOn
        (fun q : ℝ × E3 => q.2 i * q.2 j / (4 * q.1 ^ 2))
        (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro q hq
        have hq0 : 0 < q.1 := hq.1
        positivity
    have hB : ContinuousOn
        (fun q : ℝ × E3 => 1 / (2 * q.1))
        (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro q hq
        have hq0 : 0 < q.1 := hq.1
        positivity
    have hdiag : ContinuousOn
        (fun q : ℝ × E3 => if i = j then 1 / (2 * q.1) else 0)
        (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
      by_cases hij : i = j
      · simp only [if_pos hij]
        simpa [div_eq_mul_inv, mul_comm] using hB
      · simp only [if_neg hij]
        exact continuousOn_const
    exact (hA.sub hdiag).mul hkernel
  have hK_cont : ContinuousOn K
      (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
    exact hK_formula_cont.congr (fun q hq => hK_formula q hq)
  let Q : (ℝ × E3) → ℝ → E3 → ℝ := fun q s y =>
    K (q.1 - s, q.2 - y) * F (s, y)
  let I : (ℝ × E3) → ℝ → ℝ := fun q s => ∫ y : E3, Q q s y
  have hQ_meas (q : ℝ × E3) (hq : q ∈ P) (s : ℝ)
      (hs : s ∈ uIcc (0 : ℝ) b) :
      AEStronglyMeasurable (fun y : E3 => Q q s y) volume := by
    have hline : Continuous (fun y : E3 => (q.1 - s, q.2 - y)) := by
      fun_prop
    have hlineOn : ContinuousOn (fun y : E3 => (q.1 - s, q.2 - y))
        (univ : Set E3) := hline.continuousOn
    have hmap : MapsTo (fun y : E3 => (q.1 - s, q.2 - y)) (univ : Set E3)
        (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
      intro y hy
      exact ⟨lt_of_lt_of_le hδ (htime q hq s hs).1, mem_univ _⟩
    have hKlineOn := hK_cont.comp hlineOn hmap
    have hKline : Continuous (fun y : E3 => K (q.1 - s, q.2 - y)) := by
      simpa only [continuousOn_univ, Function.comp_def] using hKlineOn
    have hFline : Continuous (fun y : E3 => F (s, y)) := by
      exact F.continuous.comp (continuous_const.prodMk continuous_id)
    change AEStronglyMeasurable (fun y : E3 =>
      K (q.1 - s, q.2 - y) * F (s, y)) volume
    exact (hKline.mul hFline).aestronglyMeasurable
  have hQ_bound (q : ℝ × E3) (hq : q ∈ P) (s : ℝ)
      (hs : s ∈ uIcc (0 : ℝ) b) : ∀ᵐ y ∂volume,
        ‖Q q s y‖ ≤ ‖F‖ * g y := by
    filter_upwards [] with y
    have hh := hdom (q.1 - s) (htime q hq s hs) q.2 y (hball q.2 hq.2)
    have hK : |K (q.1 - s, q.2 - y)| ≤ g y := hh.2.2 i j
    have hF : |F (s, y)| ≤ ‖F‖ := by
      simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (s, y)
    rw [show ‖Q q s y‖ = |K (q.1 - s, q.2 - y) * F (s, y)| by
      simp [Q, Real.norm_eq_abs], abs_mul]
    calc
      |K (q.1 - s, q.2 - y)| * |F (s, y)| ≤ g y * ‖F‖ :=
        mul_le_mul hK hF (abs_nonneg _) (hg_nonneg y)
      _ = ‖F‖ * g y := by ring
  have hQ_cont_space (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) b) :
      ∀ᵐ y ∂volume, ContinuousOn (fun q : ℝ × E3 => Q q s y) P := by
    filter_upwards [] with y
    have hline : ContinuousOn (fun q : ℝ × E3 => (q.1 - s, q.2 - y)) P := by
      fun_prop
    have hmap : MapsTo (fun q : ℝ × E3 => (q.1 - s, q.2 - y)) P
        (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
      intro q hq
      exact ⟨lt_of_lt_of_le hδ (htime q hq s hs).1, mem_univ _⟩
    have hKline := hK_cont.comp hline hmap
    have hFline : ContinuousOn (fun q : ℝ × E3 => F (s, y)) P :=
      continuousOn_const
    exact (hKline.mul hFline).congr (fun q hq => rfl)
  have hI_space_contOn (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) b) :
      ContinuousOn (fun q : ℝ × E3 => I q s) P := by
    apply continuousOn_of_dominated (s := P)
    · intro q hq
      simpa [I] using hQ_meas q hq s hs
    · intro q hq
      simpa [I] using hQ_bound q hq s hs
    · exact hg.const_mul ‖F‖
    · exact hQ_cont_space s hs
  have hQ_cont_time (q : ℝ × E3) (hq : q ∈ P) :
      ∀ᵐ y ∂volume, ContinuousOn (fun s : ℝ => Q q s y)
        (uIcc (0 : ℝ) b) := by
    filter_upwards [] with y
    have hline : ContinuousOn (fun s : ℝ => (q.1 - s, q.2 - y))
        (uIcc (0 : ℝ) b) := by
      fun_prop
    have hmap : MapsTo (fun s : ℝ => (q.1 - s, q.2 - y))
        (uIcc (0 : ℝ) b) (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
      intro s hs
      exact ⟨lt_of_lt_of_le hδ (htime q hq s hs).1, mem_univ _⟩
    have hKline := hK_cont.comp hline hmap
    have hFline : ContinuousOn (fun s : ℝ => F (s, y))
        (uIcc (0 : ℝ) b) := by
      exact (F.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    exact (hKline.mul hFline).congr (fun s hs => rfl)
  have hI_time_contOn (q : ℝ × E3) (hq : q ∈ P) :
      ContinuousOn (I q) (uIcc (0 : ℝ) b) := by
    apply continuousOn_of_dominated (s := uIcc (0 : ℝ) b)
    · intro s hs
      simpa [I] using hQ_meas q hq s hs
    · intro s hs
      simpa [I] using hQ_bound q hq s hs
    · exact hg.const_mul ‖F‖
    · exact hQ_cont_time q hq
  have hI_meas : ∀ᶠ q in 𝓝 p,
      AEStronglyMeasurable (I q) (volume.restrict (uIoc (0 : ℝ) b)) := by
    filter_upwards [hP_nhds] with q hq
    have hcont := (hI_time_contOn q hq).mono uIoc_subset_uIcc
    exact hcont.aestronglyMeasurable measurableSet_uIoc
  have hI_bound : ∀ᶠ q in 𝓝 p, ∀ᵐ s ∂volume,
      s ∈ uIoc (0 : ℝ) b → ‖I q s‖ ≤ ∫ y : E3, ‖F‖ * g y := by
    filter_upwards [hP_nhds] with q hq
    filter_upwards [] with s
    intro hs
    have hs' : s ∈ uIcc (0 : ℝ) b := uIoc_subset_uIcc hs
    have hmajor : Integrable (fun y : E3 => ‖F‖ * g y) volume :=
      hg.const_mul ‖F‖
    have hnorm := norm_integral_le_of_norm_le hmajor (hQ_bound q hq s hs')
    simpa [I, Q] using hnorm
  have hI_cont : ∀ᵐ s ∂volume,
      s ∈ uIoc (0 : ℝ) b → ContinuousAt (fun q : ℝ × E3 => I q s) p := by
    filter_upwards [] with s hs
    have hs' : s ∈ uIcc (0 : ℝ) b := uIoc_subset_uIcc hs
    have hcont := (hI_space_contOn s hs').continuousWithinAt hpP
    exact hcont.continuousAt hP_nhds
  have houter := intervalIntegral.continuousAt_of_dominated_interval
    (μ := (volume : Measure ℝ)) (x₀ := p)
    (F := I) (bound := fun _ : ℝ => ∫ y : E3, ‖F‖ * g y)
    hI_meas hI_bound intervalIntegrable_const hI_cont
  exact houter.continuousWithinAt
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
