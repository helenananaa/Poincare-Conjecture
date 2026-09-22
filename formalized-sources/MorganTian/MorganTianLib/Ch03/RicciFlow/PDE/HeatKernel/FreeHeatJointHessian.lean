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
/-- Positive-time Hessian integrals of actual bounded initial data are jointly continuous. -/
theorem free_heat_joint_hessian_continuity (f : E3 →ᵇ ℝ) (i j : Fin 3) :
    ContinuousOn (fun p : ℝ × E3 => ∫ y : E3,
      fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 p.1) z
        (EuclideanSpace.single i 1)) (p.2-y) (EuclideanSpace.single j 1)*f y)
      (Ioi (0:ℝ) ×ˢ (univ : Set E3)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  rintro ⟨t₀, x₀⟩ hp
  have ht₀ : 0 < t₀ := hp.1
  let a : ℝ := t₀ / 2
  let b : ℝ := 3 * t₀ / 2
  let R : ℝ := ‖x₀‖ + 1
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  obtain ⟨g, hg, hg_nonneg, hdom⟩ :=
    compact_time_spatial_derivative_dominator a b R ha hab hR
  let s : Set (ℝ × E3) := Icc a b ×ˢ Metric.closedBall 0 R
  have hp₀ : (t₀, x₀) ∈ s := by
    constructor
    · constructor <;> dsimp [a, b] <;> linarith
    · rw [Metric.mem_closedBall, dist_zero_right]
      dsimp [R]
      exact le_add_of_nonneg_right (by norm_num)
  have hs_nhds : s ∈ 𝓝 (t₀, x₀) := by
    have hopen : IsOpen (Ioo a b ×ˢ Metric.ball x₀ 1) :=
      isOpen_Ioo.prod Metric.isOpen_ball
    have hopen_mem : (t₀, x₀) ∈ Ioo a b ×ˢ Metric.ball x₀ 1 := by
      constructor
      · constructor <;> dsimp [a, b] <;> linarith
      · exact Metric.mem_ball_self one_pos
    apply Filter.mem_of_superset (hopen.mem_nhds hopen_mem)
    intro p hp'
    constructor
    · exact ⟨le_of_lt hp'.1.1, le_of_lt hp'.1.2⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      calc
        ‖p.2‖ ≤ ‖p.2 - x₀‖ + ‖x₀‖ := by
          simpa [sub_add_cancel] using norm_add_le (p.2 - x₀) x₀
        _ = dist p.2 x₀ + ‖x₀‖ := by rw [dist_eq_norm]
        _ ≤ 1 + ‖x₀‖ := by
          linarith [Metric.mem_ball.mp hp'.2]
        _ = R := by dsimp [R]; ring
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
  let F : (ℝ × E3) → E3 → ℝ := fun p y => K (p.1, p.2 - y) * f y
  have hF_meas (p : ℝ × E3) (hp : p ∈ s) :
      AEStronglyMeasurable (F p) volume := by
    have hline : Continuous (fun y : E3 => (p.1, p.2 - y)) := by
      fun_prop
    have hlineOn : ContinuousOn (fun y : E3 => (p.1, p.2 - y))
        (univ : Set E3) := hline.continuousOn
    have hmap : MapsTo (fun y : E3 => (p.1, p.2 - y)) (univ : Set E3)
        (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
      intro y hy
      exact ⟨lt_of_lt_of_le ha hp.1.1, mem_univ _⟩
    have hKlineOn := hK_cont.comp hlineOn hmap
    have hKline : Continuous (fun y : E3 => K (p.1, p.2 - y)) := by
      simpa only [continuousOn_univ, Function.comp_def] using hKlineOn
    dsimp [F]
    have hEq : (fun y : E3 => K (p.1, p.2 - y) * f y) =
        (fun y : E3 => K (p.1, p.2 - y)) * f := by
      funext y
      rfl
    rw [hEq]
    exact (hKline.mul f.continuous).aestronglyMeasurable
  have hF_bound (p : ℝ × E3) (hp : p ∈ s) :
      ∀ᵐ y ∂volume, ‖F p y‖ ≤ ‖f‖ * g y := by
    filter_upwards [] with y
    have hxy : ‖p.2‖ ≤ R := by
      simpa [s, Metric.mem_closedBall, dist_zero_right] using hp.2
    have hh := hdom p.1 hp.1 p.2 y hxy
    have hK : |K (p.1, p.2 - y)| ≤ g y := by
      dsimp [K]
      exact hh.2.2 i j
    have hf : |f y| ≤ ‖f‖ := by
      simpa [Real.norm_eq_abs] using f.norm_coe_le_norm y
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |K (p.1, p.2 - y)| * |f y| ≤ g y * ‖f‖ :=
        mul_le_mul hK hf (abs_nonneg _) (hg_nonneg y)
      _ = ‖f‖ * g y := by ring
  have hF_cont : ∀ᵐ y ∂volume, ContinuousOn (fun p : ℝ × E3 => F p y) s := by
    filter_upwards [] with y
    have hline : Continuous (fun p : ℝ × E3 => (p.1, p.2 - y)) := by
      fun_prop
    have hlineOn : ContinuousOn (fun p : ℝ × E3 => (p.1, p.2 - y)) s :=
      hline.continuousOn
    have hmap : MapsTo (fun p : ℝ × E3 => (p.1, p.2 - y)) s
        (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
      intro p hp
      exact ⟨lt_of_lt_of_le ha hp.1.1, mem_univ _⟩
    have hKline := hK_cont.comp hlineOn hmap
    dsimp [F]
    have hEq : (fun p : ℝ × E3 => K (p.1, p.2 - y) * f y) =
        (fun p : ℝ × E3 => K (p.1, p.2 - y)) *
          (fun _ : ℝ × E3 => f y) := by
      funext p
      rfl
    rw [hEq]
    exact hKline.mul (continuousOn_const : ContinuousOn (fun _ : ℝ × E3 => f y) s)
  have hInt : ContinuousOn (fun p : ℝ × E3 => ∫ y : E3, F p y) s := by
    apply continuousOn_of_dominated (s := s)
    · exact hF_meas
    · exact hF_bound
    · exact hg.const_mul ‖f‖
    · exact hF_cont
  have hAt : ContinuousAt (fun p : ℝ × E3 => ∫ y : E3, F p y) (t₀, x₀) :=
    (hInt.continuousWithinAt hp₀).continuousAt hs_nhds
  simpa [F, K] using hAt.continuousWithinAt
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
