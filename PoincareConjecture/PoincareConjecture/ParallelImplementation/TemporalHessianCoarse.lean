import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.GaussianHessianTimeDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianEstimate
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.TemporalHessianCoarse
open MorganTianLib.MetricCoefficient
open Set MeasureTheory
open scoped Topology
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Global weighted time-difference estimate, with no comparability restriction. -/
theorem heatHessian_time_difference_coarse
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t h : ℝ, 0 < t → 0 ≤ h → ∀ i j : Fin 3,
      Integrable (fun y : E3 =>
        |heatHessian3 (t+h) i j y - heatHessian3 t i j y| * ‖y‖^alpha) volume ∧
      (∫ y : E3, |heatHessian3 (t+h) i j y - heatHessian3 t i j y| * ‖y‖^alpha) ≤
        C * t^(alpha/2-1) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C, hC, hrecursive⟩ :=
    MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_weighted_hessian_recursive
      alpha ha ha1
  refine ⟨2 * C, by positivity, ?_⟩
  intro t h ht hh i j
  have htph : 0 < t + h := by linarith
  have httph : t ≤ t + h := by linarith
  obtain ⟨hIph, hBph⟩ := hrecursive (t + h) htph i j
  obtain ⟨hIt, hBt⟩ := hrecursive t ht i j
  let fph : E3 → ℝ := fun y => |heatHessian3 (t + h) i j y| * ‖y‖ ^ alpha
  let ft : E3 → ℝ := fun y => |heatHessian3 t i j y| * ‖y‖ ^ alpha
  let fd : E3 → ℝ := fun y =>
    |heatHessian3 (t + h) i j y - heatHessian3 t i j y| * ‖y‖ ^ alpha
  have hIph' : Integrable fph volume := by simpa [fph, heatHessian3] using hIph
  have hIt' : Integrable ft volume := by simpa [ft, heatHessian3] using hIt
  have hBph' : (∫ y, fph y ∂volume) ≤ C * (t + h) ^ (alpha / 2 - 1) := by
    simpa [fph, heatHessian3] using hBph
  have hBt' : (∫ y, ft y ∂volume) ≤ C * t ^ (alpha / 2 - 1) := by
    simpa [ft, heatHessian3] using hBt
  have hheat_meas (s : ℝ) (a b : Fin 3) :
      Measurable (fun y : E3 => heatHessian3 s a b y) := by
    unfold heatHessian3
    exact measurable_fderiv_apply_const ℝ
      (fun z => (fderiv ℝ (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 s) z)
        (EuclideanSpace.single a 1)) (EuclideanSpace.single b 1)
  have hfd_meas : Measurable fd := by
    dsimp [fd]
    exact ((hheat_meas (t + h) i j).sub (hheat_meas t i j)).abs.mul
      (measurable_norm.pow_const alpha)
  have hfd_le (y : E3) : fd y ≤ fph y + ft y := by
    have hw : 0 ≤ ‖y‖ ^ alpha := Real.rpow_nonneg (norm_nonneg y) alpha
    dsimp [fd, fph, ft]
    calc
      |heatHessian3 (t + h) i j y - heatHessian3 t i j y| * ‖y‖ ^ alpha
          ≤ (|heatHessian3 (t + h) i j y| + |heatHessian3 t i j y|) * ‖y‖ ^ alpha :=
            mul_le_mul_of_nonneg_right (by
              calc
                |heatHessian3 (t + h) i j y - heatHessian3 t i j y| =
                    |heatHessian3 (t + h) i j y + -heatHessian3 t i j y| := by rw [sub_eq_add_neg]
                _ ≤ |heatHessian3 (t + h) i j y| + |-heatHessian3 t i j y| := abs_add_le _ _
                _ = |heatHessian3 (t + h) i j y| + |heatHessian3 t i j y| := by rw [abs_neg]) hw
      _ = |heatHessian3 (t + h) i j y| * ‖y‖ ^ alpha +
            |heatHessian3 t i j y| * ‖y‖ ^ alpha := by ring
  have hfd_norm_le (y : E3) : ‖fd y‖ ≤ fph y + ft y := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hfd_le y
    · dsimp [fd]
      exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (norm_nonneg y) alpha)
  have hsum : Integrable (fun y : E3 => fph y + ft y) volume := hIph'.add hIt'
  have hId : Integrable fd volume :=
    hsum.mono' hfd_meas.aestronglyMeasurable (Filter.Eventually.of_forall hfd_norm_le)
  have hInt : (∫ y, fd y ∂volume) ≤ (∫ y, fph y ∂volume) + (∫ y, ft y ∂volume) := by
    calc
      (∫ y, fd y ∂volume) ≤ ∫ y, (fph y + ft y) ∂volume :=
        integral_mono hId hsum hfd_le
      _ = (∫ y, fph y ∂volume) + (∫ y, ft y ∂volume) := integral_add hIph' hIt'
  constructor
  · simpa [fd] using hId
  · change (∫ y, fd y ∂volume) ≤ (2 * C) * t ^ (alpha / 2 - 1)
    have hexp : alpha / 2 - 1 ≤ 0 := by linarith
    have hpow : (t + h) ^ (alpha / 2 - 1) ≤ t ^ (alpha / 2 - 1) :=
      Real.rpow_le_rpow_of_nonpos ht httph hexp
    calc
      (∫ y, fd y ∂volume) ≤ (∫ y, fph y ∂volume) + (∫ y, ft y ∂volume) := hInt
      _ ≤ C * (t + h) ^ (alpha / 2 - 1) + C * t ^ (alpha / 2 - 1) :=
        add_le_add hBph' hBt'
      _ ≤ C * t ^ (alpha / 2 - 1) + C * t ^ (alpha / 2 - 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hpow hC.le) le_rfl
      _ = (2 * C) * t ^ (alpha / 2 - 1) := by ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.TemporalHessianCoarse
