import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.TimeDerivativeDominator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideBoundedHessianIdentification
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderHessianConvolutionThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianEstimate
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideHessianUnweighted
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GaussianNormForm
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HeatTimeDerivativeL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalInitialTrace
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ShiftedDerivativeDominator
import Mathlib.Analysis.Calculus.ParametricIntegral
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual time derivative of bounded-data convolution equals its spatial Laplacian. -/
theorem bounded_heat_time_equation (f : E3 →ᵇ ℝ) {t : ℝ} (ht : 0 < t) (x : E3) :
    let u : ℝ → E3 → ℝ := fun s z => ∫ y : E3, euclideanHeatKernel 3 s (z-y)*f y
    HasDerivAt (fun s => u s x)
      (∑ i : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ (u t) z
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) t :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  dsimp
  let K : ℝ → E3 → ℝ := fun s z => euclideanHeatKernel 3 s z
  let F : ℝ → E3 → ℝ := fun s y => K s (x - y) * f y
  let F' : ℝ → E3 → ℝ := fun s y =>
    deriv (fun r => K r (x - y)) s * f y
  obtain ⟨g, hg, hg_nonneg, hdom⟩ :=
    euclideanHeatKernel_time_derivative_dominator (t / 2) (3 * t / 2) ‖x‖
      (by positivity) (by linarith) (norm_nonneg x)
  have hKcont (s : ℝ) (hs : 0 < s) : Continuous (K s) := by
    simpa [K] using (euclideanHeatKernel_three_heat_equation hs).1.continuous
  have hFcont (s : ℝ) (hs : 0 < s) : Continuous (F s) := by
    dsimp [F]
    exact (hKcont s hs).comp (continuous_const.sub continuous_id) |>.mul f.continuous
  let hS : Set ℝ := Ioo (t / 2) (3 * t / 2)
  have hSnhds : hS ∈ 𝓝 t := by
    dsimp [hS]
    apply Ioo_mem_nhds <;> linarith
  have hSpos (s : ℝ) (hs : s ∈ hS) : 0 < s := by
    dsimp [hS] at hs
    exact lt_trans (by positivity) hs.1
  have hSJ (s : ℝ) (hs : s ∈ hS) : s ∈ Icc (t / 2) (3 * t / 2) := by
    exact ⟨hs.1.le, hs.2.le⟩
  have hFmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) volume := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (hFcont s hs).aestronglyMeasurable
  have hFint : Integrable (F t) volume := by
    apply (hg.const_mul ‖f‖).mono' (hFcont t ht).aestronglyMeasurable
    filter_upwards [] with y
    dsimp [F]
    rw [abs_mul]
    calc
      |K t (x - y)| * |f y| ≤ g y * ‖f‖ :=
        mul_le_mul (hdom t x y ⟨by linarith, by linarith⟩ (le_refl _)).1
          (f.norm_coe_le_norm y) (abs_nonneg _) (hg_nonneg y)
      _ = ‖f‖ * g y := by ring
  have hderivcont : Continuous
      (fun y : E3 => deriv (fun s => K s (x - y)) t) := by
    have heq : (fun y : E3 => deriv (fun s => K s (x - y)) t) =
        (fun y : E3 =>
          (‖x - y‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t)) * K t (x - y)) := by
      funext y
      exact (euclideanHeatKernel_three_time_formula ht (x - y)).deriv
    rw [heq]
    have hc : Continuous (fun y : E3 =>
        ‖x - y‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t)) := by fun_prop
    exact hc.mul ((hKcont t ht).comp (continuous_const.sub continuous_id))
  have hF'meas : AEStronglyMeasurable (F' t) volume := by
    change AEStronglyMeasurable
      (fun y : E3 => deriv (fun s => K s (x - y)) t * f y) volume
    exact (hderivcont.mul f.continuous).aestronglyMeasurable
  have hbound_int : Integrable (fun y : E3 => ‖f‖ * g y) volume :=
    hg.const_mul ‖f‖
  have hbound : ∀ᵐ y : E3, ∀ s ∈ hS,
      ‖F' s y‖ ≤ ‖f‖ * g y := by
    filter_upwards [] with y s hs
    dsimp [F']
    rw [abs_mul]
    calc
      |deriv (fun r => K r (x - y)) s| * |f y| ≤ g y * ‖f‖ :=
        mul_le_mul (hdom s x y (hSJ s hs) (le_refl _)).2
          (f.norm_coe_le_norm y) (abs_nonneg _) (hg_nonneg y)
      _ = ‖f‖ * g y := by ring
  have hdiff : ∀ᵐ y : E3, ∀ s ∈ hS,
      HasDerivAt (fun r => F r y) (F' s y) s := by
    filter_upwards [] with y s hs
    have hformula : deriv (fun r => K r (x - y)) s =
        (‖x - y‖ ^ 2 / (4 * s ^ 2) - 3 / (2 * s)) * K s (x - y) := by
      simpa [K] using (euclideanHeatKernel_three_time_formula (hSpos s hs)
        (x - y)).deriv
    have h := (euclideanHeatKernel_three_time_formula (hSpos s hs) (x - y)).mul_const
      (f y)
    rw [← hformula] at h
    simpa [F, F', K] using h
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure E3)) (F := F) (x₀ := t) (s := hS)
      (bound := fun y : E3 => ‖f‖ * g y)
      hSnhds hFmeas hFint hF'meas hbound hbound_int hdiff
  let H : Fin 3 → E3 → ℝ := fun i z =>
    fderiv ℝ (fun w : E3 => fderiv ℝ (euclideanHeatKernel 3 t) w
      (EuclideanSpace.single i 1)) z (EuclideanSpace.single i 1)
  have hdiag (z : E3) (i : Fin 3) : H i z =
      ((z i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * K t z := by
    dsimp [H, K]
    simpa [pow_two] using euclideanHeatKernel_three_hessian_formula ht z i i
  have htime (z : E3) :
      deriv (fun s => K s z) t = ∑ i : Fin 3, H i z := by
    have hformula := (euclideanHeatKernel_three_time_formula ht z).deriv
    calc
      deriv (fun s => K s z) t =
          (‖z‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t)) * K t z := by
            simpa [K] using hformula
      _ = (∑ i : Fin 3, ((z i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * K t z := by
        rw [EuclideanSpace.real_norm_sq_eq]
        congr 1
        rw [Finset.sum_sub_distrib, Finset.sum_div]
        have hconst : (∑ i : Fin 3, (1 : ℝ) / (2 * t)) = 3 / (2 * t) := by
          simp
          ring
        rw [hconst]
      _ = ∑ i : Fin 3, H i z := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        exact (hdiag z i).symm
  obtain ⟨C, hC, hHL1⟩ := euclideanHeatKernel_three_hessian_L1
  have hterm_int (i : Fin 3) : Integrable (fun y : E3 => H i (x - y) * f y) volume := by
    have hHi : Integrable (H i) volume := by
      simpa [H] using (hHL1 t ht i i).1
    have hshift : Integrable (fun y : E3 => H i (x - y)) volume := by
      have hm := (Measure.measurePreserving_sub_left (volume : Measure E3) x).integrable_comp_of_integrable hHi
      simpa [Function.comp_def] using hm
    exact hshift.mul_bdd f.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => f.norm_coe_le_norm y))
  have hsum_int : Integrable (fun y : E3 =>
      ∑ i : Fin 3, H i (x - y) * f y) volume := by
    exact integrable_finsetSum Finset.univ (fun i hi => hterm_int i)
  have htime_int :
      (∫ y : E3, deriv (fun s => K s (x - y)) t * f y) =
        ∑ i : Fin 3, ∫ y : E3, H i (x - y) * f y := by
    calc
      (∫ y : E3, deriv (fun s => K s (x - y)) t * f y) =
          ∫ y : E3, (∑ i : Fin 3, H i (x - y)) * f y := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun y => by
              change deriv (fun s => K s (x - y)) t * f y =
                (∑ i : Fin 3, H i (x - y)) * f y
              rw [htime])
      _ = ∫ y : E3, ∑ i : Fin 3, H i (x - y) * f y := by
            congr 1
            funext y
            rw [Finset.sum_mul]
      _ = ∑ i : Fin 3, ∫ y : E3, H i (x - y) * f y := by
            simpa using (integral_finsetSum (μ := (volume : Measure E3))
              Finset.univ (fun i hi => hterm_int i))
  have hchange (i : Fin 3) :
      (∫ y : E3, H i (x - y) * f y) =
        ∫ y : E3, H i y * f (x - y) := by
    rw [← integral_sub_left_eq_self (fun z : E3 => H i z * f (x - z)) volume x]
    congr 1
    funext y
    congr 2
    abel
  have hident (i : Fin 3) :
      fderiv ℝ (fun z : E3 => fderiv ℝ
        (fun w : E3 => ∫ y : E3, K t (w - y) * f y) z
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) =
        ∫ y : E3, H i y * f (x - y) := by
    simpa [K, H] using
      (euclideanHeatKernel_bounded_hessian_identification f ht).2 x i i
  have hcoef :
      (∫ y : E3, deriv (fun s => K s (x - y)) t * f y) =
        ∑ i : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ
          (fun w : E3 => ∫ y : E3, K t (w - y) * f y) z
            (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) := by
    calc
      (∫ y : E3, deriv (fun s => K s (x - y)) t * f y) =
          ∑ i : Fin 3, ∫ y : E3, H i (x - y) * f y := htime_int
      _ = ∑ i : Fin 3, ∫ y : E3, H i y * f (x - y) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hchange i
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hident i).symm
  have hder := hmain.2
  have hder' : HasDerivAt (fun s =>
      ∫ y : E3, K s (x - y) * f y)
      (∫ y : E3, deriv (fun r => K r (x - y)) t * f y) t := by
    simpa [F, F', K] using hder
  rw [hcoef] at hder'
  exact hder'
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
