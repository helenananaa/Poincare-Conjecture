import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ShiftedDerivativeDominator
import Mathlib.Analysis.Calculus.ParametricIntegral
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Full Frechet derivative of actual bounded-data heat convolution. -/
theorem bounded_heat_first_fderiv (f : E3 →ᵇ ℝ) {t : ℝ} (ht : 0 < t) (x : E3) :
    HasFDerivAt (fun z : E3 => ∫ y : E3, euclideanHeatKernel 3 t (z-y)*f y)
      (∑ i : Fin 3, (∫ y : E3, fderiv ℝ (euclideanHeatKernel 3 t) (x-y)
        (EuclideanSpace.single i 1)*f y) • (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i)) x :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let K : E3 → ℝ := euclideanHeatKernel 3 t
  let F : E3 → E3 → ℝ := fun z y => K (z - y) * f y
  let F' : E3 → E3 → E3 →L[ℝ] ℝ := fun z y =>
    (fderiv ℝ K (z - y)).smulRight (f y)
  obtain ⟨g, hg, hg_nonneg, hdom⟩ :=
    euclideanHeatKernel_three_shifted_derivative_dominator t (‖x‖ + 1) ht
      (by positivity)
  have hKdiff (z : E3) : HasFDerivAt K (fderiv ℝ K z) z := by
    exact ((euclideanHeatKernel_three_heat_equation ht).1.differentiable
      (by simp) z).hasFDerivAt
  have hKcont : Continuous K :=
    (euclideanHeatKernel_three_heat_equation ht).1.continuous
  have hKfderiv : Continuous (fderiv ℝ K) :=
    (euclideanHeatKernel_three_heat_equation ht).1.continuous_fderiv (by simp)
  have hball_norm (z : E3) (hz : z ∈ Metric.ball x 1) :
      ‖z‖ ≤ ‖x‖ + 1 := by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    calc
      ‖z‖ = ‖(z - x) + x‖ := by congr 1 <;> abel
      _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ 1 + ‖x‖ := by linarith
      _ = ‖x‖ + 1 := by ring
  have hcoord_expand (L : E3 →L[ℝ] ℝ) (v : E3) :
      L v = ∑ i : Fin 3, (L (EuclideanSpace.single i 1)) * v i := by
    have hv : v = ∑ i : Fin 3, v i • EuclideanSpace.single i 1 := by
      ext j
      fin_cases j <;> simp [Fin.sum_univ_succ]
    calc
      L v = L (∑ i : Fin 3, v i • EuclideanSpace.single i 1) := congrArg L hv
      _ = ∑ i : Fin 3, L (v i • EuclideanSpace.single i 1) := by rw [map_sum]
      _ = ∑ i : Fin 3, (L (EuclideanSpace.single i 1)) * v i := by
        simp only [map_smul, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hcoord_clm (L : E3 →L[ℝ] ℝ) :
      L = ∑ i : Fin 3, (L (EuclideanSpace.single i 1)) •
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) := by
    ext v
    rw [hcoord_expand]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      PiLp.proj_apply, smul_eq_mul]
  have hopnorm (L : E3 →L[ℝ] ℝ) :
      ‖L‖ ≤ ∑ i : Fin 3, |L (EuclideanSpace.single i 1)| := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [hcoord_expand]
    calc
      ‖∑ i : Fin 3, L (EuclideanSpace.single i 1) * v i‖ ≤
          ∑ i : Fin 3, ‖L (EuclideanSpace.single i 1) * v i‖ :=
        norm_sum_le _ _
      _ = ∑ i : Fin 3, |L (EuclideanSpace.single i 1)| * |v i| := by
        simp [Real.norm_eq_abs]
      _ ≤ ∑ i : Fin 3, |L (EuclideanSpace.single i 1)| * ‖v‖ := by
        apply Finset.sum_le_sum
        intro i hi
        gcongr
        simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le v i)
      _ = (∑ i : Fin 3, |L (EuclideanSpace.single i 1)|) * ‖v‖ := by
        rw [Finset.sum_mul]
  have hFcont (z : E3) : Continuous (F z) := by
    dsimp [F]
    exact (hKcont.comp (continuous_const.sub continuous_id)).mul f.continuous
  have hFmeas : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (F z) volume := by
    exact Eventually.of_forall (fun z => (hFcont z).aestronglyMeasurable)
  have hFint : Integrable (F x) volume := by
    apply (hg.const_mul ‖f‖).mono' (hFcont x).aestronglyMeasurable
    filter_upwards [] with y
    dsimp [F]
    rw [abs_mul]
    calc
      |K (x - y)| * |f y| ≤ g y * ‖f‖ := by
        exact mul_le_mul (hdom x y (by linarith)).1
          (f.norm_coe_le_norm y) (abs_nonneg _) (hg_nonneg y)
      _ = ‖f‖ * g y := by ring
  have hF'cont (z : E3) : Continuous (F' z) := by
    have hcomp : Continuous (fun y : E3 => fderiv ℝ K (z - y)) :=
      hKfderiv.comp (continuous_const.sub continuous_id)
    have hsmul : Continuous
        (fun p : (E3 →L[ℝ] ℝ) × ℝ => p.1.smulRight p.2) := by
      exact (ContinuousLinearMap.smulRightL ℝ E3 ℝ).continuous₂
    exact hsmul.comp (hcomp.prodMk f.continuous)
  have hF'meas : AEStronglyMeasurable (F' x) volume :=
    (hF'cont x).aestronglyMeasurable
  have hbound_int : Integrable
      (fun y : E3 => 3 * ‖f‖ * g y) volume := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hg.const_mul (3 * ‖f‖)
  have hbound : ∀ᵐ y : E3, ∀ z ∈ Metric.ball x 1,
      ‖F' z y‖ ≤ 3 * ‖f‖ * g y := by
    filter_upwards [] with y
    intro z hz
    have hz' := hball_norm z hz
    have hcoord (i : Fin 3) :
        |fderiv ℝ K (z - y) (EuclideanSpace.single i 1)| ≤ g y := by
      simpa [K] using (hdom z y hz' ).2.1 i
    have hsum :
        ∑ i : Fin 3, |fderiv ℝ K (z - y) (EuclideanSpace.single i 1)| ≤
          3 * g y := by
      calc
        ∑ i : Fin 3, |fderiv ℝ K (z - y) (EuclideanSpace.single i 1)| ≤
            ∑ i : Fin 3, g y := Finset.sum_le_sum (fun i hi => hcoord i)
        _ = 3 * g y := by simp
    dsimp [F']
    rw [ContinuousLinearMap.norm_smulRight_apply]
    calc
      ‖fderiv ℝ K (z - y)‖ * ‖f y‖ ≤
          (∑ i : Fin 3, |fderiv ℝ K (z - y)
            (EuclideanSpace.single i 1)|) * ‖f y‖ :=
        mul_le_mul_of_nonneg_right (hopnorm _) (norm_nonneg _)
      _ ≤ (3 * g y) * ‖f‖ := by
        calc
          (∑ i : Fin 3, |fderiv ℝ K (z - y)
              (EuclideanSpace.single i 1)|) * ‖f y‖ ≤
              (3 * g y) * ‖f y‖ :=
            mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
          _ ≤ (3 * g y) * ‖f‖ :=
            mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y)
              (mul_nonneg (by norm_num) (hg_nonneg y))
      _ = 3 * ‖f‖ * g y := by ring
  have hdiff : ∀ᵐ y : E3, ∀ z ∈ Metric.ball x 1,
      HasFDerivAt (F · y) (F' z y) z := by
    filter_upwards [] with y
    intro z hz
    have hcomp := (hKdiff (z - y)).comp z
      ((hasFDerivAt_id z).sub_const y)
    have hcomp' : HasFDerivAt (fun w : E3 => K (w - y))
        (fderiv ℝ K (z - y)) z := by
      simpa [Function.comp_def, ContinuousLinearMap.comp_id] using hcomp
    have hmul := hcomp'.mul_const (f y)
    change HasFDerivAt (fun w : E3 => K (w - y) * f y)
      ((fderiv ℝ K (z - y)).smulRight (f y)) z
    have heq : f y • fderiv ℝ K (z - y) =
        (fderiv ℝ K (z - y)).smulRight (f y) := by
      ext v
      simp [ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_comm]
    rw [← heq]
    exact hmul
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := (volume : Measure E3)) (F := F) (x₀ := x) (s := Metric.ball x 1)
      (bound := fun y : E3 => 3 * ‖f‖ * g y)
      (Metric.ball_mem_nhds x one_pos) hFmeas hFint hF'meas hbound hbound_int hdiff
  have hscalar_int (i : Fin 3) : Integrable
      (fun y : E3 => fderiv ℝ K (x - y) (EuclideanSpace.single i 1) * f y) volume := by
    have hdi : Integrable
        (fun y : E3 => fderiv ℝ K (x - y) (EuclideanSpace.single i 1)) volume := by
      apply hg.mono' ((hKfderiv.comp (continuous_const.sub continuous_id)).clm_apply
        continuous_const).aestronglyMeasurable
      filter_upwards [] with y
      simpa [Real.norm_eq_abs, K] using (hdom x y (by linarith)).2.1 i
    exact hdi.mul_bdd f.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => f.norm_coe_le_norm y))
  have hterm_int (i : Fin 3) : Integrable
      (fun y : E3 =>
        (fderiv ℝ K (x - y) (EuclideanSpace.single i 1) * f y) •
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i)) volume := by
    exact (hscalar_int i).smul_const _
  have hF'exp (y : E3) : F' x y = ∑ i : Fin 3,
      (fderiv ℝ K (x - y) (EuclideanSpace.single i 1) * f y) •
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) := by
    dsimp [F']
    have hL := hcoord_clm (fderiv ℝ K (x - y))
    calc
      (fderiv ℝ K (x - y)).smulRight (f y) =
          (∑ i : Fin 3, (fderiv ℝ K (x - y))
            (EuclideanSpace.single i 1) •
              (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i)).smulRight (f y) :=
        congrArg (fun L : E3 →L[ℝ] ℝ => L.smulRight (f y)) hL
      _ = ∑ i : Fin 3,
          (fderiv ℝ K (x - y) (EuclideanSpace.single i 1) * f y) •
            (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) := by
        ext v
        simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.sum_apply,
          ContinuousLinearMap.smul_apply, PiLp.proj_apply, smul_eq_mul]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hsum_integral :
      (∫ y : E3, F' x y) = ∑ i : Fin 3,
        (∫ y : E3, fderiv ℝ K (x - y) (EuclideanSpace.single i 1) * f y) •
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) := by
    calc
      (∫ y : E3, F' x y) =
          ∫ y : E3, ∑ i : Fin 3,
            (fderiv ℝ K (x - y) (EuclideanSpace.single i 1) * f y) •
              (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun y => hF'exp y)
      _ = ∑ i : Fin 3, ∫ y : E3,
            (fderiv ℝ K (x - y) (EuclideanSpace.single i 1) * f y) •
              (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) := by
        simpa using
          (integral_finsetSum (μ := (volume : Measure E3))
            (Finset.univ : Finset (Fin 3)) (fun i hi => hterm_int i))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_smul_const]
  have hderiv : HasFDerivAt
      (fun z : E3 => ∫ y : E3, euclideanHeatKernel 3 t (z - y) * f y)
      (∑ i : Fin 3,
        (∫ y : E3, fderiv ℝ (euclideanHeatKernel 3 t) (x-y)
          (EuclideanSpace.single i 1)*f y) •
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i)) x := by
    rw [← hsum_integral]
    simpa [F, K] using hmain
  exact hderiv
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
