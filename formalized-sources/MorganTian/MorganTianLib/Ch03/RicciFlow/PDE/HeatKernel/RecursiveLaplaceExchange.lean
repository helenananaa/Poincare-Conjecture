import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveJointSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual coordinate Laplacian of convolution equals integral of the kernel Laplacian. -/
theorem euclideanHeatKernel_compact_laplace_integral (f : E3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {t : ℝ} (ht : 0 < t) (x : E3) :
    (∀ i : Fin 3, Integrable (fun y : E3 =>
      iteratedDeriv 2 (fun z : ℝ => euclideanHeatKernel 3 t
        (WithLp.toLp 2 (Function.update (WithLp.ofLp (x-y)) i z))) ((x-y) i) * f y) volume) ∧
    (∑ i : Fin 3, iteratedDeriv 2 (fun z : ℝ =>
      ∫ y : E3, euclideanHeatKernel 3 t
        (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i z) - y) * f y) (x i)) =
      ∫ y : E3, (∑ i : Fin 3, iteratedDeriv 2 (fun z : ℝ =>
        euclideanHeatKernel 3 t (WithLp.toLp 2 (Function.update (WithLp.ofLp (x-y)) i z))) ((x-y) i)) * f y :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hkernel : ContDiff ℝ ∞ (euclideanHeatKernel 3 t) :=
    (euclideanHeatKernel_three_heat_equation ht).1
  let ℓ : Fin 3 → E3 → ℝ → ℝ := fun i a z => euclideanHeatKernel 3 t
    (WithLp.toLp 2 (Function.update (WithLp.ofLp a) i z))
  have hcurve (i : Fin 3) (a : E3) :
      ℓ i a = (fun z : ℝ => gaussianHeatKernel t z *
        ∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t (a j)) := by
    funext z
    unfold ℓ euclideanHeatKernel
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j : Fin 3 => gaussianHeatKernel t
        ((Function.update (WithLp.ofLp a) i z) j)) (Finset.mem_univ i)]
    rw [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hline (a : E3) (i : Fin 3) :
      ContDiff ℝ ∞ (ℓ i a) := by
    rw [hcurve]
    exact (gaussianHeatKernel_derivatives ht).1.mul contDiff_const
  have hline_deriv (i : Fin 3) (a : E3) (z : ℝ) :
      deriv (ℓ i a) z = deriv (gaussianHeatKernel t) z *
        ∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t (a j) := by
    rw [hcurve, deriv_mul_const_field]
  have hline_second (i : Fin 3) (a : E3) (z : ℝ) :
      iteratedDeriv 2 (ℓ i a) z = iteratedDeriv 2 (gaussianHeatKernel t) z *
        ∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t (a j) := by
    rw [hcurve, iteratedDeriv_mul_const_field]
  have hshift (i : Fin 3) (z : ℝ) (y : E3) :
      ℓ i (x - y) (z - y i) = euclideanHeatKernel 3 t
        (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i z) - y) := by
    unfold ℓ
    congr 2
    ext j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [hji]
  let Q : Fin 3 → ℝ → E3 → ℝ := fun i z y => ℓ i (x - y) (z - y i)
  let Q₁ : Fin 3 → ℝ → E3 → ℝ := fun i z y =>
    deriv (ℓ i (x - y)) (z - y i)
  let Q₂ : Fin 3 → ℝ → E3 → ℝ := fun i z y =>
    iteratedDeriv 2 (ℓ i (x - y)) (z - y i)
  have hQ_eq (i : Fin 3) (z : ℝ) (y : E3) :
      Q i z y = euclideanHeatKernel 3 t
        (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i z) - y) := by
    exact hshift i z y
  have hQ_cont (i : Fin 3) :
      Continuous (fun p : ℝ × E3 => Q i p.1 p.2) := by
    simp only [Q, hcurve]
    have hprod : Continuous (fun p : ℝ × E3 =>
        ∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t ((x - p.2) j)) := by
      apply continuous_finsetProd
      intro j hj
      exact (gaussianHeatKernel_derivatives ht).1.continuous.comp (by fun_prop)
    exact ((gaussianHeatKernel_derivatives ht).1.continuous.comp (by fun_prop)).mul hprod
  have hQ₁_cont (i : Fin 3) :
      Continuous (fun p : ℝ × E3 => Q₁ i p.1 p.2) := by
    simp only [Q₁, hline_deriv]
    have hprod : Continuous (fun p : ℝ × E3 =>
        ∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t ((x - p.2) j)) := by
      apply continuous_finsetProd
      intro j hj
      exact (gaussianHeatKernel_derivatives ht).1.continuous.comp (by fun_prop)
    have hg1 : Continuous (deriv (gaussianHeatKernel t)) := by
      simpa only [iteratedDeriv_one] using
        (gaussianHeatKernel_derivatives ht).1.continuous_iteratedDeriv 1 (by simp)
    exact (hg1.comp (by fun_prop)).mul hprod
  have hQ₂_cont (i : Fin 3) :
      Continuous (fun p : ℝ × E3 => Q₂ i p.1 p.2) := by
    simp only [Q₂, hline_second]
    have hprod : Continuous (fun p : ℝ × E3 =>
        ∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t ((x - p.2) j)) := by
      apply continuous_finsetProd
      intro j hj
      exact (gaussianHeatKernel_derivatives ht).1.continuous.comp (by fun_prop)
    have hg2 : Continuous (iteratedDeriv 2 (gaussianHeatKernel t)) :=
      (gaussianHeatKernel_derivatives ht).1.continuous_iteratedDeriv 2
        (show (2 : ℕ∞ω) ≤ ∞ by
          exact WithTop.coe_le_coe.2 (show (2 : ℕ∞) ≤ ⊤ by exact le_top))
    exact (hg2.comp (by fun_prop)).mul hprod
  have hF_cont (i : Fin 3) :
      Continuous (fun p : ℝ × E3 => Q i p.1 p.2 * f p.2) := by
    exact (hQ_cont i).mul (hf.continuous.comp continuous_snd)
  have hF₁_cont (i : Fin 3) :
      Continuous (fun p : ℝ × E3 => Q₁ i p.1 p.2 * f p.2) := by
    exact (hQ₁_cont i).mul (hf.continuous.comp continuous_snd)
  have hF₂_cont (i : Fin 3) :
      Continuous (fun p : ℝ × E3 => Q₂ i p.1 p.2 * f p.2) := by
    exact (hQ₂_cont i).mul (hf.continuous.comp continuous_snd)
  have hInt (i : Fin 3) (z : ℝ) :
      Integrable (fun y : E3 => Q i z y * f y) volume := by
    apply (integrableOn_iff_integrable_of_support_subset (s := tsupport f) ?_).mp
    · exact (hF_cont i).comp (continuous_const.prodMk continuous_id) |>.continuousOn.integrableOn_compact hfc
    · refine Function.support_subset_iff'.2 ?_
      intro y hyt
      have hfy : f y = 0 := image_eq_zero_of_notMem_tsupport hyt
      simp [hfy]
  have hQ_deriv (i : Fin 3) (z : ℝ) (y : E3) :
      HasDerivAt (fun w : ℝ => Q i w y) (Q₁ i z y) z := by
    have hbase := (hline (x - y) i).differentiable (by simp) (z - y i)
    have hshift' := hbase.hasDerivAt.comp z ((hasDerivAt_id z).sub_const (y i))
    simpa [Q, Q₁, Function.comp_def] using hshift'
  have hQ₁_deriv (i : Fin 3) (z : ℝ) (y : E3) :
      HasDerivAt (fun w : ℝ => Q₁ i w y) (Q₂ i z y) z := by
    have hdiff := (hline (x - y) i).differentiable_iteratedDeriv 1 (by simp)
    have hbase := (hdiff (z - y i)).hasDerivAt
    have hbase' : HasDerivAt (fun w : ℝ => deriv (ℓ i (x - y)) w)
        (iteratedDeriv 2 (ℓ i (x - y)) (z - y i)) (z - y i) := by
      simpa only [iteratedDeriv_zero, iteratedDeriv_one,
        show (2 : ℕ) = 1 + 1 by norm_num,
        iteratedDeriv_succ] using hbase
    have hshift' := hbase'.comp z ((hasDerivAt_id z).sub_const (y i))
    simpa [Q₁, Q₂, Function.comp_def] using hshift'
  have hdom₁ (i : Fin 3) (a : ℝ) :
      ∃ C : ℝ, Integrable ((tsupport f).indicator (fun _ : E3 => C)) volume ∧
        ∀ z ∈ Metric.ball a 1, ∀ y : E3,
          ‖Q₁ i z y * f y‖ ≤ (tsupport f).indicator (fun _ : E3 => C) y := by
    obtain ⟨C, hC⟩ :=
      ((isCompact_closedBall a 1).prod hfc).exists_bound_of_continuousOn
        (f := fun p : ℝ × E3 => Q₁ i p.1 p.2 * f p.2) (hF₁_cont i).continuousOn
    refine ⟨C, ?_, ?_⟩
    · exact (integrableOn_const (s := tsupport f) (μ := volume) (C := C)
        hfc.measure_lt_top.ne).integrable_indicator
        hfc.measurableSet
    · intro z hz y
      by_cases hy : y ∈ tsupport f
      · rw [Set.indicator_of_mem hy]
        exact hC (z, y)
          ⟨(Metric.mem_closedBall'.2 (le_of_lt (Metric.mem_ball'.1 hz))), hy⟩
      · simp [hy, image_eq_zero_of_notMem_tsupport hy]
  have hdom₂ (i : Fin 3) (a : ℝ) :
      ∃ C : ℝ, Integrable ((tsupport f).indicator (fun _ : E3 => C)) volume ∧
        ∀ z ∈ Metric.ball a 1, ∀ y : E3,
          ‖Q₂ i z y * f y‖ ≤ (tsupport f).indicator (fun _ : E3 => C) y := by
    obtain ⟨C, hC⟩ :=
      ((isCompact_closedBall a 1).prod hfc).exists_bound_of_continuousOn
        (f := fun p : ℝ × E3 => Q₂ i p.1 p.2 * f p.2) (hF₂_cont i).continuousOn
    refine ⟨C, ?_, ?_⟩
    · exact (integrableOn_const (s := tsupport f) (μ := volume) (C := C)
        hfc.measure_lt_top.ne).integrable_indicator
        hfc.measurableSet
    · intro z hz y
      by_cases hy : y ∈ tsupport f
      · rw [Set.indicator_of_mem hy]
        exact hC (z, y)
          ⟨(Metric.mem_closedBall'.2 (le_of_lt (Metric.mem_ball'.1 hz))), hy⟩
      · simp [hy, image_eq_zero_of_notMem_tsupport hy]
  have hInt₁ (i : Fin 3) (z : ℝ) :
      Integrable (fun y : E3 => Q₁ i z y * f y) volume := by
    apply (integrableOn_iff_integrable_of_support_subset (s := tsupport f) ?_).mp
    · exact ContinuousOn.integrableOn_compact hfc
        ((hF₁_cont i).comp (continuous_const.prodMk continuous_id)).continuousOn
    · refine Function.support_subset_iff'.2 ?_
      intro y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
  have hInt₂ (i : Fin 3) (z : ℝ) :
      Integrable (fun y : E3 => Q₂ i z y * f y) volume := by
    apply (integrableOn_iff_integrable_of_support_subset (s := tsupport f) ?_).mp
    · exact ContinuousOn.integrableOn_compact hfc
        ((hF₂_cont i).comp (continuous_const.prodMk continuous_id)).continuousOn
    · refine Function.support_subset_iff'.2 ?_
      intro y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
  have hfirst (i : Fin 3) (a : ℝ) :
      HasDerivAt (fun z : ℝ => ∫ y : E3, Q i z y * f y)
        (∫ y : E3, Q₁ i a y * f y) a := by
    obtain ⟨C, hCint, hC⟩ := hdom₁ i a
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (𝕜 := ℝ) (E := ℝ) (α := E3) (μ := volume) (x₀ := a)
      (F := fun z : ℝ => fun y : E3 => Q i z y * f y)
      (F' := fun z y => Q₁ i z y * f y)
      (s := Metric.ball a 1) (bound := (tsupport f).indicator (fun _ : E3 => C))
      (Metric.ball_mem_nhds a zero_lt_one) ?_ ?_ ?_ ?_ ?_ ?_).2
    · filter_upwards with z
      exact (hF_cont i).comp (continuous_const.prodMk continuous_id) |>.aestronglyMeasurable
    · exact hInt i a
    · exact (hF₁_cont i).comp (continuous_const.prodMk continuous_id) |>.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun y z hz => hC z hz y)
    · exact hCint
    · filter_upwards with y z hz
      simpa using (hQ_deriv i z y).mul_const (f y)
  have hsecond (i : Fin 3) (a : ℝ) :
      HasDerivAt (fun z : ℝ => ∫ y : E3, Q₁ i z y * f y)
        (∫ y : E3, Q₂ i a y * f y) a := by
    obtain ⟨C, hCint, hC⟩ := hdom₂ i a
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (𝕜 := ℝ) (E := ℝ) (α := E3) (μ := volume) (x₀ := a)
      (F := fun z : ℝ => fun y : E3 => Q₁ i z y * f y)
      (F' := fun z y => Q₂ i z y * f y)
      (s := Metric.ball a 1) (bound := (tsupport f).indicator (fun _ : E3 => C))
      (Metric.ball_mem_nhds a zero_lt_one) ?_ ?_ ?_ ?_ ?_ ?_).2
    · filter_upwards with z
      exact (hF₁_cont i).comp (continuous_const.prodMk continuous_id) |>.aestronglyMeasurable
    · exact hInt₁ i a
    · exact (hF₂_cont i).comp (continuous_const.prodMk continuous_id) |>.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun y z hz => hC z hz y)
    · exact hCint
    · filter_upwards with y z hz
      simpa using (hQ₁_deriv i z y).mul_const (f y)
  have hraw_eq (i : Fin 3) :
      (fun z : ℝ => ∫ y : E3, euclideanHeatKernel 3 t
        (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i z) - y) * f y) =
        (fun z : ℝ => ∫ y : E3, Q i z y * f y) := by
    funext z
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y =>
      congrArg (fun u : ℝ => u * f y) (hQ_eq i z y).symm)
  have hI_second (i : Fin 3) :
      iteratedDeriv 2 (fun z : ℝ => ∫ y : E3, Q i z y * f y) (x i) =
        ∫ y : E3, Q₂ i (x i) y * f y := by
    have hderiv :
        deriv (fun z : ℝ => ∫ y : E3, Q i z y * f y) =
          (fun z : ℝ => ∫ y : E3, Q₁ i z y * f y) := by
      funext z
      exact (hfirst i z).deriv
    calc
      iteratedDeriv 2 (fun z : ℝ => ∫ y : E3, Q i z y * f y) (x i) =
          deriv (deriv (fun z : ℝ => ∫ y : E3, Q i z y * f y)) (x i) := by
            simpa only [iteratedDeriv_zero, show (2 : ℕ) = 1 + 1 by norm_num,
              iteratedDeriv_succ,
              iteratedDeriv_one]
      _ = deriv (fun z : ℝ => ∫ y : E3, Q₁ i z y * f y) (x i) := by
        rw [hderiv]
      _ = ∫ y : E3, Q₂ i (x i) y * f y := (hsecond i (x i)).deriv
  have hQ₂_target (i : Fin 3) (y : E3) :
      Q₂ i (x i) y = iteratedDeriv 2 (fun z : ℝ => euclideanHeatKernel 3 t
        (WithLp.toLp 2 (Function.update (WithLp.ofLp (x - y)) i z))) ((x - y) i) := by
    simp [Q₂, ℓ]
  have hsum_integral :
      (∑ i : Fin 3, ∫ y : E3, Q₂ i (x i) y * f y) =
        ∫ y : E3, ∑ i : Fin 3, Q₂ i (x i) y * f y := by
    symm
    simpa using
      (integral_finsetSum (μ := volume) Finset.univ
        (fun i _ => hInt₂ i (x i)))
  refine ⟨?_, ?_⟩
  · intro i
    simpa [Q₂, ℓ] using hInt₂ i (x i)
  · calc
      (∑ i : Fin 3, iteratedDeriv 2 (fun z : ℝ =>
          ∫ y : E3, euclideanHeatKernel 3 t
            (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i z) - y) * f y)
          (x i)) =
          ∑ i : Fin 3, ∫ y : E3, Q₂ i (x i) y * f y := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hraw_eq i]
            exact hI_second i
      _ = ∫ y : E3, ∑ i : Fin 3, Q₂ i (x i) y * f y := hsum_integral
      _ = ∫ y : E3, (∑ i : Fin 3,
          iteratedDeriv 2 (fun z : ℝ => euclideanHeatKernel 3 t
            (WithLp.toLp 2 (Function.update (WithLp.ofLp (x - y)) i z))) ((x - y) i)) * f y := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun y => by
              simp_rw [hQ₂_target]
              rw [Finset.sum_mul])
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
