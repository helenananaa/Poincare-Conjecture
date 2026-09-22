import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveJointSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursivePolynomialMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderHessianConvolutionThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHolderControl
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Translation continuity with the actual L1 smoothing rate. -/
theorem euclideanHeatKernel_three_translation_L1 :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ h : E3,
      Integrable (fun y : E3 => euclideanHeatKernel 3 t (y+h)-euclideanHeatKernel 3 t y) volume ∧
      (∫ y : E3, |euclideanHeatKernel 3 t (y+h)-euclideanHeatKernel 3 t y|)
        ≤ min 2 (C*‖h‖/Real.sqrt t) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨Cg, hCg, hgrad⟩ := euclideanHeatKernel_three_gradient_L1
  let C : ℝ := 3 * Cg
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro t ht h
  let K : E3 → ℝ := euclideanHeatKernel 3 t
  obtain ⟨hKint, hKmass⟩ := (euclideanHeatKernel_mass_semigroup 3).1 t ht
  have hKcont : Continuous K := by
    dsimp [K]
    unfold euclideanHeatKernel
    exact (contDiff_prod (fun k _ =>
      (gaussianHeatKernel_derivatives ht).1.comp (by fun_prop))).continuous
  have hKsmooth : ContDiff ℝ ∞ K := by
    dsimp [K]
    exact (euclideanHeatKernel_three_heat_equation ht).1
  have hKshift : Integrable (fun y : E3 => K (y + h)) volume := by
    have hh := (measurePreserving_add_right (volume : Measure E3) h).integrable_comp_of_integrable
      hKint
    simpa [K, Function.comp_def] using hh
  have hdiff : Integrable (fun y : E3 => K (y + h) - K y) volume :=
    hKshift.sub (by simpa [K] using hKint)
  have habs : Integrable (fun y : E3 => |K (y + h) - K y|) volume := by
    simpa [Real.norm_eq_abs] using hdiff.norm
  have hsum : Integrable (fun y : E3 => K (y + h) + K y) volume :=
    hKshift.add (by simpa [K] using hKint)
  have hpoint_mass (y : E3) :
      |K (y + h) - K y| ≤ K (y + h) + K y := by
    calc
      |K (y + h) - K y| ≤ |K (y + h)| + |K y| := abs_sub _ _
      _ = K (y + h) + K y := by
        rw [abs_of_pos (euclideanHeatKernel_pos 3 ht (y + h)),
          abs_of_pos (euclideanHeatKernel_pos 3 ht y)]
  have hshift_integral : (∫ y : E3, K (y + h)) = ∫ y : E3, K y := by
    simpa [Function.comp_def] using
      (measurePreserving_add_right (volume : Measure E3) h).integral_comp
        (measurableEmbedding_addRight h) K
  have hmass_bound :
      (∫ y : E3, |K (y + h) - K y|) ≤ 2 := by
    have hi := integral_mono habs hsum hpoint_mass
    rw [integral_add hKshift (by simpa [K] using hKint), hshift_integral,
      hKmass] at hi
    norm_num at hi
    exact hi
  let D : Fin 3 → E3 → ℝ := fun i y =>
    fderiv ℝ (euclideanHeatKernel 3 t) y (EuclideanSpace.single i 1)
  have hD_formula (i : Fin 3) (y : E3) :
      D i y = -(y i / (2 * t)) * euclideanHeatKernel 3 t y := by
    dsimp [D]
    exact euclideanHeatKernel_three_gradient_formula ht y i
  have hDcont (i : Fin 3) : Continuous (D i) := by
    rw [show D i = (fun y : E3 =>
        -(y i / (2 * t)) * euclideanHeatKernel 3 t y) from
      funext (hD_formula i)]
    have hc : Continuous (fun y : E3 => -(y i / (2 * t))) := by fun_prop
    exact hc.mul hKcont
  have hDint (i : Fin 3) : Integrable (fun y : E3 => |D i y|) volume := by
    simpa [D, Real.norm_eq_abs] using (hgrad t ht i).1.norm
  let F : Fin 3 → ℝ × E3 → ℝ := fun i z => |D i (z.2 + z.1 • h)|
  have hFcont (i : Fin 3) : Continuous (F i) := by
    dsimp [F]
    exact (hDcont i).abs.comp (by fun_prop)
  have hFslice (i : Fin 3) (s : ℝ) :
      Integrable (fun y : E3 => F i (s, y)) volume := by
    have hh := (measurePreserving_add_right (volume : Measure E3) (s • h)).integrable_comp_of_integrable
      (hDint i)
    simpa [F, Function.comp_def] using hh
  have hFinner (i : Fin 3) (s : ℝ) :
      (∫ y : E3, F i (s, y)) = ∫ y : E3, |D i y| := by
    have hh := (measurePreserving_add_right (volume : Measure E3) (s • h)).integral_comp
      (measurableEmbedding_addRight (s • h)) (fun y : E3 => |D i y|)
    simpa [F, Function.comp_def] using hh
  have hFprod (i : Fin 3) :
      Integrable (F i)
        ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume : Measure E3)) := by
    apply (integrable_prod_iff (hFcont i).aestronglyMeasurable).2
    refine ⟨Filter.Eventually.of_forall (hFslice i), ?_⟩
    have heq :
        (fun s : ℝ => ∫ y : E3, ‖F i (s, y)‖) =
          (fun _ : ℝ => ∫ y : E3, |D i y|) := by
      funext s
      simpa [F, Real.norm_eq_abs] using hFinner i s
    rw [heq]
    exact (integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) 1)
      (C := ∫ y : E3, |D i y|) (by simp)).integrable
  have hFinner_integrable (i : Fin 3) :
      Integrable (fun y : E3 => ∫ s in (0 : ℝ)..1, F i (s, y)) volume := by
    have hh := (hFprod i).swap.integral_norm_prod_left
    simpa [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
      F, Real.norm_eq_abs, abs_nonneg, Function.comp_def] using hh
  have hFswap (i : Fin 3) :
      (∫ y : E3, ∫ s in (0 : ℝ)..1, F i (s, y)) =
        ∫ s in (0 : ℝ)..1, ∫ y : E3, F i (s, y) := by
    symm
    apply intervalIntegral_integral_swap
    rw [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact (hFprod i).congr (Filter.Eventually.of_forall (fun z => by
      change F i z = F i (z.1, z.2)
      rw [Prod.eta z]))
  let B : ℝ × E3 → ℝ := fun z =>
    ∑ i : Fin 3, |h i| * F i z
  have hBprod :
      Integrable B ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume : Measure E3)) := by
    dsimp [B]
    apply integrable_finsetSum Finset.univ
    intro i hi
    exact (hFprod i).const_mul _
  have hBinner (s : ℝ) :
      (∫ y : E3, B (s, y)) =
        ∑ i : Fin 3, |h i| * (∫ y : E3, F i (s, y)) := by
    calc
      (∫ y : E3, B (s, y)) =
          ∑ i : Fin 3, ∫ y : E3, |h i| * F i (s, y) := by
        dsimp [B]
        simpa using
          (integral_finsetSum (μ := volume) (Finset.univ : Finset (Fin 3))
            (fun i hi => (hFslice i s).const_mul (|h i|)))
      _ = ∑ i : Fin 3, |h i| * (∫ y : E3, F i (s, y)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_const_mul]
  have hBinner_eq :
      (fun s : ℝ => ∫ y : E3, B (s, y)) =
        (fun _ : ℝ => ∑ i : Fin 3, |h i| * (∫ y : E3, |D i y|)) := by
    funext s
    rw [hBinner s]
    congr 1
    funext i
    rw [hFinner i s]
  have hBswap :
      (∫ y : E3, ∫ s in (0 : ℝ)..1, B (s, y)) =
        ∫ s in (0 : ℝ)..1, ∫ y : E3, B (s, y) := by
    symm
    apply intervalIntegral_integral_swap
    rw [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact hBprod.congr (Filter.Eventually.of_forall (fun z => by
      change B z = B (z.1, z.2)
      rw [Prod.eta z]))
  have hBnonneg (z : ℝ × E3) : 0 ≤ B z := by
    dsimp [B]
    positivity
  have hBint : Integrable
      (fun y : E3 => ∫ s in (0 : ℝ)..1, B (s, y)) volume := by
    have hh := hBprod.swap.integral_norm_prod_left
    simpa [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
      B, Real.norm_eq_abs, abs_of_nonneg, hBnonneg, Function.comp_def] using hh
  have hB_integral :
      (∫ y : E3, ∫ s in (0 : ℝ)..1, B (s, y)) =
        ∑ i : Fin 3, |h i| * (∫ y : E3, |D i y|) := by
    rw [hBswap, hBinner_eq, intervalIntegral.integral_const]
    simp
  have hdecomp (x : E3) :
      fderiv ℝ (euclideanHeatKernel 3 t) x h =
        ∑ i : Fin 3, h i * D i x := by
    have hv : h = ∑ i : Fin 3, h i • EuclideanSpace.single i 1 := by
      ext j
      fin_cases j <;> simp [Fin.sum_univ_succ]
    calc
      fderiv ℝ (euclideanHeatKernel 3 t) x h =
          fderiv ℝ (euclideanHeatKernel 3 t) x
            (∑ i : Fin 3, h i • EuclideanSpace.single i 1) :=
        congrArg (fderiv ℝ (euclideanHeatKernel 3 t) x) hv
      _ = ∑ i : Fin 3,
          fderiv ℝ (euclideanHeatKernel 3 t) x
            (h i • EuclideanSpace.single i 1) := by rw [map_sum]
      _ = ∑ i : Fin 3, h i * D i x := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul]
        simp only [D, smul_eq_mul]
  have hpoint_linear (y : E3) :
      |K (y + h) - K y| ≤ ∫ s in (0 : ℝ)..1, B (s, y) := by
    let g : ℝ → ℝ := fun s => K (y + s • h)
    have hline_at (s : ℝ) : HasDerivAt (fun r : ℝ => y + r • h) h s := by
      simpa using (hasDerivAt_id s).smul_const h |>.const_add y
    have hgd : Differentiable ℝ g := by
      dsimp [g]
      exact (hKsmooth.differentiable (by simp)).comp (by fun_prop)
    have hgc : ContinuousOn g (Icc (0 : ℝ) 1) :=
      hgd.continuous.continuousOn
    have hderiv (s : ℝ) : deriv g s = fderiv ℝ (euclideanHeatKernel 3 t)
        (y + s • h) h := by
      have hh := ((hKsmooth.differentiable (by simp) (y + s • h)).hasFDerivAt).comp_hasDerivAt
        s (hline_at s)
      exact hh.deriv
    have hnorm (s : ℝ) : ‖deriv g s‖ ≤ B (s, y) := by
      rw [hderiv s, hdecomp]
      dsimp [B, F]
      calc
        ‖∑ i : Fin 3, h i * D i (y + s • h)‖ ≤
            ∑ i : Fin 3, ‖h i * D i (y + s • h)‖ := norm_sum_le _ _
        _ = ∑ i : Fin 3, |h i| * |D i (y + s • h)| := by
          simp [Real.norm_eq_abs]
    have hBi : IntervalIntegrable (fun s : ℝ => B (s, y)) volume 0 1 := by
      apply Continuous.intervalIntegrable
      dsimp [B]
      apply continuous_finsetSum
      intro i hi
      exact continuous_const.mul ((hFcont i).comp (by fun_prop))
    have hh := norm_sub_le_integral_of_norm_deriv_le_of_le
      (f := g) (B := fun s => B (s, y)) (show (0 : ℝ) ≤ 1 by norm_num)
      hgc hgd.differentiableOn (Filter.Eventually.of_forall (fun s _ => hnorm s)) hBi
    simpa [g, K] using hh
  have hlinear_bound :
      (∫ y : E3, |K (y + h) - K y|) ≤ C * ‖h‖ / Real.sqrt t := by
    have hi := integral_mono habs hBint hpoint_linear
    rw [hB_integral] at hi
    have hsum_bound :
        (∑ i : Fin 3, |h i| * (∫ y : E3, |D i y|)) ≤
          ∑ i : Fin 3, |h i| * (Cg / Real.sqrt t) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hgrad t ht i).2 (abs_nonneg _)
    have hcoord : (∑ i : Fin 3, |h i|) ≤ 3 * ‖h‖ := by
      calc
        (∑ i : Fin 3, |h i|) ≤ ∑ i : Fin 3, ‖h‖ := by
          apply Finset.sum_le_sum
          intro i hi
          simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le h i)
        _ = 3 * ‖h‖ := by simp
    have hrate : 0 ≤ Cg / Real.sqrt t := by positivity
    calc
      (∫ y : E3, |K (y + h) - K y|) ≤
          ∑ i : Fin 3, |h i| * (Cg / Real.sqrt t) := hi.trans hsum_bound
      _ = (∑ i : Fin 3, |h i|) * (Cg / Real.sqrt t) := by
        rw [Finset.sum_mul]
      _ ≤ (3 * ‖h‖) * (Cg / Real.sqrt t) :=
        mul_le_mul_of_nonneg_right hcoord hrate
      _ = C * ‖h‖ / Real.sqrt t := by
        dsimp [C]
        ring
  refine ⟨hdiff, le_min hmass_bound hlinear_bound⟩
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
