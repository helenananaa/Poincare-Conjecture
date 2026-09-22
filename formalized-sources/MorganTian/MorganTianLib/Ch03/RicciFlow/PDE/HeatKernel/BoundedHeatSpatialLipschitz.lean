import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideTranslationL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Spatial Lipschitz regularization of the actual bounded heat convolution. -/
theorem bounded_heat_spatial_lipschitz :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : E3 →ᵇ ℝ) (t : ℝ), 0 < t → ∀ x z : E3,
      |(∫ y : E3, euclideanHeatKernel 3 t (x-y)*f y) -
        (∫ y : E3, euclideanHeatKernel 3 t (z-y)*f y)| ≤
          C*‖f‖*‖x-z‖/Real.sqrt t :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C, hC, htrans⟩ := euclideanHeatKernel_three_translation_L1
  refine ⟨C, hC, ?_⟩
  intro f t ht x z
  let K : E3 → ℝ := euclideanHeatKernel 3 t
  have hKint : Integrable K volume := by
    simpa [K] using (euclideanHeatKernel_mass_semigroup 3).1 t ht |>.1
  have hKcomp (a : E3) : Integrable (fun y : E3 => K (a - y)) volume := by
    have hmap := (Measure.measurePreserving_sub_left (volume : Measure E3) a).integrable_comp_of_integrable hKint
    simpa [K, Function.comp_def] using hmap
  have hconv (a : E3) :
      Integrable (fun y : E3 => K (a - y) * f y) volume := by
    apply hKcomp a |>.mul_bdd f.continuous.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun y => f.norm_coe_le_norm y)
  have hdiffK :
      Integrable (fun y : E3 => K (y + (x - z)) - K y) volume := by
    simpa [K] using (htrans t ht (x - z)).1
  have hdiffK_bound :
      (∫ y : E3, |K (y + (x - z)) - K y|) ≤
        min 2 (C * ‖x - z‖ / Real.sqrt t) := by
    simpa [K] using (htrans t ht (x - z)).2
  let q : E3 → ℝ := fun y =>
    (K (y + (x - z)) - K y) * f (z - y)
  have hfcomp : AEStronglyMeasurable (fun y : E3 => f (z - y)) volume := by
    exact (f.continuous.comp (by fun_prop)).aestronglyMeasurable
  have hq : Integrable q volume := by
    apply hdiffK.mul_bdd hfcomp
    exact Filter.Eventually.of_forall (fun y => f.norm_coe_le_norm (z - y))
  have hmajor : Integrable (fun y : E3 => ‖f‖ *
      |K (y + (x - z)) - K y|) volume := by
    simpa [Real.norm_eq_abs, mul_comm] using hdiffK.norm.const_mul ‖f‖
  have hq_bound : ∀ᵐ y : E3 ∂(volume : Measure E3),
      ‖q y‖ ≤ ‖f‖ * |K (y + (x - z)) - K y| := by
    filter_upwards [] with y
    dsimp [q]
    rw [abs_mul]
    calc
      |K (y + (x - z)) - K y| * |f (z - y)| ≤
          |K (y + (x - z)) - K y| * ‖f‖ :=
        mul_le_mul_of_nonneg_left (f.norm_coe_le_norm (z - y)) (abs_nonneg _)
      _ = ‖f‖ * |K (y + (x - z)) - K y| := by ring
  have hq_integral_bound :
      |∫ y : E3, q y| ≤ ‖f‖ *
        (∫ y : E3, |K (y + (x - z)) - K y|) := by
    have hh := norm_integral_le_of_norm_le hmajor hq_bound
    calc
      |∫ y : E3, q y| ≤ ∫ y : E3, ‖f‖ *
          |K (y + (x - z)) - K y| := by
        simpa [Real.norm_eq_abs] using hh
      _ = ‖f‖ * (∫ y : E3, |K (y + (x - z)) - K y|) := by
        rw [integral_const_mul]
  have hchange :
      (∫ y : E3, K (x - y) * f y - K (z - y) * f y) = ∫ y : E3, q y := by
    have hmap :=
      (Measure.measurePreserving_sub_left (volume : Measure E3) z).integral_comp
        (MeasurableEquiv.subLeft z).measurableEmbedding q
    calc
      (∫ y : E3, K (x - y) * f y - K (z - y) * f y) =
          ∫ y : E3, q (z - y) := by
            congr 1
            funext y
            dsimp [q]
            have hxy : (z - y) + (x - z) = x - y := by abel
            rw [hxy, sub_sub_cancel]
            ring
      _ = ∫ y : E3, q y := hmap
  rw [← integral_sub (hconv x) (hconv z), hchange]
  calc
    |∫ y : E3, q y| ≤ ‖f‖ *
        (∫ y : E3, |K (y + (x - z)) - K y|) := hq_integral_bound
    _ ≤ ‖f‖ * (C * ‖x - z‖ / Real.sqrt t) := by
      exact mul_le_mul_of_nonneg_left
        (hdiffK_bound.trans (min_le_right _ _)) (norm_nonneg _)
    _ = C * ‖f‖ * ‖x - z‖ / Real.sqrt t := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
