import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanBasic
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Semigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Equation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderTimeKernel
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators
noncomputable section
namespace MorganTianLib.ParabolicPDE
/-- **Math.** Normalization and convolution for the actual kernel on Euclidean n-space. -/
theorem euclideanHeatKernel_mass_semigroup (n : ℕ) :
    (∀ t : ℝ, 0 < t → Integrable (euclideanHeatKernel n t) volume ∧
      (∫ x : EuclideanSpace ℝ (Fin n), euclideanHeatKernel n t x) = 1) ∧
    ∀ t s : ℝ, 0 < t → 0 < s → ∀ x : EuclideanSpace ℝ (Fin n),
      Integrable (fun y => euclideanHeatKernel n t (x - y) * euclideanHeatKernel n s y) volume ∧
      (∫ y : EuclideanSpace ℝ (Fin n), euclideanHeatKernel n t (x - y) * euclideanHeatKernel n s y) =
        euclideanHeatKernel n (t + s) x := by
/- SWARM_PROOF_BEGIN -/
  constructor
  · intro t ht
    have hscalar : Integrable (gaussianHeatKernel t) (volume : Measure ℝ) :=
      (gaussianHeatKernel_mass_semigroup.1 t ht).1
    have hpi : Integrable
        (fun v : Fin n → ℝ => ∏ i, gaussianHeatKernel t (v i))
        (volume : Measure (Fin n → ℝ)) := by
      exact Integrable.fintype_prod (fun _ => hscalar)
    have hmass_pi :
        (∫ v : Fin n → ℝ, ∏ i, gaussianHeatKernel t (v i)) = 1 := by
      rw [integral_fintype_prod_volume_eq_prod]
      simp [(gaussianHeatKernel_mass_semigroup.1 t ht).2]
    constructor
    · rw [← (PiLp.volume_preserving_toLp (Fin n)).integrable_comp_emb
        (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding]
      simpa [euclideanHeatKernel, Function.comp_def] using hpi
    · rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding]
      simpa [euclideanHeatKernel, Function.comp_def] using hmass_pi
  · intro t s ht hs x
    have hscalar_t : Integrable (gaussianHeatKernel t) (volume : Measure ℝ) :=
      (gaussianHeatKernel_mass_semigroup.1 t ht).1
    have hscalar_s : Integrable (gaussianHeatKernel s) (volume : Measure ℝ) :=
      (gaussianHeatKernel_mass_semigroup.1 s hs).1
    have hpi : Integrable
        (fun v : Fin n → ℝ =>
          ∏ i, (gaussianHeatKernel t (x i - v i) * gaussianHeatKernel s (v i)))
        (volume : Measure (Fin n → ℝ)) := by
      refine Integrable.fintype_prod
        (f := fun i (v : ℝ) =>
          gaussianHeatKernel t (x i - v) * gaussianHeatKernel s v) ?_
      intro i
      exact (gaussianHeatKernel_mass_semigroup.2 t s ht hs (x i)).1
    have hconv_pi :
        (∫ v : Fin n → ℝ,
          ∏ i, (gaussianHeatKernel t (x i - v i) * gaussianHeatKernel s (v i))) =
          ∏ i, gaussianHeatKernel (t + s) (x i) := by
      rw [integral_fintype_prod_volume_eq_prod
        (f := fun i (v : ℝ) =>
          gaussianHeatKernel t (x i - v) * gaussianHeatKernel s v)]
      congr with i
      exact (gaussianHeatKernel_mass_semigroup.2 t s ht hs (x i)).2
    constructor
    · rw [← (PiLp.volume_preserving_toLp (Fin n)).integrable_comp_emb
        (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding]
      simpa [euclideanHeatKernel, Function.comp_def, Finset.prod_mul_distrib,
        PiLp.toLp_apply,
        MeasurableEquiv.toLp_apply] using hpi
    · rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding]
      simpa [euclideanHeatKernel, Function.comp_def, Finset.prod_mul_distrib,
        PiLp.toLp_apply,
        MeasurableEquiv.toLp_apply] using hconv_pi
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
