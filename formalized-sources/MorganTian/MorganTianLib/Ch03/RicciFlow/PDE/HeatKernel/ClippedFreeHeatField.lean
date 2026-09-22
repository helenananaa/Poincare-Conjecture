import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.StandardGaussianConvolution
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedClassicalIVP
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedDuhamelNonlinearDifference
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelBoundedForcing
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideTranslationL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GaussianNormForm
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.ParametricIntegral
open Set MeasureTheory Filter Function
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "HeatSpace" => (ℝ × E3) →ᵇ ℝ
/-- The initial-data heat field, continuous through time zero and bounded on a time slab. -/
theorem clipped_free_heat_field (f : E3 →ᵇ ℝ) (hf : UniformContinuous f) (T : ℝ) (hT : 0 ≤ T) :
    ∃ P : HeatSpace, ‖P‖ ≤ ‖f‖ ∧ ∀ p : ℝ × E3,
      P p = if max 0 (min T p.1) = 0 then f p.2 else
        ∫ y : E3, euclideanHeatKernel 3 (max 0 (min T p.1)) y * f (p.2-y) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let K : E3 → ℝ := fun z => euclideanHeatKernel 3 1 z
  have hKint : Integrable K volume := by
    simpa [K] using (euclideanHeatKernel_mass_semigroup 3).1 1 one_pos |>.1
  have hKmass : (∫ z : E3, K z) = 1 := by
    simpa [K] using (euclideanHeatKernel_mass_semigroup 3).1 1 one_pos |>.2
  have hKnonneg (z : E3) : 0 ≤ K z := by
    dsimp [K]
    exact (euclideanHeatKernel_pos 3 one_pos z).le
  have hKcont : Continuous K := by
    simpa [K] using (euclideanHeatKernel_three_heat_equation one_pos).1.continuous
  let G : (ℝ × E3) → E3 → ℝ := fun p z =>
    K z * f (p.2 - (Real.sqrt (max 0 p.1)) • z)
  have hGcont (z : E3) : Continuous (fun p : ℝ × E3 => G p z) := by
    dsimp [G]
    exact continuous_const.mul (f.continuous.comp (by fun_prop))
  have hGslice (p : ℝ × E3) : Continuous (fun z : E3 => G p z) := by
    dsimp [G]
    exact hKcont.mul (f.continuous.comp (by fun_prop))
  let H : ℝ × E3 → ℝ := fun p => ∫ z : E3, G p z
  have hGbound (p : ℝ × E3) (z : E3) :
      ‖G p z‖ ≤ K z * ‖f‖ := by
    dsimp [G]
    rw [abs_mul, abs_of_nonneg (hKnonneg z)]
    exact mul_le_mul_of_nonneg_left
      (by simpa [Real.norm_eq_abs] using
        f.norm_coe_le_norm (p.2 - (Real.sqrt (max 0 p.1)) • z)) (hKnonneg z)
  have hbound_int : Integrable (fun z : E3 => K z * ‖f‖) volume :=
    hKint.mul_const _
  have hHcont : Continuous H := by
    rw [continuous_iff_continuousAt]
    intro p
    have hmeas : ∀ᶠ q : ℝ × E3 in 𝓝 p,
        AEStronglyMeasurable (G q) volume := by
      filter_upwards [] with q
      exact (hGslice q).aestronglyMeasurable
    have hbound : ∀ᶠ q : ℝ × E3 in 𝓝 p,
        ∀ᵐ z : E3 ∂volume, ‖G q z‖ ≤ K z * ‖f‖ := by
      filter_upwards [] with q
      exact ae_of_all _ (hGbound q)
    have hlim : ∀ᵐ z : E3 ∂volume,
        Tendsto (fun q : ℝ × E3 => G q z) (𝓝 p) (𝓝 (G p z)) := by
      exact ae_of_all _ (fun z => (hGcont z).continuousAt)
    change Tendsto H (𝓝 p) (𝓝 (H p))
    simpa [H] using
      (MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (l := 𝓝 p) (F := G) (f := G p) (K · * ‖f‖)
        hmeas hbound hbound_int hlim)
  have hHbound (p : ℝ × E3) : ‖H p‖ ≤ ‖f‖ := by
    have hInt : Integrable (G p) volume :=
      hbound_int.mono' (hGslice p).aestronglyMeasurable
        (ae_of_all _ (hGbound p))
    calc
      ‖H p‖ ≤ ∫ z : E3, K z * ‖f‖ := by
        dsimp [H]
        exact norm_integral_le_of_norm_le hbound_int
          (Eventually.of_forall (hGbound p))
      _ = ‖f‖ := by
        rw [integral_mul_const, hKmass, one_mul]
  let clip : ℝ → ℝ := fun t => max 0 (min T t)
  let Q : ℝ × E3 → ℝ := fun p => H (clip p.1, p.2)
  have hclip : Continuous clip := by
    dsimp [clip]
    fun_prop
  have hQcont : Continuous Q := by
    apply hHcont.comp
    fun_prop
  have hQbound (p : ℝ × E3) : ‖Q p‖ ≤ ‖f‖ := by
    exact hHbound (clip p.1, p.2)
  let P : HeatSpace :=
    BoundedContinuousFunction.ofNormedAddCommGroup Q hQcont ‖f‖ hQbound
  refine ⟨P, ?_, ?_⟩
  · exact BoundedContinuousFunction.norm_le_of_nonempty.mpr hQbound
  · intro p
    let r : ℝ := clip p.1
    have hr : 0 ≤ r := by
      dsimp [r, clip]
      exact le_max_left _ _
    by_cases hr0 : r = 0
    · have hzero : H (r, p.2) = f p.2 := by
        dsimp [H, G]
        rw [show Real.sqrt (max 0 r) = 0 by simp [hr0]]
        simp only [zero_smul, sub_zero]
        rw [integral_mul_const, hKmass, one_mul]
      change Q p = _
      rw [show Q p = H (r, p.2) by rfl, hzero]
      have hr_eq : max 0 (min T p.1) = r := rfl
      rw [hr_eq, if_pos hr0]
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have hstd := heat_convolution_standard_gaussian f r hrpos p.2
      change Q p = _
      rw [show Q p = H (r, p.2) by rfl]
      have hr_eq : max 0 (min T p.1) = r := rfl
      rw [hr_eq, if_neg hr0]
      simpa [H, G, K, max_eq_right hr] using hstd.symm
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
