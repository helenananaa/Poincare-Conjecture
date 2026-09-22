import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveJointSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Time differentiation passes under the actual compactly supported convolution integral. -/
theorem euclideanHeatKernel_compact_time_derivative (f : E3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {t : ℝ} (ht : 0 < t) (x : E3) :
    Integrable (fun y : E3 => deriv (fun s => euclideanHeatKernel 3 s (x-y)) t * f y) volume ∧
    HasDerivAt (fun s => ∫ y : E3, euclideanHeatKernel 3 s (x-y) * f y)
      (∫ y : E3, deriv (fun s => euclideanHeatKernel 3 s (x-y)) t * f y) t :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let G : ℝ × E3 → ℝ := fun p => euclideanHeatKernel 3 p.1 p.2
  let U : Set (ℝ × E3) := Ioi (0 : ℝ) ×ˢ (univ : Set E3)
  have hG : ContDiffOn ℝ ∞ G U := by
    simpa [G, U] using euclideanHeatKernel_joint_smooth 3
  have hUopen : IsOpen U := by
    exact isOpen_Ioi.prod isOpen_univ
  have hGfd : ContinuousOn (fderiv ℝ G) U :=
    hG.continuousOn_fderiv_of_isOpen hUopen (by simp)
  have hpart : ContinuousOn
      (fun p : ℝ × E3 => fderiv ℝ G p ((1 : ℝ), (0 : E3))) U := by
    exact hGfd.clm_apply continuousOn_const
  have htimePartial (r : ℝ) (hr : 0 < r) (z : E3) :
      HasDerivAt (fun q => euclideanHeatKernel 3 q z)
        (fderiv ℝ G (r, z) ((1 : ℝ), (0 : E3))) r := by
    have hp : (r, z) ∈ U := by
      exact ⟨hr, mem_univ _⟩
    have hca := hG.contDiffAt (hUopen.mem_nhds hp)
    have hfd := hca.differentiableAt (by simp) |>.hasFDerivAt
    have hcurve : HasDerivAt (fun q : ℝ => (q, z)) ((1 : ℝ), (0 : E3)) r := by
      simpa using (hasDerivAt_id r).prodMk (hasDerivAt_const r z)
    have hc := hfd.comp r hcurve
    have hc' : HasDerivAt (fun q => euclideanHeatKernel 3 q z)
        (fderiv ℝ G (r, z) ((1 : ℝ), (0 : E3))) r := by
      simpa [G, Function.comp_def] using hc.hasDerivAt
    exact hc'
  have htime (r : ℝ) (hr : 0 < r) (z : E3) :
      HasDerivAt (fun q => euclideanHeatKernel 3 q z)
        (deriv (fun q => euclideanHeatKernel 3 q z) r) r := by
    exact (htimePartial r hr z).congr_deriv (htimePartial r hr z).deriv.symm
  have htime_eq (r : ℝ) (hr : 0 < r) (z : E3) :
      deriv (fun q => euclideanHeatKernel 3 q z) r =
        fderiv ℝ G (r, z) ((1 : ℝ), (0 : E3)) :=
    (htimePartial r hr z).deriv
  let K : Set E3 := tsupport f
  have hK : IsCompact K := hfc.isCompact
  let S : Set ℝ := Ioo (t - t / 2) (t + t / 2)
  let J : Set ℝ := Icc (t - t / 2) (t + t / 2)
  have hSnhds : S ∈ 𝓝 t := by
    apply Ioo_mem_nhds <;> linarith [ht]
  have hSpos : ∀ r ∈ S, 0 < r := by
    intro r hr
    dsimp [S] at hr
    linarith [ht, hr.1]
  have hJpos : ∀ r ∈ J, 0 < r := by
    intro r hr
    dsimp [J] at hr
    linarith [ht, hr.1]
  let Q : ℝ × E3 → ℝ × E3 := fun p => (p.1, x - p.2)
  have hQ : Continuous Q := by
    exact continuous_fst.prodMk (continuous_const.sub continuous_snd)
  have hQJK : IsCompact (Q '' (J ×ˢ K)) := by
    apply (isCompact_Icc.prod hK).image
    exact hQ
  have hQsub : Q '' (J ×ˢ K) ⊆ U := by
    rintro p ⟨q, hq, rfl⟩
    exact ⟨hJpos q.1 hq.1, mem_univ _⟩
  obtain ⟨C, hC⟩ := hQJK.exists_bound_of_continuousOn (hpart.mono hQsub)
  let C₀ : ℝ := max C 0
  let F : ℝ → E3 → ℝ := fun r y => euclideanHeatKernel 3 r (x - y) * f y
  let F' : ℝ → E3 → ℝ := fun r y =>
    deriv (fun q => euclideanHeatKernel 3 q (x - y)) r * f y
  have hFcont (r : ℝ) (hr : 0 < r) : Continuous (F r) := by
    have hk : Continuous (fun y : E3 => euclideanHeatKernel 3 r (x - y)) := by
      exact (euclideanHeatKernel_three_heat_equation hr).1.continuous.comp
        (continuous_const.sub continuous_id)
    change Continuous ((fun y : E3 => euclideanHeatKernel 3 r (x - y)) * f)
    exact hk.mul hf.continuous
  have hFmeas : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (F r) volume := by
    filter_upwards [Ioi_mem_nhds ht] with r hr
    exact (hFcont r hr).aestronglyMeasurable
  have hpartial_comp : Continuous
      (fun y : E3 => fderiv ℝ G (t, x - y) ((1 : ℝ), (0 : E3))) := by
    have hm : Continuous (fun y : E3 => (t, x - y)) := by
      exact continuous_const.prodMk (continuous_const.sub continuous_id)
    have hmU : ∀ y : E3, (t, x - y) ∈ U := by
      intro y
      exact ⟨ht, mem_univ _⟩
    simpa [Function.comp_def] using hpart.comp_continuous hm hmU
  have hderivcont : Continuous
      (fun y : E3 => deriv (fun q => euclideanHeatKernel 3 q (x - y)) t) := by
    have heq : (fun y : E3 => deriv (fun q => euclideanHeatKernel 3 q (x - y)) t) =
        (fun y : E3 => fderiv ℝ G (t, x - y) ((1 : ℝ), (0 : E3))) := by
      funext y
      exact htime_eq t ht (x - y)
    rw [heq]
    exact hpartial_comp
  have hF'int : Integrable (F' t) volume := by
    have hcont : Continuous (F' t) := by
      change Continuous ((fun y : E3 => deriv (fun q => euclideanHeatKernel 3 q (x - y)) t) * f)
      exact hderivcont.mul hf.continuous
    exact hcont.integrable_of_hasCompactSupport hfc.mul_left
  have hF'meas : AEStronglyMeasurable (F' t) volume := by
    have hcont : Continuous (F' t) := by
      change Continuous ((fun y : E3 => deriv (fun q => euclideanHeatKernel 3 q (x - y)) t) * f)
      exact hderivcont.mul hf.continuous
    exact hcont.aestronglyMeasurable
  have hbound : ∀ᵐ y : E3, ∀ r ∈ S, ‖F' r y‖ ≤ C₀ * ‖f y‖ := by
    filter_upwards [] with y
    intro r hr
    by_cases hy : y ∈ K
    · have hrJ : r ∈ J := by
        exact ⟨le_of_lt hr.1, le_of_lt hr.2⟩
      have hq : (r, x - y) ∈ Q '' (J ×ˢ K) := by
        refine ⟨(r, y), ⟨hrJ, hy⟩, ?_⟩
        rfl
      have hCb := hC (r, x - y) hq
      have hder := htime_eq r (hSpos r hr) (x - y)
      dsimp [F', C₀]
      rw [hder]
      calc
        ‖fderiv ℝ G (r, x - y) ((1 : ℝ), (0 : E3)) * f y‖ =
            ‖fderiv ℝ G (r, x - y) ((1 : ℝ), (0 : E3))‖ * ‖f y‖ := norm_mul _ _
        _ ≤ max C 0 * ‖f y‖ :=
          mul_le_mul_of_nonneg_right (hCb.trans (le_max_left C 0)) (norm_nonneg _)
    · have hnot : y ∉ Function.support f := by
        intro hys
        exact hy (subset_closure hys)
      have hfy : f y = 0 := by
        by_contra hne
        exact hnot (Function.mem_support.mpr hne)
      simp [F', hfy]
  have hbound_int : Integrable (fun y : E3 => C₀ * ‖f y‖) volume := by
    exact (hf.continuous.norm.integrable_of_hasCompactSupport hfc.norm).const_mul C₀
  have hdiff : ∀ᵐ y : E3, ∀ r ∈ S, HasDerivAt (fun q => F q y) (F' r y) r := by
    filter_upwards [] with y
    intro r hr
    have hd := (htime r (hSpos r hr) (x - y)).mul_const (f y)
    simpa [F, F'] using hd
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure E3)) (F := F) (x₀ := t) (s := S)
      (bound := fun y : E3 => C₀ * ‖f y‖)
      hSnhds hFmeas (by simpa [F] using (hFcont t ht).integrable_of_hasCompactSupport hfc.mul_left)
      hF'meas hbound hbound_int hdiff
  constructor
  · simpa [F'] using hmain.1
  · simpa [F, F'] using hmain.2
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
