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
/-- Put the true time-space integral on a fixed nonsingular parameter domain. -/
theorem duhamel_fixed_domain_formula (F : HeatSpace) (t : ℝ) (ht : 0 ≤ t) (x : E3) :
    (∫ s in (0:ℝ)..t, ∫ y : E3, euclideanHeatKernel 3 (t-s) y * F (s,x-y)) =
      t * ∫ r in (0:ℝ)..1, ∫ z : E3, euclideanHeatKernel 3 1 z *
        F (t*r,x-(Real.sqrt (t*(1-r))) • z) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  by_cases ht0 : t = 0
  · subst t
    simp
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    let g : ℝ → ℝ := fun s =>
      ∫ y : E3, euclideanHeatKernel 3 (t - s) y * F (s, x - y)
    let H : ℝ → ℝ := fun r =>
      ∫ z : E3, euclideanHeatKernel 3 1 z *
        F (t * r, x - (Real.sqrt (t * (1 - r))) • z)
    obtain ⟨hgint, hg_bound⟩ := euclideanHeatKernel_three_bounded_duhamel F t ht x
    have hrescaled : IntervalIntegrable (fun r => g (t * r)) volume 0 1 := by
      have h := hgint.comp_mul_left (c := t)
      simpa [g, htpos.ne', div_self htpos.ne'] using h
    have hEq : ∀ᵐ r ∂volume, r ∈ uIoc (0 : ℝ) 1 → g (t * r) = H r := by
      filter_upwards [volume.ae_ne (1 : ℝ)] with r hr
      intro hrI
      rw [uIoc_of_le (by norm_num)] at hrI
      have hrlt : r < 1 := lt_of_le_of_ne hrI.2 hr
      have hq : 0 < t * (1 - r) := mul_pos htpos (sub_pos.mpr hrlt)
      let fs : E3 →ᵇ ℝ := F.compContinuous
        ⟨fun y : E3 => (t * r, y), continuous_const.prodMk continuous_id⟩
      have hstd := heat_convolution_standard_gaussian fs (t * (1 - r)) hq x
      change
        (∫ y : E3, euclideanHeatKernel 3 (t - t * r) y * F (t * r, x - y)) =
          ∫ z : E3, euclideanHeatKernel 3 1 z *
            F (t * r, x - (Real.sqrt (t * (1 - r))) • z)
      convert hstd using 1 <;> simp [fs]
      congr 1
      funext y
      congr 1
      rw [show t - t * r = t * (1 - r) by ring]
    have hEqRestr : (fun r => g (t * r)) =ᵐ[volume.restrict (uIoc (0 : ℝ) 1)] H := by
      exact (ae_restrict_iff' measurableSet_uIoc).2 hEq
    have hfixed : IntervalIntegrable H volume 0 1 :=
      hrescaled.congr_ae hEqRestr
    have hinner :
        (∫ r in (0 : ℝ)..1, g (t * r)) = ∫ r in (0 : ℝ)..1, H r := by
      exact intervalIntegral.integral_congr_ae hEq
    have hchange :
        (∫ s in (0 : ℝ)..t, g s) =
          t * ∫ r in (0 : ℝ)..1, g (t * r) := by
      have h := intervalIntegral.smul_integral_comp_mul_left
        (f := g) (a := (0 : ℝ)) (b := 1) t
      simpa [smul_eq_mul] using h.symm
    calc
      (∫ s in (0 : ℝ)..t, ∫ y : E3,
          euclideanHeatKernel 3 (t-s) y * F (s,x-y)) =
          ∫ s in (0 : ℝ)..t, g s := by rfl
      _ = t * ∫ r in (0 : ℝ)..1, g (t * r) := hchange
      _ = t * ∫ r in (0 : ℝ)..1, H r := by rw [hinner]
      _ = t * ∫ r in (0 : ℝ)..1, ∫ z : E3, euclideanHeatKernel 3 1 z *
          F (t*r,x-(Real.sqrt (t*(1-r))) • z) := by rfl
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
