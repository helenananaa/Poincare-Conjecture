import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelRestart
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelTerminalQuotient
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearMildSpatialC2
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FullDuhamelSpatialC2
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.CompactSpatialDerivativeDominator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHessianTerminalTail
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedNemytskiiOperator
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.ParabolicPDE
open Set Function Filter MeasureTheory
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Continuous right derivatives give the genuine two-sided derivative on an open interval. -/
theorem continuous_right_derivative_is_derivative (f g : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Ioo a b)) (hg : ContinuousOn g (Ioo a b))
    (hd : ∀ x∈Ioo a b, HasDerivWithinAt f (g x) (Ici x) x) :
    ∀ x∈Ioo a b, HasDerivAt f (g x) x :=
/- SWARM_PROOF_BEGIN -/
by
  intro x hx
  obtain ⟨c, hac, hcx⟩ := exists_between hx.1
  obtain ⟨d, hxd, hdb⟩ := exists_between hx.2
  have hcd : c ≤ d := hcx.le.trans hxd.le
  have hIcc : Icc c d ⊆ Ioo a b := by
    intro y hy
    exact ⟨hac.trans_le hy.1, lt_of_le_of_lt hy.2 hdb⟩
  have hfc : ContinuousOn f (Icc c d) := hf.mono hIcc
  have hgc : ContinuousOn g (Icc c d) := hg.mono hIcc
  have hPderiv : ∀ y ∈ Ico c d,
      HasDerivWithinAt (fun z => (∫ t in c..z, g t) + f c) (g y) (Ici y) y := by
    intro y hy
    have hyab : y ∈ Ioo a b := hIcc ⟨hy.1, hy.2.le⟩
    have hgcy : ContinuousOn g (Icc c y) :=
      hgc.mono (Icc_subset_Icc le_rfl hy.2.le)
    have h := intervalIntegral.integral_hasDerivAt_right
      (hgcy.intervalIntegrable_of_Icc hy.1)
      (hg.stronglyMeasurableAtFilter isOpen_Ioo y hyab)
      (hg.continuousAt (isOpen_Ioo.mem_nhds hyab))
    exact h.hasDerivWithinAt.add_const (f c)
  have hPcont : ContinuousOn (fun z => (∫ t in c..z, g t) + f c) (Icc c d) := by
    apply continuousOn_of_forall_continuousAt
    intro y hy
    have hyab : y ∈ Ioo a b := hIcc hy
    have hgcy : ContinuousOn g (Icc c y) :=
      hgc.mono (Icc_subset_Icc le_rfl hy.2)
    have h := intervalIntegral.integral_hasDerivAt_right
      (hgcy.intervalIntegrable_of_Icc hy.1)
      (hg.stronglyMeasurableAtFilter isOpen_Ioo y hyab)
      (hg.continuousAt (isOpen_Ioo.mem_nhds hyab))
    exact (h.add_const (f c)).continuousAt
  have heq : ∀ y ∈ Icc c d, f y = (∫ t in c..y, g t) + f c := by
    intro y hy
    exact eq_of_has_deriv_right_eq
      (fun z hz => hd z (hIcc ⟨hz.1, hz.2.le⟩)) hPderiv hfc hPcont (by simp) y hy
  have hgxc : ContinuousOn g (Icc c x) :=
    hgc.mono (Icc_subset_Icc le_rfl hxd.le)
  have h := intervalIntegral.integral_hasDerivAt_right
    (hgxc.intervalIntegrable_of_Icc hcx.le)
    (hg.stronglyMeasurableAtFilter isOpen_Ioo x hx)
    (hg.continuousAt (isOpen_Ioo.mem_nhds hx))
  apply (h.add_const (f c)).congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hcx hxd] with y hy
  exact (heq y hy)
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
