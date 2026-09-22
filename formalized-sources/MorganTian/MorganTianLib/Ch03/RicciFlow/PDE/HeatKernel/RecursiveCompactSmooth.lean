import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveJointSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual compactly supported heat convolution is jointly smooth for positive time. -/
theorem euclideanHeatKernel_compact_convolution_smooth (f : E3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E3 =>
      ∫ y : E3, euclideanHeatKernel 3 p.1 (p.2 - y) * f y)
      (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) :=
/- SWARM_PROOF_BEGIN -/
by
  let s : Set (ℝ × E3) := Ioi (0 : ℝ) ×ˢ (univ : Set E3)
  let k : Set E3 := -tsupport f
  let h : (ℝ × E3) → E3 → ℝ := fun p z =>
    euclideanHeatKernel 3 p.1 (p.2 + z) * f (-z)
  have hs : IsOpen s := by
    exact (isOpen_Ioi.prod isOpen_univ)
  have hk : IsCompact k := by
    dsimp [k]
    exact hfc.isCompact.neg
  have hzero : ∀ p x, p ∈ s → x ∉ k → h p x = 0 := by
    intro p x hp hx
    have hneg : -x ∉ tsupport f := by
      intro hnx
      change x ∉ -tsupport f at hx
      apply hx
      change -x ∈ tsupport f
      exact hnx
    simp [h, image_eq_zero_of_notMem_tsupport hneg]
  have hK : ContDiffOn ℝ ∞
      (fun q : ℝ × E3 => euclideanHeatKernel 3 q.1 q.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) :=
    euclideanHeatKernel_joint_smooth 3
  have harg : ContDiffOn ℝ ∞
      (fun q : (ℝ × E3) × E3 => (q.1.1, q.1.2 + q.2))
      (s ×ˢ (univ : Set E3)) := by
    fun_prop
  have hKcomp : ContDiffOn ℝ ∞
      (fun q : (ℝ × E3) × E3 =>
        euclideanHeatKernel 3 q.1.1 (q.1.2 + q.2))
      (s ×ˢ (univ : Set E3)) := by
    apply hK.comp harg
    intro q hq
    exact ⟨hq.1.1, mem_univ _⟩
  have hfneg : ContDiffOn ℝ ∞
      (fun q : (ℝ × E3) × E3 => f (-q.2))
      (s ×ˢ (univ : Set E3)) := by
    have hfneg' : ContDiff ℝ ∞ (fun z : E3 => f (-z)) :=
      hf.comp contDiff_neg
    exact hfneg'.comp_contDiffOn (by fun_prop)
  have hsmooth : ContDiffOn ℝ ∞
      (fun q : (ℝ × E3) × E3 => h q.1 q.2)
      (s ×ˢ (univ : Set E3)) := by
    exact hKcomp.mul hfneg
  have H := contDiffOn_convolution_right_with_param_comp
    (𝕜 := ℝ) (G := E3) (P := ℝ × E3) (E := ℝ) (E' := ℝ) (F := ℝ)
    (μ := volume) (n := (⊤ : ℕ∞)) (ContinuousLinearMap.mul ℝ ℝ)
    (s := s) (v := fun _ : ℝ × E3 => (0 : E3))
    (f := fun _ : E3 => (1 : ℝ)) (g := h) (k := k)
    contDiffOn_const hs hk hzero (locallyIntegrable_const (1 : ℝ)) hsmooth
  simpa [s, h, MeasureTheory.convolution, sub_eq_add_neg] using H
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
