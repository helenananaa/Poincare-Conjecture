import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HistoryHessianJointContinuity
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHessianTerminalTail
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideDuhamelHessianThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HeatGeneratorC2
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearMildRestart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.ParabolicPDE
open Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual full Hessian integral minus a fixed history cutoff is uniformly small. -/
theorem hessian_history_cutoff_error (alpha : ℝ) (ha : 0<alpha) (ha1 : alpha<1) :
    ∃ C : ℝ, 0<C ∧ ∀ (F : (ℝ × E3) →ᵇ ℝ) (L t b : ℝ), 0≤L → 0<t →
      0≤b → b≤t →
      (∀ s∈Icc (0:ℝ) t, ∀ x y : E3, |F (s,x)-F (s,y)|≤L*‖x-y‖^alpha) →
      ∀ (x : E3) (i j : Fin 3),
        |(∫ s in (0:ℝ)..t, ∫ y : E3,
          fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (t-s)) z
            (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1)*F (s,y))-
         (∫ s in (0:ℝ)..b, ∫ y : E3,
          fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (t-s)) z
            (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1)*F (s,y))|
        ≤ C*L*(t-b)^(alpha/2) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C, hC, hterminal⟩ :=
    duhamel_hessian_terminal_tail alpha ha ha1
  obtain ⟨_, _, hfullcontrol⟩ :=
    euclideanHeatKernel_three_duhamel_hessian_control alpha ha ha1
  refine ⟨C, hC, ?_⟩
  intro F L t b hL ht hb hbt hHolder x i j
  by_cases hbT : b = t
  · subst b
    simp [ha.ne']
  · let q : ℝ → ℝ := fun s => ∫ y : E3,
      fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (t-s)) z
        (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1)*F (s,y)
    let r : ℝ → ℝ := fun s => ∫ y : E3,
      fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (t-s)) z
        (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)*F (s,x-y)
    have hreflect : ∀ s : ℝ, q s = r s := by
      intro s
      have hmap :=
        (Measure.measurePreserving_sub_left (volume : Measure E3) x).integral_comp
          (MeasurableEquiv.subLeft x).measurableEmbedding
          (fun z : E3 =>
            fderiv ℝ (fun w : E3 => fderiv ℝ (euclideanHeatKernel 3 (t-s)) w
              (EuclideanSpace.single i 1)) z (EuclideanSpace.single j 1)*F (s,x-z))
      simpa [q, r, sub_sub_cancel] using hmap
    have hFbound : ∀ s ∈ Icc (0 : ℝ) t, ∀ y : E3,
        |F (s,y)| ≤ ‖F‖ := by
      intro s hs y
      simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (s,y)
    obtain ⟨hfullr, _⟩ := hfullcontrol F F.continuous ‖F‖ L t
      (norm_nonneg F) hL ht.le hFbound hHolder i j x
    have hfull : IntervalIntegrable q volume 0 t := by
      have hr : IntervalIntegrable r volume 0 t := by
        simpa [r] using hfullr
      exact hr.congr (fun s _ => (hreflect s).symm)
    obtain ⟨htailr, htailbound⟩ := hterminal F L t (t-b) hL
      (sub_nonneg.mpr hbt) (by linarith) hHolder x i j
    have htailr' : IntervalIntegrable r volume b t := by
      simpa [r, sub_sub_cancel] using htailr
    have htail : IntervalIntegrable q volume b t := by
      exact htailr'.congr (fun s _ => (hreflect s).symm)
    have hmem : b ∈ uIcc (0 : ℝ) t := by
      rw [uIcc_of_le ht.le]
      exact ⟨hb, hbt⟩
    have hparts := (IntervalIntegrable.trans_iff hmem).mp hfull
    have hleft : IntervalIntegrable q volume 0 b := hparts.1
    have hadd : (∫ s in (0 : ℝ)..t, q s) =
        (∫ s in (0 : ℝ)..b, q s) + ∫ s in b..t, q s := by
      symm
      exact intervalIntegral.integral_add_adjacent_intervals hleft htail
    have hdiff : (∫ s in (0 : ℝ)..t, q s) -
        ∫ s in (0 : ℝ)..b, q s = ∫ s in b..t, q s := by
      rw [hadd]
      ring
    have htail_eq : (∫ s in b..t, q s) = ∫ s in b..t, r s := by
      exact intervalIntegral.integral_congr (fun s _ => hreflect s)
    change |(∫ s in (0 : ℝ)..t, q s) - ∫ s in (0 : ℝ)..b, q s| ≤
      C * L * (t-b)^(alpha/2)
    rw [hdiff, htail_eq]
    simpa [r, sub_sub_cancel] using htailbound
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
