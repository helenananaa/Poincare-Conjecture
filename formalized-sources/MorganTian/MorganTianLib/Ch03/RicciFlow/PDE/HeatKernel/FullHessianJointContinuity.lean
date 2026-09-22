import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ContinuousLocalApproximation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HessianHistoryCutoffError
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HistoryHessianJointContinuity
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
/-- Actual untruncated Hessian integrals are jointly continuous for spatially Holder source. -/
theorem full_hessian_joint_continuity (F : (ℝ × E3) →ᵇ ℝ)
    (alpha L T : ℝ) (ha : 0<alpha) (ha1 : alpha<1) (hL : 0≤L) (hT : 0<T)
    (hF : ∀ s∈Icc (0:ℝ) T, ∀ x y : E3, |F (s,x)-F (s,y)|≤L*‖x-y‖^alpha)
    (i j : Fin 3) :
    ContinuousOn (fun p : ℝ × E3 => ∫ s in (0:ℝ)..p.1, ∫ y : E3,
      fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (p.1-s)) z
        (EuclideanSpace.single i 1)) (p.2-y) (EuclideanSpace.single j 1)*F (s,y))
      (Ioo (0:ℝ) T ×ˢ (univ : Set E3)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  intro p hp
  have hp0 : 0 < p.1 := hp.1.1
  have hpT : p.1 < T := hp.1.2
  obtain ⟨C, hC, hcut⟩ := hessian_history_cutoff_error alpha ha ha1
  have hpowpos : 0 < alpha / 2 := by linarith
  have htwo : Tendsto (fun d : ℝ => 2 * d) (𝓝 (0 : ℝ)) (𝓝 0) := by
    convert
      ((continuous_const.mul continuous_id :
        Continuous ((fun _ : ℝ => (2 : ℝ)) * (fun d : ℝ => d))).tendsto 0) using 1
    ext d
    · rfl
    · simp [Pi.mul_apply]
  have hpow : Tendsto (fun d : ℝ => (2 * d) ^ (alpha / 2))
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, Real.zero_rpow hpowpos.ne'] using
      (Real.continuous_rpow_const hpowpos.le).tendsto 0 |>.comp htwo
  have hsmall : Tendsto (fun d : ℝ => C * L * (2 * d) ^ (alpha / 2))
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hpow : Tendsto
        (fun d : ℝ => (C * L) * (2 * d) ^ (alpha / 2))
        (𝓝 (0 : ℝ)) (𝓝 ((C * L) * 0)))
  refine (continuousAt_of_local_approximants _ p ?_).continuousWithinAt
  intro eps heps
  have hset : {d : ℝ | C * L * (2 * d) ^ (alpha / 2) < eps} ∈ 𝓝 (0 : ℝ) :=
    hsmall.eventually (eventually_lt_nhds heps)
  obtain ⟨δ, hδ, hδset⟩ := Metric.mem_nhds_iff.1 hset
  let d : ℝ := min (δ / 2) (p.1 / 4)
  have hdpos : 0 < d := by
    dsimp [d]
    exact lt_min (by linarith) (by linarith)
  have hdδ : dist d (0 : ℝ) < δ := by
    have hdδ' : d < δ := by
      dsimp [d]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    simpa [dist_zero_right, Real.norm_eq_abs, abs_of_pos hdpos] using hdδ'
  have hdsmall : C * L * (2 * d) ^ (alpha / 2) < eps := hδset hdδ
  have hdupper : d < p.1 / 2 := by
    dsimp [d]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  let b : ℝ := p.1 - d
  let g : (ℝ × E3) → ℝ := fun q => ∫ s in (0 : ℝ)..b, ∫ y : E3,
    fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (q.1-s)) z
      (EuclideanSpace.single i 1)) (q.2-y) (EuclideanSpace.single j 1)*F (s,y)
  have hb0 : 0 ≤ b := by
    dsimp [b]
    linarith
  have hbp : b < p.1 := by
    dsimp [b]
    linarith
  have hgh : ContinuousAt g p := by
    have hpI : p ∈ Ioi b ×ˢ (univ : Set E3) := ⟨hbp, mem_univ _⟩
    have hopen : IsOpen (Ioi b ×ˢ (univ : Set E3)) :=
      isOpen_Ioi.prod isOpen_univ
    have hcont := (history_hessian_joint_continuity F b hb0 i j) p hpI
    exact (show ContinuousWithinAt g (Ioi b ×ˢ (univ : Set E3)) p from
      hcont).continuousAt (hopen.mem_nhds hpI)
  have hfg : ∀ᶠ q : ℝ × E3 in 𝓝 p, |(fun q : ℝ × E3 => ∫ s in (0:ℝ)..q.1,
      ∫ y : E3, fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (q.1-s)) z
        (EuclideanSpace.single i 1)) (q.2-y) (EuclideanSpace.single j 1)*F (s,y)) q -
      g q| ≤ eps := by
    have htime : ∀ᶠ q : ℝ × E3 in 𝓝 p, q.1 ∈ Ioo (0 : ℝ) T :=
      continuousAt_fst.eventually (Ioo_mem_nhds hp0 hpT)
    have hnear : ∀ᶠ q : ℝ × E3 in 𝓝 p,
        q.1 ∈ Ioo (p.1 - d) (p.1 + d) :=
      continuousAt_fst.eventually (Ioo_mem_nhds (by linarith) (by linarith))
    filter_upwards [htime, hnear] with q hqt hqn
    have hqb : 0 ≤ b := hb0
    have hqpos : 0 < q.1 := hqt.1
    have hqT : q.1 ≤ T := hqt.2.le
    have hbt : b ≤ q.1 := by
      dsimp [b]
      linarith [hqn.1]
    have hholderq : ∀ s ∈ Icc (0 : ℝ) q.1, ∀ x y : E3,
        |F (s,x)-F (s,y)|≤L*‖x-y‖^alpha := by
      intro s hs x y
      exact hF s ⟨hs.1, hs.2.trans hqT⟩ x y
    have herr := hcut F L q.1 b hL hqpos hqb hbt hholderq q.2 i j
    have hqdiff : q.1 - b < 2 * d := by
      dsimp [b]
      linarith [hqn.2]
    have hqdiff0 : 0 ≤ q.1 - b := sub_nonneg.mpr hbt
    have hpowl : (q.1 - b) ^ (alpha / 2) ≤ (2 * d) ^ (alpha / 2) :=
      Real.rpow_le_rpow hqdiff0 hqdiff.le hpowpos.le
    have hbound : C * L * (q.1 - b) ^ (alpha / 2) ≤ eps := by
      calc
        C * L * (q.1 - b) ^ (alpha / 2) ≤ C * L * (2 * d) ^ (alpha / 2) :=
          mul_le_mul_of_nonneg_left hpowl (mul_nonneg hC.le hL)
        _ ≤ eps := hdsmall.le
    simpa [g] using herr.trans hbound
  exact ⟨g, hgh, hfg⟩
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
