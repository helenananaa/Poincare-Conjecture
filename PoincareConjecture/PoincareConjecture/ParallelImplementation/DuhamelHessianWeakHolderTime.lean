import PoincareConjecture.ParallelImplementation.DuhamelHessianOperatorSchauder
import PoincareConjecture.ParallelImplementation.HolderTemporalInterpolation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FullDuhamelSpatialC2
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.DuhamelHessianWeakHolderTime
open Set MeasureTheory
open scoped Topology BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Time increments of the actual Hessian are small in weaker spatial Holder norm. -/
theorem duhamel_hessian_weaker_holder_time_bound
    (alpha beta : ℝ) (hb : 0 < beta) (hba : beta < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (ℝ × E3) →ᵇ ℝ) (L T : ℝ),
      0 ≤ L → 0 ≤ T →
      (∀ r ∈ Icc (0:ℝ) T, ∀ x z : E3, |F (r,x)-F (r,z)| ≤ L*‖x-z‖^alpha) →
      let u : ℝ → E3 → ℝ := fun t x => ∫ r in (0:ℝ)..t, ∫ y : E3,
        MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (t-r) (x-y)*F (r,y)
      let H := fun t x => fderiv ℝ (fderiv ℝ (u t)) x
      ∀ t ∈ Icc (0:ℝ) T, ∀ s ∈ Icc (0:ℝ) T, ∀ x z,
        ‖(H t x-H s x)-(H t z-H s z)‖ ≤
          C*L*|t-s|^((alpha-beta)/2)*‖x-z‖^beta :=
/- SWARM_PROOF_BEGIN -/
by
  have ha : 0 < alpha := lt_trans hb hba
  obtain ⟨C0, hC0, hOp⟩ :=
    PoincareConjecture.ParallelImplementation.DuhamelHessianOperatorSchauder.actual_duhamel_hessian_operator_schauder
      alpha ha ha1
  refine ⟨4 * C0, by positivity, ?_⟩
  intro F L T hL hT hholder
  dsimp only
  let u : ℝ → E3 → ℝ := fun t x => ∫ r in (0:ℝ)..t, ∫ y : E3,
    MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (t-r) (x-y)*F (r,y)
  let H := fun t x => fderiv ℝ (fderiv ℝ (u t)) x
  have hjoint : ∀ t ∈ Icc (0:ℝ) T, ∀ s ∈ Icc (0:ℝ) T, ∀ x z : E3,
      ‖H t x - H s z‖ ≤ C0 * L * (‖x-z‖^alpha + |t-s|^(alpha/2)) := by
    simpa [H, u] using (hOp F L T hL hT hholder).2.2
  have hzeroTime : (0:ℝ)^(alpha/2) = 0 :=
    Real.zero_rpow (ne_of_gt (by linarith : 0 < alpha/2))
  have hzeroSpace : (0:ℝ)^alpha = 0 := Real.zero_rpow (ne_of_gt ha)
  have hexp : 0 < (alpha-beta)/2 := by linarith
  have hzeroExp : (0:ℝ)^((alpha-beta)/2) = 0 :=
    Real.zero_rpow (ne_of_gt hexp)
  let K : ℝ := C0 * L
  have hK : 0 ≤ K := by dsimp [K]; positivity
  intro t ht s hs x z
  change ‖(H t x - H s x) - (H t z - H s z)‖ ≤
    (4 * C0) * L * |t-s|^((alpha-beta)/2) * ‖x-z‖^beta
  by_cases hts : t = s
  · subst s
    simp [hzeroExp]
  · let h : ℝ := |t-s|
    have hh : 0 < h := by
      dsimp [h]
      exact abs_pos.mpr (sub_ne_zero.mpr hts)
    have hf : ∀ x y : E3, ‖H t x - H t y‖ ≤ K * ‖x-y‖^alpha := by
      intro a b
      have hab := hjoint t ht t ht a b
      simpa [K, hzeroTime] using hab
    have hg : ∀ x y : E3, ‖H s x - H s y‖ ≤ K * ‖x-y‖^alpha := by
      intro a b
      have hab := hjoint s hs s hs a b
      simpa [K, hzeroTime] using hab
    have hdiff : ∀ w : E3, ‖H t w - H s w‖ ≤ K * h^(alpha/2) := by
      intro w
      have hw := hjoint t ht s hs w w
      simpa [K, h, hzeroTime, hzeroSpace] using hw
    have hinterp :=
      PoincareConjecture.ParallelImplementation.HolderTemporalInterpolation.holder_difference_time_interpolation
        (fun w : E3 => H t w) (fun w : E3 => H s w)
        alpha beta K h hb hba hK hh hf hg hdiff
    calc
      ‖(H t x - H s x) - (H t z - H s z)‖ ≤
          (4 * K * h^((alpha-beta)/2)) * ‖x-z‖^beta := hinterp x z
      _ = (4 * C0) * L * |t-s|^((alpha-beta)/2) * ‖x-z‖^beta := by
        dsimp [K, h]
        ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.DuhamelHessianWeakHolderTime
