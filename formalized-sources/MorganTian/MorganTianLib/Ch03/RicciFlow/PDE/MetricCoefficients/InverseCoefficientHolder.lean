import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalInverseControl
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)

/-- **Math.** inverse coefficient holder. -/
theorem inverse_coefficient_holder (A0 : E3 →L[ℝ] E3) (G : E3 → (E3 →L[ℝ] E3))
    (c L alpha : ℝ) (hc : 0 < c) (hL : 0 ≤ L)
    (hA0 : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A0 v) v)
    (hball : ∀ x : E3, ‖G x-A0‖ ≤ c/2)
    (hholder : ∀ x y : E3, ‖G x-G y‖ ≤ L*‖x-y‖^alpha) :
    ∀ x y : E3, ∀ i j : Fin 3,
      |((G x).inverse (EuclideanSpace.single j 1)) i -
        ((G y).inverse (EuclideanSpace.single j 1)) i| ≤
        (4*L/c^2)*‖x-y‖^alpha :=
/- SWARM_PROOF_BEGIN -/
by
  intro x y i j
  obtain ⟨a, b, ha, hb, ha_bound, hb_bound, hinv_bound⟩ :=
    positive_ball_inverse_control A0 c hc hA0 (G x) (G y) (hball x) (hball y)
  have hax : (G x).inverse = a.symm.toContinuousLinearMap := by
    rw [← ha, ContinuousLinearMap.inverse_equiv]
  have hby : (G y).inverse = b.symm.toContinuousLinearMap := by
    rw [← hb, ContinuousLinearMap.inverse_equiv]
  have hcoord (T : E3 →L[ℝ] E3) :
      |(T (EuclideanSpace.single j 1)) i| ≤ ‖T‖ := by
    calc
      |(T (EuclideanSpace.single j 1)) i| =
          ‖(T (EuclideanSpace.single j 1)) i‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖T (EuclideanSpace.single j 1)‖ := PiLp.norm_apply_le _ _
      _ ≤ ‖T‖ * ‖EuclideanSpace.single j 1‖ := T.le_opNorm _
      _ = ‖T‖ := by simp
  calc
    |((G x).inverse (EuclideanSpace.single j 1)) i -
        ((G y).inverse (EuclideanSpace.single j 1)) i| =
        |((a.symm.toContinuousLinearMap - b.symm.toContinuousLinearMap)
          (EuclideanSpace.single j 1)) i| := by rw [hax, hby]; simp
    _ ≤ ‖a.symm.toContinuousLinearMap - b.symm.toContinuousLinearMap‖ :=
      hcoord _
    _ ≤ (4 / c ^ 2) * ‖G x - G y‖ := hinv_bound
    _ ≤ (4 / c ^ 2) * (L * ‖x - y‖ ^ alpha) :=
      mul_le_mul_of_nonneg_left (hholder x y) (by positivity)
    _ = (4 * L / c ^ 2) * ‖x - y‖ ^ alpha := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
