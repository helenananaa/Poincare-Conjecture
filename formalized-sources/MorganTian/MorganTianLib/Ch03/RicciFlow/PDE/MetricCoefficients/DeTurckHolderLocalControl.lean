import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.FullDeTurckNonlinearity
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalC2DerivativeControl
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.HolderNonlinearityDifference
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "J3" => (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)
local notation "M3" => Fin 3 → Fin 3 → ℝ
local notation "E9" => EuclideanSpace ℝ (Fin 3 × Fin 3)

/-- **Math.** deturck holder local control. -/
theorem deturck_holder_local_control (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3)
    (c : ℝ) (hc : 0 < c) (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v) :
    ∃ r K : ℝ, 0 < r ∧ 0 < K ∧ ∀ (u v : E3 → J3),
      (∀ x, u x ∈ Metric.ball (A,P) r) → (∀ x, v x ∈ Metric.ball (A,P) r) →
      ∀ (alpha H D delta : ℝ), 0 ≤ H → 0 ≤ D → 0 ≤ delta →
      (∀ x, ‖u x-v x‖ ≤ delta) →
      (∀ x y, ‖u x-u y‖ ≤ H*‖x-y‖^alpha) →
      (∀ x y, ‖v x-v y‖ ≤ H*‖x-y‖^alpha) →
      (∀ x y, ‖(u x-v x)-(u y-v y)‖ ≤ D*‖x-y‖^alpha) →
      ∀ x y, ‖(fullDeTurckNonlinearity (u x)-fullDeTurckNonlinearity (v x))-
        (fullDeTurckNonlinearity (u y)-fullDeTurckNonlinearity (v y))‖ ≤
        K*(D+H*delta)*‖x-y‖^alpha :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  letI : NormedAddCommGroup E9 := inferInstance
  letI : InnerProductSpace ℝ E9 := inferInstance
  have hsmooth := full_deturck_nonlinearity_smooth A P c hc hA
  obtain ⟨r, M, L, hr, hM, hL, hderiv, hLip⟩ :=
    local_C2_derivative_control fullDeTurckNonlinearity (A, P)
      (hsmooth.of_le (by norm_cast))
  let s : Set J3 := Metric.ball (A, P) r
  have hsconvex : Convex ℝ s := by
    exact convex_ball _ _
  refine ⟨r, M + 2 * L, hr, ?_, ?_⟩
  · positivity
  · intro u v hu hv alpha H D delta hH hD hdelta hclose huHolder hvHolder hdiffHolder
    have hmain := holder_nonlinearity_difference
      (E := J3) (F := E9) fullDeTurckNonlinearity s hsconvex
      (fun q hq => (hderiv q hq).1)
      M L (le_of_lt hM) (le_of_lt hL)
      (fun q hq => (hderiv q hq).2) hLip
      u v hu hv alpha H D delta hH hD hdelta hclose huHolder hvHolder hdiffHolder
    have hcoeff : M * D + 2 * L * H * delta ≤ (M + 2 * L) * (D + H * delta) := by
      have hmhδ : 0 ≤ M * (H * delta) := mul_nonneg (le_of_lt hM) (mul_nonneg hH hdelta)
      have h2ld : 0 ≤ (2 * L) * D :=
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hL)) hD
      nlinarith
    intro x y
    calc
      ‖(fullDeTurckNonlinearity (u x) - fullDeTurckNonlinearity (v x)) -
          (fullDeTurckNonlinearity (u y) - fullDeTurckNonlinearity (v y))‖
          ≤ (M * D + 2 * L * H * delta) * ‖x - y‖ ^ alpha := hmain x y
      _ ≤ ((M + 2 * L) * (D + H * delta)) * ‖x - y‖ ^ alpha :=
        mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (norm_nonneg _) _)
      _ = (M + 2 * L) * (D + H * delta) * ‖x - y‖ ^ alpha := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
