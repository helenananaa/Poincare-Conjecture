import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.NonlinearFourPointEstimate
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

/-- **Math.** holder nonlinearity difference. -/
theorem holder_nonlinearity_difference {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (s : Set E) (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hbound : ∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ M)
    (hLip : ∀ x ∈ s, ∀ y ∈ s, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ L*‖x-y‖)
    (u v : E3 → E) (hu : ∀ x, u x ∈ s) (hv : ∀ x, v x ∈ s)
    (alpha H D delta : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D) (hdelta : 0 ≤ delta)
    (hclose : ∀ x, ‖u x-v x‖ ≤ delta)
    (huHolder : ∀ x y, ‖u x-u y‖ ≤ H*‖x-y‖^alpha)
    (hvHolder : ∀ x y, ‖v x-v y‖ ≤ H*‖x-y‖^alpha)
    (hdiffHolder : ∀ x y, ‖(u x-v x)-(u y-v y)‖ ≤ D*‖x-y‖^alpha) :
    ∀ x y, ‖(f (u x)-f (v x))-(f (u y)-f (v y))‖ ≤
      (M*D+2*L*H*delta)*‖x-y‖^alpha :=
/- SWARM_PROOF_BEGIN -/
by
  intro x y
  let r : ℝ := ‖x - y‖ ^ alpha
  have hr : 0 ≤ r := by
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hfour := nonlinear_four_point_estimate f s hs hf M L hM hL hbound hLip
    (u x) (v x) (u y) (v y) (hu x) (hv x) (hu y) (hv y)
  have hfirst := hdiffHolder x y
  have hux := huHolder x y
  have hvx := hvHolder x y
  have hclosey := hclose y
  have hsum : ‖u x - u y‖ + ‖v x - v y‖ ≤ (2 * H) * r := by
    dsimp [r]
    calc
      ‖u x - u y‖ + ‖v x - v y‖ ≤ H * ‖x - y‖ ^ alpha + H * ‖x - y‖ ^ alpha :=
        add_le_add hux hvx
      _ = (2 * H) * ‖x - y‖ ^ alpha := by ring
  have hcoef_nonneg : 0 ≤ L * ((2 * H) * r) :=
    mul_nonneg hL (mul_nonneg (by positivity) hr)
  have hsecond : L * (‖u x - u y‖ + ‖v x - v y‖) * ‖u y - v y‖ ≤
      L * ((2 * H) * r) * delta := by
    calc
      L * (‖u x - u y‖ + ‖v x - v y‖) * ‖u y - v y‖ ≤
          (L * ((2 * H) * r)) * ‖u y - v y‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left hsum hL
      _ ≤ (L * ((2 * H) * r)) * delta :=
        mul_le_mul_of_nonneg_left hclosey hcoef_nonneg
  have hfirst' : M * ‖(u x - v x) - (u y - v y)‖ ≤ M * (D * r) := by
    exact mul_le_mul_of_nonneg_left hfirst hM
  calc
    ‖(f (u x) - f (v x)) - (f (u y) - f (v y))‖ =
        ‖f (u x) - f (v x) - f (u y) + f (v y)‖ := by congr 1 <;> abel
    _ ≤ M * ‖(u x - v x) - (u y - v y)‖ +
        L * (‖u x - u y‖ + ‖v x - v y‖) * ‖u y - v y‖ := hfour
    _ ≤ M * (D * r) + L * ((2 * H) * r) * delta := add_le_add hfirst' hsecond
    _ = (M * D + 2 * L * H * delta) * r := by
      dsimp [r]
      ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
