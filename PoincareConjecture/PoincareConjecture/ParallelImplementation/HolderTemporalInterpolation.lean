import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.HolderScaleInterpolation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.HolderTemporalInterpolation
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Parabolic time smallness gives a quantitative weaker spatial Holder bound. -/
theorem holder_difference_time_interpolation
    {V : Type*} [NormedAddCommGroup V] (f g : E3 → V)
    (alpha beta K h : ℝ) (hb : 0 < beta) (hba : beta < alpha)
    (hK : 0 ≤ K) (hh : 0 < h)
    (hf : ∀ x y, ‖f x-f y‖ ≤ K*‖x-y‖^alpha)
    (hg : ∀ x y, ‖g x-g y‖ ≤ K*‖x-y‖^alpha)
    (hdiff : ∀ x, ‖f x-g x‖ ≤ K*h^(alpha/2)) :
    ∀ x y, ‖(f x-g x)-(f y-g y)‖ ≤
      (4*K*h^((alpha-beta)/2))*‖x-y‖^beta :=
/- SWARM_PROOF_BEGIN -/
by
  let u : E3 → V := fun x => f x - g x
  let r : ℝ := h ^ ((1 : ℝ) / 2)
  let δ : ℝ := K * h ^ (alpha / 2)
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact mul_nonneg hK (Real.rpow_nonneg (le_of_lt hh) _)
  have hr : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos hh _
  have hu_bound : ∀ x, ‖u x‖ ≤ δ := by
    intro x
    dsimp [u, δ]
    exact hdiff x
  have hu_holder : ∀ x y, ‖u x - u y‖ ≤ (2 * K) * ‖x - y‖ ^ alpha := by
    intro x y
    dsimp [u]
    calc
      ‖(f x - g x) - (f y - g y)‖ = ‖(f x - f y) - (g x - g y)‖ := by
        congr 1; abel
      _ ≤ ‖f x - f y‖ + ‖g x - g y‖ := norm_sub_le _ _
      _ ≤ K * ‖x - y‖ ^ alpha + K * ‖x - y‖ ^ alpha :=
        add_le_add (hf x y) (hg x y)
      _ = (2 * K) * ‖x - y‖ ^ alpha := by ring
  have hinterp :=
    MorganTianLib.MetricCoefficient.holder_scale_interpolation u alpha beta (2 * K) δ r
      hb hba (mul_nonneg (by norm_num) hK) hδ hr hu_bound hu_holder
  have hrpow : r ^ (alpha - beta) = h ^ ((alpha - beta) / 2) := by
    dsimp [r]
    calc
      (h ^ ((1 : ℝ) / 2)) ^ (alpha - beta) =
          h ^ (((1 : ℝ) / 2) * (alpha - beta)) :=
        (Real.rpow_mul hh.le _ _).symm
      _ = h ^ ((alpha - beta) / 2) := by congr 1; ring
  have hden : r ^ beta = h ^ (beta / 2) := by
    dsimp [r]
    calc
      (h ^ ((1 : ℝ) / 2)) ^ beta = h ^ (((1 : ℝ) / 2) * beta) :=
        (Real.rpow_mul hh.le _ _).symm
      _ = h ^ (beta / 2) := by congr 1; ring
  have hratio : h ^ (alpha / 2) / r ^ beta = h ^ ((alpha - beta) / 2) := by
    rw [hden]
    calc
      h ^ (alpha / 2) / h ^ (beta / 2) = h ^ (alpha / 2 - beta / 2) :=
        (Real.rpow_sub hh _ _).symm
      _ = h ^ ((alpha - beta) / 2) := by congr 1; ring
  have hcoeff :
      2 * K * r ^ (alpha - beta) + 2 * δ / r ^ beta =
        4 * K * h ^ ((alpha - beta) / 2) := by
    rw [hrpow]
    have hsecond : 2 * δ / r ^ beta = 2 * K * h ^ ((alpha - beta) / 2) := by
      dsimp [δ]
      calc
        2 * (K * h ^ (alpha / 2)) / r ^ beta =
            2 * K * (h ^ (alpha / 2) / r ^ beta) := by ring
        _ = 2 * K * h ^ ((alpha - beta) / 2) := by rw [hratio]
    rw [hsecond]
    ring
  intro x y
  calc
    ‖(f x - g x) - (f y - g y)‖ = ‖u x - u y‖ := by rfl
    _ ≤ (2 * K * r ^ (alpha - beta) + 2 * δ / r ^ beta) * ‖x - y‖ ^ beta :=
      hinterp x y
    _ = (4 * K * h ^ ((alpha - beta) / 2)) * ‖x - y‖ ^ beta := by
      rw [hcoeff]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.HolderTemporalInterpolation
