import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** holder scale interpolation. -/
theorem holder_scale_interpolation 
    {V : Type*} [NormedAddCommGroup V] (f : E3 → V)
    (alpha beta H delta r : ℝ) (hb : 0 < beta) (hba : beta < alpha)
    (hH : 0 ≤ H) (hd : 0 ≤ delta) (hr : 0 < r)
    (hbound : ∀ x, ‖f x‖ ≤ delta)
    (hholder : ∀ x y, ‖f x-f y‖ ≤ H*‖x-y‖^alpha) :
    ∀ x y, ‖f x-f y‖ ≤ (H*r^(alpha-beta)+2*delta/r^beta)*‖x-y‖^beta :=
/- SWARM_PROOF_BEGIN -/
by
  intro x y
  by_cases hxy : x = y
  · subst y
    simp [hb.ne']
  · let d : ℝ := ‖x - y‖
    have hd0 : 0 ≤ d := by
      dsimp [d]
      exact norm_nonneg _
    have hdpos : 0 < d := by
      dsimp [d]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hr0 : 0 ≤ r := le_of_lt hr
    have he : 0 < alpha - beta := sub_pos.mpr hba
    have hrpow : 0 < r ^ beta := Real.rpow_pos_of_pos hr beta
    have hdpow : 0 ≤ d ^ beta := Real.rpow_nonneg hd0 beta
    have hterm : 0 ≤ H * r ^ (alpha - beta) :=
      mul_nonneg hH (Real.rpow_nonneg hr0 (alpha - beta))
    have hdeltaTerm : 0 ≤ 2 * delta / r ^ beta :=
      div_nonneg (mul_nonneg (by norm_num) hd) (le_of_lt hrpow)
    by_cases hnear : d ≤ r
    · have hpowsplit : d ^ alpha = d ^ (alpha - beta) * d ^ beta := by
        calc
          d ^ alpha = d ^ ((alpha - beta) + beta) := by congr 1; ring
          _ = d ^ (alpha - beta) * d ^ beta := Real.rpow_add hdpos _ _
      have hscale : d ^ alpha ≤ r ^ (alpha - beta) * d ^ beta := by
        rw [hpowsplit]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hd0 hnear he.le) hdpow
      calc
        ‖f x - f y‖ ≤ H * d ^ alpha := by
          simpa [d] using hholder x y
        _ ≤ H * (r ^ (alpha - beta) * d ^ beta) :=
          mul_le_mul_of_nonneg_left hscale hH
        _ = (H * r ^ (alpha - beta)) * d ^ beta := by ring
        _ ≤ (H * r ^ (alpha - beta) + 2 * delta / r ^ beta) * d ^ beta := by
          rw [add_mul]
          exact le_add_of_nonneg_right (mul_nonneg hdeltaTerm hdpow)
    · have hfar : r ≤ d := le_of_not_ge hnear
      have hpowcmp : r ^ beta ≤ d ^ beta := Real.rpow_le_rpow hr0 hfar hb.le
      have hratio : 1 ≤ d ^ beta / r ^ beta := (one_le_div hrpow).2 hpowcmp
      have hweighted : 2 * delta ≤ (2 * delta / r ^ beta) * d ^ beta := by
        calc
          2 * delta = (2 * delta) * 1 := by ring
          _ ≤ (2 * delta) * (d ^ beta / r ^ beta) :=
            mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num) hd)
          _ = (2 * delta / r ^ beta) * d ^ beta := by ring
      have hdiff : ‖f x - f y‖ ≤ 2 * delta := by
        calc
          ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
          _ ≤ delta + delta := add_le_add (hbound x) (hbound y)
          _ = 2 * delta := by ring
      calc
        ‖f x - f y‖ ≤ 2 * delta := hdiff
        _ ≤ (2 * delta / r ^ beta) * d ^ beta := hweighted
        _ ≤ (H * r ^ (alpha - beta) + 2 * delta / r ^ beta) * d ^ beta := by
          rw [add_mul]
          exact le_add_of_nonneg_left (mul_nonneg hterm hdpow)
        _ = (H * r ^ (alpha - beta) + 2 * delta / r ^ beta) *
              ‖x - y‖ ^ beta := by rfl
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
