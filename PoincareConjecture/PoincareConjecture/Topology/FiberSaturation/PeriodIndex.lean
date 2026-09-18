import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

set_option autoImplicit false
namespace PoincareConjecture.Topology.FiberSaturation.SmoothBundle
open Set

/-- The integer period and its half-open representative, including negative times. -/
noncomputable def periodIndex (L t : ℝ) : ℤ := ⌊t/L⌋
noncomputable def periodRemainder (L t : ℝ) : ℝ := t - (periodIndex L t : ℝ)*L

theorem periodRemainder_mem {L : ℝ} (hL : 0 < L) (t : ℝ) :
    periodRemainder L t ∈ Ico (0 : ℝ) L := by
  have h1 := (le_div_iff₀ hL).mp (Int.floor_le (t/L))
  have h2 := (div_lt_iff₀ hL).mp (Int.lt_floor_add_one (t/L))
  change 0 ≤ t - (⌊t/L⌋ : ℝ)*L ∧ t - (⌊t/L⌋ : ℝ)*L < L
  constructor <;> nlinarith

theorem periodIndex_eq {L t : ℝ} (hL : 0 < L) (n : ℤ)
    (ht : t - (n : ℝ)*L ∈ Ico (0 : ℝ) L) : periodIndex L t = n := by
  apply Int.floor_eq_iff.mpr
  constructor
  · exact (le_div_iff₀ hL).mpr (by linarith [ht.1])
  · exact (div_lt_iff₀ hL).mpr (by nlinarith [ht.2])

theorem periodIndex_add_periods {L : ℝ} (hL : 0 < L) (t : ℝ) (n : ℤ) :
    periodIndex L (t+(n : ℝ)*L) = periodIndex L t+n := by
  unfold periodIndex
  rw [add_div, mul_div_cancel_right₀ _ hL.ne', Int.floor_add_intCast]

theorem periodRemainder_add_periods {L : ℝ} (hL : 0 < L) (t : ℝ) (n : ℤ) :
    periodRemainder L (t+(n : ℝ)*L) = periodRemainder L t := by
  unfold periodRemainder
  rw [periodIndex_add_periods hL]
  push_cast
  ring

theorem periodIndex_zeroCell {L t : ℝ} (hL : 0 < L) (ht : t ∈ Ico (0 : ℝ) L) :
    periodIndex L t = 0 := by
  apply periodIndex_eq hL 0
  simpa using ht

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
