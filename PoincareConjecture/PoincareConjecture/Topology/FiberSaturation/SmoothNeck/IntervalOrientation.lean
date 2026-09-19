import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.Core
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothNeck
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- A cut strictly inside any finite neck admits a two-sided normalized strip,
including reversed axial orientation. -/
theorem exists_oriented_strip_width (a b c s : ℝ) (ha : a < c) (hb : c < b)
    (hs : s = 1 ∨ s = -1) :
    ∃ r : ℝ, 0 < r ∧
      (∀ t ∈ Ioo (-1 : ℝ) 1, c + s*r*t ∈ Ioo a b) ∧
      (∀ t : ℝ, (s * (c + s*r*t - c) ≤ 0 ↔ t ≤ 0)) :=
/- SWARM_PROOF_BEGIN -/
by
  let r : ℝ := min (c - a) (b - c) / 2
  have hca : 0 < c - a := sub_pos.mpr ha
  have hbc : 0 < b - c := sub_pos.mpr hb
  have hr : 0 < r := half_pos (lt_min hca hbc)
  have hr_lt_ca : r < c - a :=
    (div_le_div_of_nonneg_right (min_le_left (c - a) (b - c))
        (by positivity : (0 : ℝ) ≤ 2)).trans_lt (half_lt_self hca)
  have hr_lt_bc : r < b - c :=
    (div_le_div_of_nonneg_right (min_le_right (c - a) (b - c))
        (by positivity : (0 : ℝ) ≤ 2)).trans_lt (half_lt_self hbc)
  have hleft : a < c - r := by linarith
  have hright : c + r < b := by linarith
  refine ⟨r, hr, ?strip, ?side⟩
  · intro t ht
    have ht1 : -1 < t := ht.1
    have ht2 : t < 1 := ht.2
    rcases hs with rfl | rfl
    · have hlo : -r < r * t := by
        have := mul_lt_mul_of_pos_left ht1 hr
        simpa using this
      have hhi : r * t < r := by
        have := mul_lt_mul_of_pos_left ht2 hr
        simpa using this
      exact ⟨by linarith, by linarith⟩
    · have hrneg : -r < 0 := neg_neg_of_pos hr
      have hlo : -r < (-r) * t := by
        have := mul_lt_mul_of_neg_left ht2 hrneg
        simpa using this
      have hhi : (-r) * t < r := by
        have := mul_lt_mul_of_neg_left ht1 hrneg
        simpa [mul_neg_one, neg_neg, mul_one] using this
      exact ⟨by linarith, by linarith⟩
  · intro t
    rcases hs with rfl | rfl
    · have hsimp : (1 : ℝ) * (c + 1 * r * t - c) = r * t := by ring
      rw [hsimp]
      simpa [mul_zero] using (mul_le_mul_iff_of_pos_left (a := r) (b := t) (c := 0) hr)
    · have hsimp : (-1 : ℝ) * (c + (-1) * r * t - c) = r * t := by ring
      rw [hsimp]
      simpa [mul_zero] using (mul_le_mul_iff_of_pos_left (a := r) (b := t) (c := 0) hr)
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothNeck
