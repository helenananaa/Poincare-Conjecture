import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open Set
open scoped ContDiff
noncomputable section
namespace MorganTianLib.SurgeryInterpolation

/-- **Math.** The explicit flat conformal profile used on the neck side. -/
def neckProfile (amplitude q s : ℝ) : ℝ := amplitude * expNegInvGlue (s / q)

/-- **Math.** A fixed cutoff, constant on neighborhoods of 1 and 2. -/
def neckCutoff (s : ℝ) : ℝ := 1 - Real.smoothTransition (2 * s - 5 / 2)

/-- **Math.** The profile is globally smooth, including its zero seam. -/
theorem neckProfile_contDiff (amplitude q : ℝ) :
    ContDiff ℝ ∞ (neckProfile amplitude q) := by
  exact contDiff_const.mul (expNegInvGlue.contDiff.comp (contDiff_id.div_const q))

/-- **Math.** Nonnegative amplitude makes the conformal factor contractive. -/
theorem neckProfile_nonneg {amplitude : ℝ} (ha : 0 ≤ amplitude) (q s : ℝ) :
    0 ≤ neckProfile amplitude q s := mul_nonneg ha (expNegInvGlue.nonneg _)

/-- **Math.** The profile is exactly zero on the retained side. -/
theorem neckProfile_eq_zero {q s : ℝ} (hq : 0 < q) (hs : s ≤ 0)
    (amplitude : ℝ) : neckProfile amplitude q s = 0 := by
  unfold neckProfile
  rw [expNegInvGlue.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hs hq.le), mul_zero]

/-- **Math.** Both interpolation weights are nonnegative and sum to one. -/
theorem neckCutoff_mem_Icc (s : ℝ) : neckCutoff s ∈ Icc (0 : ℝ) 1 := by
  have h0 := Real.smoothTransition.nonneg (2 * s - 5 / 2)
  have h1 := Real.smoothTransition.le_one (2 * s - 5 / 2)
  constructor <;> dsimp [neckCutoff] <;> linarith

/-- **Math.** Smoothness of the fixed cutoff. -/
theorem neckCutoff_contDiff : ContDiff ℝ ∞ neckCutoff := by
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const))

/-- **Math.** The left formula holds on an open neighborhood of the join at 1. -/
theorem neckCutoff_eq_one {s : ℝ} (hs : s ≤ 5 / 4) : neckCutoff s = 1 := by
  unfold neckCutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

/-- **Math.** The right formula holds on an open neighborhood of the join at 2. -/
theorem neckCutoff_eq_zero {s : ℝ} (hs : 7 / 4 ≤ s) : neckCutoff s = 0 := by
  unfold neckCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith), sub_self]

end MorganTianLib.SurgeryInterpolation
