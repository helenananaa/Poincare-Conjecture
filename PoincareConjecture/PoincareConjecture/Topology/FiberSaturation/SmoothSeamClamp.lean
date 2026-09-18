import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothBundle
open Set
open scoped ContDiff

/-- A smooth parameter map equal to t near c and frozen at c away from c.
Only the parameter at which a fiber automorphism is evaluated is changed;
the base coordinate of the resulting bundle map will remain t. -/
def seamClamp (c d t : ℝ) : ℝ :=
  c + Real.smoothTransition ((4*d^2 - (t-c)^2)/(3*d^2)) * (t-c)

theorem contDiff_seamClamp (c d : ℝ) : ContDiff ℝ ∞ (seamClamp c d) := by
  unfold seamClamp
  fun_prop

theorem seamClamp_eq_self {c d t : ℝ} (hd : 0 < d)
    (ht : t ∈ Icc (c-d) (c+d)) : seamClamp c d t = t := by
  have hs : (t-c)^2 ≤ d^2 := by
    nlinarith [mul_nonneg (show 0 ≤ d-(t-c) by linarith [ht.2])
      (show 0 ≤ d+(t-c) by linarith [ht.1])]
  have h : 1 ≤ (4*d^2 - (t-c)^2)/(3*d^2) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  simp [seamClamp, Real.smoothTransition.one_of_one_le h]

theorem seamClamp_eq_center {c d t : ℝ} (hd : 0 < d)
    (ht : t ≤ c-2*d ∨ c+2*d ≤ t) : seamClamp c d t = c := by
  have hs : 4*d^2 ≤ (t-c)^2 := by
    rcases ht with h | h
    · have hh := mul_self_le_mul_self
        (show 0 ≤ 2*d by positivity) (show 2*d ≤ c-t by linarith)
      nlinarith
    · have hh := mul_self_le_mul_self
        (show 0 ≤ 2*d by positivity) (show 2*d ≤ t-c by linarith)
      nlinarith
  have h : (4*d^2-(t-c)^2)/(3*d^2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  simp [seamClamp, Real.smoothTransition.zero_of_nonpos h]

theorem seamClamp_mem {c d : ℝ} (hd : 0 < d) (t : ℝ) :
    seamClamp c d t ∈ Ioo (c-2*d) (c+2*d) := by
  by_cases ht : t ∈ Ioo (c-2*d) (c+2*d)
  · let w := Real.smoothTransition ((4*d^2-(t-c)^2)/(3*d^2))
    have hw0 : 0 ≤ w := Real.smoothTransition.nonneg _
    have hw1 : w ≤ 1 := Real.smoothTransition.le_one _
    change c-2*d < c+w*(t-c) ∧ c+w*(t-c) < c+2*d
    by_cases htc : 0 ≤ t-c
    · have hlo := mul_nonneg hw0 htc
      have hhi := mul_le_mul_of_nonneg_right hw1 htc
      constructor <;> nlinarith [ht.1,ht.2]
    · have htneg : t-c ≤ 0 := le_of_not_ge htc
      have hlo := mul_le_mul_of_nonpos_right hw1 htneg
      have hhi := mul_nonpos_of_nonneg_of_nonpos hw0 htneg
      constructor <;> nlinarith [ht.1,ht.2]
  · have hout : t ≤ c-2*d ∨ c+2*d ≤ t := by
      simpa only [mem_Ioo, not_and_or, not_lt] using ht
    rw [seamClamp_eq_center hd hout]
    constructor <;> linarith

/-- In particular, the parameter clamp is the identity on an open collar. -/
theorem seamClamp_eqOn {c d : ℝ} (hd : 0 < d) :
    EqOn (seamClamp c d) id (Ioo (c-d) (c+d)) :=
  fun _ ht => seamClamp_eq_self hd (Ioo_subset_Icc_self ht)

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
