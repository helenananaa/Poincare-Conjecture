import PoincareConjecture.ParallelMath.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath
open Set Function Filter
open scoped BigOperators Topology

/-- The finite-extinction comparison barrier has the required differential equation. -/
theorem powerBarrier_hasDerivAt (alpha c a k t : ℝ)
    (hbase : 0 < t+c) (halpha : alpha ≠ 1) :
    HasDerivAt (powerBarrier alpha c a k)
      (-k + alpha/(t+c) * powerBarrier alpha c a k t) t :=
/- SWARM_PROOF_BEGIN -/
by
  have htc0 : t + c ≠ 0 := hbase.ne'
  have hid : HasDerivAt (fun s : ℝ => s + c) 1 t := (hasDerivAt_id' t).add_const c
  have hpowα : HasDerivAt (fun s : ℝ => (s + c) ^ alpha)
      (alpha * (t + c) ^ (alpha - 1)) t :=
    (hid.rpow_const (Or.inl htc0)).congr_deriv (by ring)
  have hpow1α : HasDerivAt (fun s : ℝ => (s + c) ^ (1 - alpha))
      ((1 - alpha) * (t + c) ^ (-alpha)) t := by
    refine (hid.rpow_const (Or.inl htc0)).congr_deriv ?_
    simp only [one_mul]
    refine congr_arg ((1 - alpha) * ·) ?_
    refine congr_arg ((t + c) ^ ·) ?_
    ring
  have hinner : HasDerivAt
      (fun s : ℝ =>
        a / c ^ alpha - k / (1 - alpha) *
          ((s + c) ^ (1 - alpha) - c ^ (1 - alpha)))
      (-k * (t + c) ^ (-alpha)) t := by
    refine (HasDerivAt.const_sub (a / c ^ alpha)
      (HasDerivAt.const_mul (k / (1 - alpha))
        (hpow1α.sub_const (c ^ (1 - alpha))))).congr_deriv ?_
    have h1α : (1 - alpha : ℝ) ≠ 0 := sub_ne_zero.2 (Ne.symm halpha)
    calc
      -(k / (1 - alpha) * ((1 - alpha) * (t + c) ^ (-alpha)))
          = -(k / (1 - alpha) * (1 - alpha) * (t + c) ^ (-alpha)) := by
            rw [← mul_assoc]
      _ = -(k * (t + c) ^ (-alpha)) := by rw [div_mul_cancel₀ _ h1α]
      _ = -k * (t + c) ^ (-alpha) := by rw [neg_mul]
  unfold powerBarrier
  refine (hpowα.mul hinner).congr_deriv ?_
  set I :=
    a / c ^ alpha - k / (1 - alpha) * ((t + c) ^ (1 - alpha) - c ^ (1 - alpha))
  have hdiv : (t + c) ^ alpha / (t + c) = (t + c) ^ (alpha - 1) := by
    nth_rw 2 [← Real.rpow_one (t + c)]
    exact (Real.rpow_sub hbase alpha 1).symm
  have hscale :
      alpha / (t + c) * ((t + c) ^ alpha * I) =
        alpha * (t + c) ^ (alpha - 1) * I := by
    rw [← mul_assoc, div_mul_eq_mul_div, mul_div_assoc, hdiv, mul_assoc]
  have hcancel :
      (t + c) ^ alpha * (-k * (t + c) ^ (-alpha)) = -k := by
    calc
      (t + c) ^ alpha * (-k * (t + c) ^ (-alpha))
          = -k * ((t + c) ^ alpha * (t + c) ^ (-alpha)) := by ring
      _ = -k * (t + c) ^ (alpha + -alpha) := by rw [Real.rpow_add hbase]
      _ = -k * (t + c) ^ (0 : ℝ) := by rw [add_neg_cancel]
      _ = -k := by rw [Real.rpow_zero, mul_one]
  rw [hscale, hcancel]
  ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath
