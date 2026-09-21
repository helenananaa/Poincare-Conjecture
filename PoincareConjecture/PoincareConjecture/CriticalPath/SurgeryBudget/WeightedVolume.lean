import Mathlib

open scoped BigOperators

namespace PoincareConjecture.CriticalPath.SurgeryBudget

/-- Exponential growth between jumps plus a positive volume loss per cutting operation
bounds the total number of cuts. No local-finiteness assumption appears here. -/
theorem weighted_cut_budget
    (n : ℕ) (a T delta : ℝ) (time volume : ℕ → ℝ) (cuts : ℕ → ℕ)
    (ha : 0 ≤ a) (hdelta : 0 < delta) (htime0 : time 0 = 0)
    (horizon : ∀ i ≤ n, time i ≤ T)
    (hvolume : ∀ i ≤ n, 0 ≤ volume i)
    (hstep : ∀ i < n, volume (i + 1) ≤
      Real.exp (a * (time (i + 1) - time i)) * volume i - delta * (cuts i : ℝ)) :
    delta * ((∑ i ∈ Finset.range n, cuts i : ℕ) : ℝ) ≤
      Real.exp (a * T) * volume 0 := by
/- SWARM_PROOF_BEGIN -/
  have hcut_nonneg : ∀ i, 0 ≤ (cuts i : ℝ) := by
    intro i
    positivity
  have hweight_pos : ∀ i, 0 < Real.exp (-a * time i) := by
    intro i
    exact Real.exp_pos _
  have hweight_lower : ∀ i ≤ n,
      Real.exp (-a * T) ≤ Real.exp (-a * time i) := by
    intro i hi
    apply Real.exp_le_exp.mpr
    have hmul : a * time i ≤ a * T := mul_le_mul_of_nonneg_left (horizon i hi) ha
    calc
      -a * T = -(a * T) := by ring
      _ ≤ -(a * time i) := neg_le_neg hmul
      _ = -a * time i := by ring
  have htel : ∀ k ≤ n,
      delta * (∑ i ∈ Finset.range k,
          Real.exp (-a * time (i + 1)) * (cuts i : ℝ)) +
        Real.exp (-a * time k) * volume k ≤ volume 0 := by
    intro k hk
    induction k with
    | zero =>
        simp [htime0]
    | succ k ih =>
        have hklt : k < n := Nat.lt_of_succ_le hk
        have hstep' := hstep k hklt
        have hmul := mul_le_mul_of_nonneg_left hstep' (le_of_lt (hweight_pos (k + 1)))
        have hexp :
            Real.exp (-a * time (k + 1)) *
                Real.exp (a * (time (k + 1) - time k)) =
              Real.exp (-a * time k) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hstep_weighted :
            Real.exp (-a * time (k + 1)) * volume (k + 1) +
                delta * (Real.exp (-a * time (k + 1)) * (cuts k : ℝ)) ≤
              Real.exp (-a * time k) * volume k := by
          have hmul' :
              Real.exp (-a * time (k + 1)) * volume (k + 1) ≤
                (Real.exp (-a * time (k + 1)) *
                    Real.exp (a * (time (k + 1) - time k))) * volume k -
                  Real.exp (-a * time (k + 1)) * (delta * (cuts k : ℝ)) := by
            calc
              Real.exp (-a * time (k + 1)) * volume (k + 1) ≤
                  Real.exp (-a * time (k + 1)) *
                    (Real.exp (a * (time (k + 1) - time k)) * volume k -
                      delta * (cuts k : ℝ)) := hmul
              _ = (Real.exp (-a * time (k + 1)) *
                    Real.exp (a * (time (k + 1) - time k))) * volume k -
                  Real.exp (-a * time (k + 1)) * (delta * (cuts k : ℝ)) := by
                    ring
          rw [hexp] at hmul'
          nlinarith [hmul']
        calc
          delta * (∑ i ∈ Finset.range (k + 1),
              Real.exp (-a * time (i + 1)) * (cuts i : ℝ)) +
              Real.exp (-a * time (k + 1)) * volume (k + 1) =
            delta * (∑ i ∈ Finset.range k,
                Real.exp (-a * time (i + 1)) * (cuts i : ℝ)) +
              (Real.exp (-a * time (k + 1)) * volume (k + 1) +
                delta * (Real.exp (-a * time (k + 1)) * (cuts k : ℝ))) := by
                  rw [Finset.sum_range_succ]
                  ring
          _ ≤ delta * (∑ i ∈ Finset.range k,
                Real.exp (-a * time (i + 1)) * (cuts i : ℝ)) +
              Real.exp (-a * time k) * volume k := by
                linarith [hstep_weighted]
          _ ≤ volume 0 := ih (Nat.le_of_succ_le hk)
  have hweighted :
      delta * (∑ i ∈ Finset.range n,
          Real.exp (-a * time (i + 1)) * (cuts i : ℝ)) ≤ volume 0 := by
    have hfinal : 0 ≤ Real.exp (-a * time n) * volume n :=
      mul_nonneg (le_of_lt (hweight_pos n)) (hvolume n (le_refl n))
    linarith [htel n (le_refl n)]
  have hsum :
      (∑ i ∈ Finset.range n, Real.exp (-a * T) * (cuts i : ℝ)) ≤
        ∑ i ∈ Finset.range n,
          Real.exp (-a * time (i + 1)) * (cuts i : ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    exact mul_le_mul_of_nonneg_right (hweight_lower (i + 1) hi') (hcut_nonneg i)
  have hbase :
      delta * (∑ i ∈ Finset.range n, Real.exp (-a * T) * (cuts i : ℝ)) ≤
        volume 0 := by
    exact le_trans
      (mul_le_mul_of_nonneg_left hsum (le_of_lt hdelta)) hweighted
  have hbase' :
      delta * (Real.exp (-a * T) *
        ((∑ i ∈ Finset.range n, cuts i : ℕ) : ℝ)) ≤ volume 0 := by
    simpa only [Nat.cast_sum, Finset.mul_sum] using hbase
  have hexp_cancel : Real.exp (a * T) * Real.exp (-a * T) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  have hscaled := mul_le_mul_of_nonneg_left hbase' (le_of_lt (Real.exp_pos (a * T)))
  calc
    delta * ((∑ i ∈ Finset.range n, cuts i : ℕ) : ℝ) =
        1 * (delta * ((∑ i ∈ Finset.range n, cuts i : ℕ) : ℝ)) := by
          simp
    _ = (Real.exp (a * T) * Real.exp (-a * T)) *
          (delta * ((∑ i ∈ Finset.range n, cuts i : ℕ) : ℝ)) := by
            rw [hexp_cancel]
    _ = Real.exp (a * T) *
          (delta * (Real.exp (-a * T) *
            ((∑ i ∈ Finset.range n, cuts i : ℕ) : ℝ))) := by
              ring
    _ ≤ Real.exp (a * T) * volume 0 := hscaled
/- SWARM_PROOF_END -/

end PoincareConjecture.CriticalPath.SurgeryBudget
