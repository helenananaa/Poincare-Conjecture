import Mathlib

open scoped BigOperators

namespace PoincareConjecture.CriticalPath.SurgeryBudget

/-- Each event cuts or discards a component; cuts can create at most one component each.
Telescoping the component balance controls all events, including pure discards. -/
theorem event_count_le_components_and_cuts
    (n initial : ℕ) (components cuts discards : ℕ → ℕ)
    (hinitial : components 0 = initial)
    (hbalance : ∀ i < n, components (i + 1) + discards i ≤ components i + cuts i)
    (hactive : ∀ i < n, 1 ≤ cuts i + discards i) :
    n ≤ initial + 2 * ∑ i ∈ Finset.range n, cuts i := by
/- SWARM_PROOF_BEGIN -/
  have htelescope : ∀ k ≤ n,
      components k + ∑ i ∈ Finset.range k, discards i ≤
        initial + ∑ i ∈ Finset.range k, cuts i := by
    intro k hk
    induction k with
    | zero =>
        simpa [hinitial]
    | succ k ih =>
        have hklt : k < n := Nat.lt_of_succ_le hk
        have hstep := hbalance k hklt
        have hprev := ih (Nat.le_of_lt hklt)
        simp only [Finset.sum_range_succ]
        omega
  have htelescope_n := htelescope n (le_refl n)
  have hsum : n ≤
      (∑ i ∈ Finset.range n, cuts i) +
        ∑ i ∈ Finset.range n, discards i := by
    have h := Finset.sum_le_sum (fun i hi => hactive i (Finset.mem_range.mp hi))
    simpa [Finset.sum_add_distrib] using h
  omega
/- SWARM_PROOF_END -/

end PoincareConjecture.CriticalPath.SurgeryBudget
