import PoincareConjecture.ParallelMath.Variational.AdmissibleTransfer
import PoincareConjecture.ParallelMath.Variational.CostGrowth
import PoincareConjecture.ParallelMath.Variational.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Variational
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- Uniform variation bounds for a fixed admissible family transfer to its
least cost on a regular time slab, without differentiating the infimum. -/
theorem leastCost_twoSided_growth {A : Type*} [Nonempty A]
    (F F' : A → ℝ → ℝ) (a b K : ℝ) (hab : a ≤ b) (hK : 0 ≤ K)
    (hc : ∀ x, ContinuousOn (F x) (Icc a b))
    (hn : ∀ x t, 0 ≤ F x t)
    (hd : ∀ x t, t ∈ Icc a b → HasDerivAt (F x) (F' x t) t)
    (hbnd : ∀ x t, t ∈ Icc a b → |F' x t| ≤ K * F x t) :
    Real.exp (-K*(b-a)) * leastCost (fun x => F x a) ≤ leastCost (fun x => F x b) ∧
      leastCost (fun x => F x b) ≤ Real.exp (K*(b-a)) * leastCost (fun x => F x a) :=
/- SWARM_PROOF_BEGIN -/
by
  -- Per-member exponential control; the infimum itself is never differentiated.
  have hmem : ∀ x,
      Real.exp (-K * (b - a)) * F x a ≤ F x b ∧
        F x b ≤ Real.exp (K * (b - a)) * F x a := fun x =>
    cost_twoSided_growth (F x) (F' x) a b K hab hK (hc x)
      (fun t _ => hn x t) (fun t ht => hd x t ht) (fun t ht => hbnd x t ht)
  have hFa : ∀ x, 0 ≤ F x a := fun x => hn x a
  have hFb : ∀ x, 0 ≤ F x b := fun x => hn x b
  have hL : 0 ≤ Real.exp (K * (b - a)) := (Real.exp_pos _).le
  constructor
  · -- Lower bound: transfer from time b back to time a, then invert the factor.
    have hcost : ∀ x, F x a ≤ Real.exp (K * (b - a)) * F x b + 0 := fun x => by
      have hx := (hmem x).1
      rw [neg_mul, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)] at hx
      linarith
    have htr :=
      leastCost_transfer (fun x => F x b) (fun x => F x a) hFb hFa id
        (Real.exp (K * (b - a))) 0 hL hcost
    rw [add_zero] at htr
    rw [neg_mul, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
    exact htr
  · -- Upper bound: transfer from time a forward to time b.
    have hcost : ∀ x, F x b ≤ Real.exp (K * (b - a)) * F x a + 0 := fun x => by
      linarith [(hmem x).2]
    simpa using
      leastCost_transfer (fun x => F x a) (fun x => F x b) hFa hFb id
        (Real.exp (K * (b - a))) 0 hL hcost
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Variational
