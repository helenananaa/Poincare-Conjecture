import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
import PoincareConjecture.ParallelMath.Variational.PeakDistortion

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

/-- **Math.** Pointwise comparison on a time set passes to the actual parameter supremum. -/
theorem peakCost_exp_control_on {B : Type*} [Nonempty B]
    (F : ℝ → B → ℝ) (S : Set ℝ) (K : ℝ)
    (hn : ∀ t ∈ S, ∀ b, 0 ≤ F t b)
    (hb : ∀ t ∈ S, BddAbove (range (F t)))
    (hc : ∀ s ∈ S, ∀ t ∈ S, ∀ b, F t b ≤ Real.exp (K*|t-s|)*F s b) :
    (∀ t ∈ S, 0 ≤ PoincareConjecture.ParallelMath.Variational.peakCost (F t)) ∧
    ∀ s ∈ S, ∀ t ∈ S,
      PoincareConjecture.ParallelMath.Variational.peakCost (F t) ≤
        Real.exp (K*|t-s|)*PoincareConjecture.ParallelMath.Variational.peakCost (F s) :=
/- SWARM_PROOF_BEGIN -/
by
  constructor
  · intro t ht
    obtain ⟨b⟩ := ‹Nonempty B›
    exact (hn t ht b).trans (le_csSup (hb t ht) (mem_range_self b))
  · intro s hs t ht
    have hL : 0 ≤ Real.exp (K * |t - s|) := (Real.exp_pos _).le
    simpa using
      PoincareConjecture.ParallelMath.Variational.peakCost_transport
        (F s) (F t) (hb s hs) (hb t ht) (id : B → B) surjective_id
        (Real.exp (K * |t - s|)) 0 hL fun b => by
          simpa using hc s hs t ht b
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport
