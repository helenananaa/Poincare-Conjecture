import PoincareConjecture.ParallelMath.Variational.PeakDistortion
import PoincareConjecture.ParallelMath.Variational.AdmissibleTransfer
import PoincareConjecture.ParallelMath.Variational.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Variational
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- Transport a minmax sweepout family with independent maps on admissible
sweepouts and their parameters; no minimizing sweepout is assumed. -/
theorem leastPeak_transfer {A B C D : Type*} [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (F : A → B → ℝ) (G : C → D → ℝ)
    (hF : ∀ a b, 0 ≤ F a b) (hG : ∀ c d, 0 ≤ G c d)
    (bF : ∀ a, BddAbove (range (F a))) (bG : ∀ c, BddAbove (range (G c)))
    (T : A → C) (P : A → B → D) (hP : ∀ a, Surjective (P a))
    (L δ : ℝ) (hL : 0 ≤ L)
    (hcost : ∀ a b, G (T a) (P a b) ≤ L * F a b + δ) :
    leastPeak G ≤ L * leastPeak F + δ :=
/- SWARM_PROOF_BEGIN -/
by
  have hFpeak : ∀ a, 0 ≤ peakCost (F a) := fun a => by
    obtain ⟨b⟩ := ‹Nonempty B›
    exact (hF a b).trans (le_csSup (bF a) (mem_range_self b))
  have hGpeak : ∀ c, 0 ≤ peakCost (G c) := fun c => by
    obtain ⟨d⟩ := ‹Nonempty D›
    exact (hG c d).trans (le_csSup (bG c) (mem_range_self d))
  have hpeak : ∀ a, peakCost (G (T a)) ≤ L * peakCost (F a) + δ := fun a =>
    peakCost_transport (F a) (G (T a)) (bF a) (bG (T a)) (P a) (hP a) L δ hL (hcost a)
  exact leastCost_transfer (fun a => peakCost (F a)) (fun c => peakCost (G c))
    hFpeak hGpeak T L δ hL hpeak
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Variational
