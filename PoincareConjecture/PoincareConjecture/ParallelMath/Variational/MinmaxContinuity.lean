import PoincareConjecture.ParallelMath.Variational.PeakDistortion
import PoincareConjecture.ParallelMath.Variational.WidthContinuity
import PoincareConjecture.ParallelMath.Variational.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Variational
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- A uniform distortion estimate yields continuity of infimum-supremum width,
without attainment of either extrema or compactness of the parameter types. -/
theorem leastPeak_continuous_of_exp_distortion {A B : Type*} [Nonempty A] [Nonempty B]
    (F : ℝ → A → B → ℝ) (hn : ∀ t a b, 0 ≤ F t a b)
    (hb : ∀ t a, BddAbove (range (F t a))) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ s t a b, F t a b ≤ Real.exp (K*|t-s|) * F s a b) :
    Continuous (fun t => leastPeak (F t)) :=
/- SWARM_PROOF_BEGIN -/
by
  have hpeak : ∀ t a, 0 ≤ peakCost (F t a) := fun t a => by
    obtain ⟨b⟩ := ‹Nonempty B›
    exact (hn t a b).trans (le_csSup (hb t a) (mem_range_self b))
  have hcontrol : ∀ s t a,
      peakCost (F t a) ≤ Real.exp (K * |t - s|) * peakCost (F s a) := fun s t a => by
    have hKd : 0 ≤ K * |t - s| := mul_nonneg hK (abs_nonneg _)
    have hL : 0 ≤ Real.exp (K * |t - s|) :=
      le_trans zero_le_one (Real.one_le_exp hKd)
    simpa using
      peakCost_transport (F s a) (F t a) (hb s a) (hb t a) (id : B → B)
        surjective_id (Real.exp (K * |t - s|)) 0 hL fun b => by
          simpa using h s t a b
  exact leastCost_continuous_of_exp_distortion
    (fun t a => peakCost (F t a)) hpeak K hK hcontrol
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Variational
