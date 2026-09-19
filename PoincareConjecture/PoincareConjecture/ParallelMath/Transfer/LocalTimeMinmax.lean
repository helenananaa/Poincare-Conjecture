import PoincareConjecture.ParallelMath.Transfer.LocalTimeInfimum
import PoincareConjecture.ParallelMath.Variational.PeakDistortion
import PoincareConjecture.ParallelMath.Transfer.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- Local-in-time exponential control gives relative continuity of the actual infimum-supremum expression. -/
theorem leastPeak_continuousOn_time_interval {A B : Type*} [Nonempty A] [Nonempty B]
    (F : ℝ → A → B → ℝ) (a b K : ℝ) (hab : a ≤ b) (hK : 0 ≤ K)
    (hn : ∀ t ∈ Icc a b, ∀ u v, 0 ≤ F t u v)
    (hb : ∀ t ∈ Icc a b, ∀ u, BddAbove (range (F t u)))
    (hd : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ u v,
      F t u v ≤ Real.exp (K*|t-s|)*F s u v) :
    ContinuousOn (fun t => Variational.leastPeak (F t)) (Icc a b) :=
/- SWARM_PROOF_BEGIN -/
by
  have hpeak : ∀ t ∈ Icc a b, ∀ u, 0 ≤ Variational.peakCost (F t u) := fun t ht u => by
    obtain ⟨v⟩ := ‹Nonempty B›
    exact (hn t ht u v).trans (le_csSup (hb t ht u) (mem_range_self v))
  have hcontrol : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ u,
      Variational.peakCost (F t u) ≤ Real.exp (K * |t - s|) * Variational.peakCost (F s u) :=
    fun s hs t ht u => by
      have hKd : 0 ≤ K * |t - s| := mul_nonneg hK (abs_nonneg _)
      have hL : 0 ≤ Real.exp (K * |t - s|) :=
        le_trans zero_le_one (Real.one_le_exp hKd)
      simpa using
        Variational.peakCost_transport (F s u) (F t u) (hb s hs u) (hb t ht u) (id : B → B)
          surjective_id (Real.exp (K * |t - s|)) 0 hL fun v => by
            simpa using hd s hs t ht u v
  exact leastCost_continuousOn_time_interval
    (fun t u => Variational.peakCost (F t u)) a b K hab hK hpeak hcontrol
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
