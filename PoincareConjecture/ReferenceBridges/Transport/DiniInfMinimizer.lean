import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
import MorganTianLib.Ch02.ForwardDifference
import PoincareConjecture.ParallelMath.Variational.InfimumApproximation

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport.Reference
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

/-- **Math.** At an attained minimum, the same competitor gives the upper right derivative bound for the infimum. -/
theorem leastCost_forwardDiff_of_minimizer {A : Type*} [Nonempty A]
    (F : ℝ → A → ℝ) (s c : ℝ) (hn : ∀ t a, 0 ≤ F t a)
    (a : A) (ha : F s a = PoincareConjecture.ParallelMath.Variational.leastCost (F s))
    (hd : MorganTianLib.ForwardDiffQuotientLE (fun t => F t a) s c) :
    MorganTianLib.ForwardDiffQuotientLE
      (fun t => PoincareConjecture.ParallelMath.Variational.leastCost (F t)) s c :=
/- SWARM_PROOF_BEGIN -/
by
  intro r hr
  -- Right slopes of the infimum are dominated by those of the attained competitor.
  filter_upwards [hd r hr, self_mem_nhdsWithin] with t ht hts
  have hbdd : BddBelow (range (F t)) := ⟨0, by rintro _ ⟨b, rfl⟩; exact hn t b⟩
  have hle : PoincareConjecture.ParallelMath.Variational.leastCost (F t) ≤ F t a :=
    csInf_le hbdd (mem_range_self a)
  have hnum :
      PoincareConjecture.ParallelMath.Variational.leastCost (F t) -
          PoincareConjecture.ParallelMath.Variational.leastCost (F s) ≤
        F t a - F s a := by
    rw [← ha]
    exact sub_le_sub_right hle _
  have hpos : 0 < t - s := sub_pos.mpr hts
  have hslope :
      slope (fun u => PoincareConjecture.ParallelMath.Variational.leastCost (F u)) s t ≤
        slope (fun u => F u a) s t := by
    rw [slope_def_field, slope_def_field]
    exact (div_le_div_iff_of_pos_right hpos).mpr hnum
  exact hslope.trans_lt ht
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport.Reference
