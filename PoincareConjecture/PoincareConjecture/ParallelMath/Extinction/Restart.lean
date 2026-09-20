import PoincareConjecture.ParallelMath.Core
import PoincareConjecture.ParallelMath.Extinction.ComparisonInterface

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.ParallelMath
open Set

/-- Chaining the explicit comparison solution at an intermediate time.
No surgery-restart geometry. -/
theorem comparisonSolution_restart (q : ℝ → ℝ) (hq : Continuous q)
    (k a s t' t : ℝ) (hst' : s ≤ t') (ht't : t' ≤ t) :
    comparisonSolution q k a s t =
      comparisonSolution q k (comparisonSolution q k a s t') t' t :=
/- SWARM_PROOF_BEGIN -/
by
  -- Uniqueness is forward from `t'`; `s ≤ t'` records the restart order.
  have _ := hst'
  obtain ⟨-, -, huniq, -⟩ :=
    scalarComparison_solution_interface q hq k (comparisonSolution q k a s t') t'
  have hw_cont : ContinuousOn (comparisonSolution q k a s) (Ici t') :=
    fun x _ => (comparisonSolution_hasDerivAt q hq k a s x).continuousAt.continuousWithinAt
  have hw_deriv : ∀ x ∈ Ioi t',
      HasDerivAt (comparisonSolution q k a s)
        (-k - q x * comparisonSolution q k a s x) x :=
    fun x _ => comparisonSolution_hasDerivAt q hq k a s x
  exact huniq (comparisonSolution q k a s) hw_cont rfl hw_deriv (mem_Ici.mpr ht't)
/- SWARM_PROOF_END -/

end PoincareConjecture.ParallelMath
