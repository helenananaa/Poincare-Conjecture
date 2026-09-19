import Mathlib
import PoincareConjecture.ParallelMath.Core
import Shared.MetricGeometry.LengthSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PoincareConjecture.ParallelMath.Quantitative.Reference
open Set Function Filter
open scoped BigOperators Topology Manifold ContDiff

/-- **Math.** A genuine intrinsic metric supplies finite paths arbitrarily close to its distance. -/
theorem exists_short_path_of_lengthSpace {X : Type*} [PseudoMetricSpace X]
    [Shared.LengthSpace X] (x y : X) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ γ : Path x y, Shared.pathLength γ ≠ ⊤ ∧
      (Shared.pathLength γ).toReal < dist x y + epsilon :=
/- SWARM_PROOF_BEGIN -/
by
  -- The intrinsic distance is finite in a pseudo-metric space, and strictly
  -- below the finite comparison bound `ENNReal.ofReal (dist x y + epsilon)`.
  have hbound : edist x y < ENNReal.ofReal (dist x y + epsilon) := by
    rw [edist_lt_ofReal]
    linarith
  -- Length-space axiom: the distance is the infimum of path lengths (not
  -- necessarily attained). Rewrite the bound in that form.
  rw [Shared.LengthSpace.edist_eq_iInf_pathLength] at hbound
  -- Extract a path whose length lies strictly below the finite bound.
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hbound
  -- Finiteness of the length follows from comparison with a finite `ofReal`.
  have hfin : Shared.pathLength γ ≠ ⊤ := ne_top_of_lt hγ
  refine ⟨γ, hfin, ?_⟩
  -- Convert to a real inequality only after finiteness is known.
  exact (ENNReal.lt_ofReal_iff_toReal_lt hfin).mp hγ
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative.Reference
