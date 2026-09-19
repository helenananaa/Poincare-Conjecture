import Mathlib
import PoincareConjecture.ParallelMath.Core
import ReferenceBridges.Quantitative.OpenCoverChains
import PoincareConjecture.ParallelMath.SurgeryMetric.LengthGluing
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PoincareConjecture.ParallelMath.Quantitative.Reference
open Set Function Filter
open scoped BigOperators Topology Manifold ContDiff

/-- **Math.** Uniformly Lipschitz compatible maps on an open cover glue globally on a true length space. -/
theorem lipschitz_gluing_on_lengthSpace_open_cover {ι X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] [Shared.LengthSpace X]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (f : ι → X → Y) (L : NNReal)
    (hcompat : ∀ i j x, x ∈ U i → x ∈ U j → f i x = f j x)
    (hlocal : ∀ i, LipschitzOnWith L (f i) (U i)) :
    ∃ F : X → Y, (∀ i x, x ∈ U i → F x = f i x) ∧ LipschitzWith L F :=
/- SWARM_PROOF_BEGIN -/
by
  -- Glue locally Lipschitz pieces using ambient distance as the piece cost.
  refine lipschitz_gluing_of_approximate_piece_chains
    U hcover f (fun _ x y => dist x y) L hcompat ?hlocal ?hchains
  · -- LipschitzOnWith supplies the local distance bound on each open set.
    intro i x y hx hy
    exact (hlocal i).dist_le_mul x hx y hy
  · -- Length-space open-cover chains supply the missing geometric hypothesis.
    intro x y epsilon he
    exact lengthSpace_open_cover_piece_chains U hU hcover x y epsilon he
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative.Reference
