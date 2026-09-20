import PoincareConjecture.Topology.FiberSaturation.Sphere
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

namespace PoincareConjecture.Topology.FiberSaturation
open Set Function

/-- An open embedding of the unit two-sphere into itself is surjective.
Compact range is closed, open embedding range is open, and `Sphere2` is connected.
Does not use invariance of domain, and does not apply to mere embeddings. -/
theorem sphere2_openEmbedding_surjective {f : Sphere2 → Sphere2}
    (hf : Topology.IsOpenEmbedding f) : Surjective f :=
/- SWARM_PROOF_BEGIN -/
by
  letI : CompactSpace Sphere2 :=
    isCompact_iff_compactSpace.mp
      (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  rw [← range_eq_univ]
  exact IsClopen.eq_univ ⟨(isCompact_range hf.continuous).isClosed, hf.isOpen_range⟩
    (range_nonempty f)
/- SWARM_PROOF_END -/

end PoincareConjecture.Topology.FiberSaturation
