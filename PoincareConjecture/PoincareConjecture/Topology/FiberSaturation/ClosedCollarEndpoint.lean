import PoincareConjecture.Topology.FiberSaturation.ClosedCollar
import PoincareConjecture.Topology.FiberSaturation.FrontierComponents
import PoincareConjecture.Topology.FiberSaturation.Sphere

set_option autoImplicit false

namespace PoincareConjecture.Topology.FiberSaturation
open Set

variable {Y : Type*} [TopologicalSpace Y] {a b : ℝ}

/-- Endpoint (or any displayed) fiber of a closed collar is a connected
component of the finite displayed union, not of the whole ambient frontier. -/
theorem closed_collar_displayed_fiber_component
    {f : Sphere2 × Icc a b → Y} (hf : Topology.IsEmbedding f)
    {T : Set (Icc a b)} (hT : T.Finite)
    (t : Icc a b) (ht : t ∈ T) (x : Sphere2) :
    connectedComponentIn (f '' (univ ×ˢ T)) (f (x, t)) =
      f '' (univ ×ˢ ({t} : Set (Icc a b))) :=
/- SWARM_PROOF_BEGIN -/
by
  have hx : (x, t) ∈ (univ : Set Sphere2) ×ˢ T := ⟨mem_univ _, ht⟩
  rw [← embedding_image_connectedComponentIn hf hx]
  haveI : Finite ↥T := hT.to_subtype
  letI : CompactSpace Sphere2 :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  let F : T → Set (Sphere2 × Icc a b) :=
    fun s => (univ : Set Sphere2) ×ˢ ({s.1} : Set (Icc a b))
  have hUnion : (⋃ s, F s) = (univ : Set Sphere2) ×ˢ T := by
    simp_rw [F, ← prod_iUnion, iUnion_singleton_eq_range, Subtype.range_val]
  have hclosed : ∀ s, IsClosed (F s) := fun s =>
    (isCompact_univ.prod isCompact_singleton).isClosed
  have hconn : ∀ s, IsPreconnected (F s) := fun s =>
    isPreconnected_univ.prod isPreconnected_singleton
  have hdis : Pairwise (fun s u => Disjoint (F s) (F u)) := by
    intro s u hsu
    exact disjoint_left.mpr fun p hps hpu =>
      hsu (Subtype.ext (hps.2.symm.trans hpu.2))
  have hxF : (x, t) ∈ F ⟨t, ht⟩ := ⟨mem_univ _, rfl⟩
  rw [← hUnion, componentIn_finite_disjoint_closed F hclosed hconn hdis ⟨t, ht⟩ hxF]
/- SWARM_PROOF_END -/

end PoincareConjecture.Topology.FiberSaturation
