import PoincareConjecture.ProofContract.Refinement20260927.CapManifold
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedCapInteriorOpen
open PoincareConjecture.ProofContract.Refinement20260927
theorem cap_interior_open : CapInteriorOpenStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  intro c
  let Q := PoincareConjecture.ParallelImplementation.CappedSpaceTopology.CappedSpace
    c.boundaryMap
  let X := c.carrier ⊕ PoincareConjecture.ParallelImplementation.CappedSpaceTopology.Ball
  let q : X → Q := Quot.mk
    (PoincareConjecture.ParallelImplementation.CappedSpaceTopology.capSeam c.boundaryMap)
  let props := PoincareConjecture.ParallelImplementation.CappedSpaceTopology.actual_cap_quotient_topology
    c.boundaryMap c.boundaryEmbedding
  have hCclosed : Topology.IsClosedEmbedding (fun x : c.carrier =>
      q (Sum.inl x)) := props.2.2.1
  letI : CompactSpace PoincareConjecture.ProofContract.V1.Sphere2 :=
    isCompact_iff_compactSpace.mp (isCompact_sphere
      (0 : PoincareConjecture.ProofContract.V1.Euclidean3) 1)
  have hboundaryClosed : IsClosed (Set.range c.boundaryMap) :=
    (isCompact_range c.boundaryEmbedding.continuous).isClosed
  have hinteriorOpen : IsOpen ((Set.range c.boundaryMap)ᶜ) :=
    hboundaryClosed.isOpen_compl
  let U : Set X := Sum.inl '' ((Set.range c.boundaryMap)ᶜ)
  have hUopen : IsOpen U := isOpenMap_inl _ hinteriorOpen
  have hsat : ∀ x y, Relation.EqvGen
      (PoincareConjecture.ParallelImplementation.CappedSpaceTopology.capSeam
        c.boundaryMap) x y →
      (x ∈ U ↔ y ∈ U) := by
    intro x y hxy
    induction hxy with
    | rel x y hxy =>
        rcases hxy with ⟨s, rfl, rfl⟩
        have hleft : Sum.inl (c.boundaryMap s) ∉ U := by
          rintro ⟨z, hz, heq⟩
          have hzb : z = c.boundaryMap s := Sum.inl.inj heq
          subst z
          exact hz (Set.mem_range_self s)
        have hright : Sum.inr
            (PoincareConjecture.ParallelImplementation.CappedSpaceTopology.boundary s) ∉ U := by
          rintro ⟨z, hz, heq⟩
          cases heq
        constructor
        · exact fun hx => (hleft hx).elim
        · exact fun hy => (hright hy).elim
    | refl x => rfl
    | symm x y hxy ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  have hUpre : q ⁻¹' (q '' U) = U := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (hsat x y (Quot.eqvGen_exact hxy.symm)).mpr hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hqmap : Topology.IsQuotientMap q := isQuotientMap_quot_mk
  have hqUopen : IsOpen (q '' U) := by
    apply hqmap.isOpen_preimage.mp
    rw [hUpre]
    exact hUopen
  have hinteriorEmbedding : Topology.IsOpenEmbedding
      (Subtype.val : PieceInterior c → c.carrier) :=
    hinteriorOpen.isOpenEmbedding_subtypeVal
  have hEmbedding : Topology.IsEmbedding (pieceInteriorInclusion c) := by
    change Topology.IsEmbedding
      ((fun x : c.carrier => q (Sum.inl x)) ∘ (Subtype.val : PieceInterior c → c.carrier))
    exact hCclosed.isEmbedding.comp hinteriorEmbedding.isEmbedding
  have hrange : Set.range (pieceInteriorInclusion c) = q '' U := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Sum.inl x.val, ⟨x.val, x.property, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨x, hx, rfl⟩, hzy⟩
      exact ⟨⟨x, hx⟩, hzy⟩
  refine ⟨hEmbedding, ?_⟩
  rw [hrange]
  exact hqUopen
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedCapInteriorOpen
