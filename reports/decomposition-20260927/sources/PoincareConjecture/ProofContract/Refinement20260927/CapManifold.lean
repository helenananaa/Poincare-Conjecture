import PoincareConjecture.ProofContract.Refinement20260927.Cap
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open Set V1
open PoincareConjecture.ParallelImplementation.CappedSpaceTopology
open scoped Topology
abbrev PieceInterior (c : CollaredPiece.{u}) :=
  {x : c.carrier // x ∉ Set.range c.boundaryMap}
abbrev pieceInteriorInclusion (c : CollaredPiece.{u}) :
    PieceInterior c → CappedSpace c.boundaryMap :=
  fun x => Quot.mk (capSeam c.boundaryMap) (Sum.inl x.val)
/-- Only original-piece regularity; no capped atlas or sphere recognition is a field. -/
structure RegularCollaredPiece extends CollaredPiece.{u} where
  connected : @ConnectedSpace carrier topology
  interiorCharts : ChartedSpace Euclidean3 (PieceInterior toCollaredPiece)
/-- The actual original interior is open in the actual cap quotient. -/
def CapInteriorOpenStatement : Prop := ∀ c : CollaredPiece.{u},
  Topology.IsOpenEmbedding (pieceInteriorInclusion c)
/-- Connectedness is a genuine consequence of gluing a ball along its nonempty sphere. -/
theorem actual_cap_connected (c : CollaredPiece.{u})
    [ConnectedSpace c.carrier] : ConnectedSpace (CappedSpace c.boundaryMap) := by
  letI : ConnectedSpace Ball := isConnected_iff_connectedSpace.mp
    ((convex_closedBall (0 : Euclidean3) 1).isConnected
      (Metric.nonempty_closedBall.mpr (by norm_num)))
  let left : c.carrier → CappedSpace c.boundaryMap :=
    fun x => Quot.mk (capSeam c.boundaryMap) (Sum.inl x)
  let right : Ball → CappedSpace c.boundaryMap :=
    fun x => Quot.mk (capSeam c.boundaryMap) (Sum.inr x)
  have hleft : Continuous left := continuous_quot_mk.comp continuous_inl
  have hright : Continuous right := continuous_quot_mk.comp continuous_inr
  let s : Sphere2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hmeet : (Set.range left ∩ Set.range right).Nonempty := by
    refine ⟨left (c.boundaryMap s), ⟨c.boundaryMap s, rfl⟩, boundary s, ?_⟩
    exact (Quot.sound ⟨s, rfl, rfl⟩).symm
  have hcover : Set.range left ∪ Set.range right = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    induction q using Quot.induction_on with
    | h x =>
      cases x with
      | inl x => exact Or.inl ⟨x, rfl⟩
      | inr y => exact Or.inr ⟨y, rfl⟩
  have hconnected : IsConnected (Set.range left ∪ Set.range right) :=
    (isConnected_range hleft).union hmeet (isConnected_range hright)
  rw [hcover] at hconnected
  exact connectedSpace_iff_univ.mpr hconnected
/-- The cap chart covers the whole glued ball; original interior charts cover the rest. -/
theorem actual_cap_atlas (charts : CapChartStatement.{u})
    (openInterior : CapInteriorOpenStatement.{u}) (c : RegularCollaredPiece.{u}) :
    Nonempty (ChartedSpace Euclidean3 (CappedSpace c.boundaryMap)) := by
  letI : ChartedSpace Euclidean3 (PieceInterior c.toCollaredPiece) := c.interiorCharts
  obtain ⟨e, he2, he⟩ := charts c.toCollaredPiece
  let incl := pieceInteriorInclusion c.toCollaredPiece
  have hi : IsLocalHomeomorph incl := (openInterior c.toCollaredPiece).isLocalHomeomorph
  have hex : ∀ q : CappedSpace c.boundaryMap,
      ∃ a : OpenPartialHomeomorph (CappedSpace c.boundaryMap) Euclidean3, q ∈ a.source := by
    intro q
    induction q using Quot.induction_on with
    | h z =>
      cases z with
      | inl x =>
        by_cases hx : x ∈ Set.range c.boundaryMap
        · obtain ⟨s, rfl⟩ := hx
          have hs1 : s.val ∈ Metric.closedBall (0 : Euclidean3) 1 :=
            Metric.sphere_subset_closedBall s.property
          have hs2 : s.val ∈ e.source := he2 (Metric.closedBall_subset_closedBall (by norm_num) hs1)
          have hs := e.map_source hs2
          refine ⟨e.symm, ?_⟩
          change Quot.mk (capSeam c.boundaryMap) (Sum.inl (c.boundaryMap s)) ∈ e.target
          rw [Quot.sound (r := capSeam c.boundaryMap) ⟨s, rfl, rfl⟩]
          simpa [he s.val hs1, boundary] using hs
        · let y : PieceInterior c.toCollaredPiece := ⟨x, hx⟩
          let a := (hi.localInverseAt y).trans (chartAt Euclidean3 y)
          refine ⟨a, ?_⟩
          change incl y ∈ (hi.localInverseAt y).source ∧
            hi.localInverseAt y (incl y) ∈ (chartAt Euclidean3 y).source
          exact ⟨hi.apply_self_mem_localInverseAt_source, by
            rw [hi.localInverseAt_apply_self]
            exact mem_chart_source Euclidean3 y⟩
      | inr x =>
        have hx2 : x.val ∈ e.source :=
          he2 (Metric.closedBall_subset_closedBall (by norm_num) x.property)
        refine ⟨e.symm, ?_⟩
        simpa [he x.val x.property] using e.map_source hx2
  let a (q : CappedSpace c.boundaryMap) := Classical.choose (hex q)
  exact ⟨{
    atlas := Set.range a
    chartAt := a
    mem_chart_source := fun q => Classical.choose_spec (hex q)
    chart_mem_atlas := fun q => ⟨q, rfl⟩ }⟩
/-- Construct the full manifold on exactly the cap quotient topology. -/
def cappedManifold (charts : CapChartStatement.{u})
    (openInterior : CapInteriorOpenStatement.{u}) (c : RegularCollaredPiece.{u}) :
    ClosedThreeManifold.{u} := by
  letI : ConnectedSpace c.carrier := c.connected
  let props := actual_cap_quotient_topology c.boundaryMap c.boundaryEmbedding
  letI : CompactSpace (CappedSpace c.boundaryMap) := props.1
  letI : T2Space (CappedSpace c.boundaryMap) := props.2.1
  letI : ConnectedSpace (CappedSpace c.boundaryMap) := actual_cap_connected c.toCollaredPiece
  letI : ChartedSpace Euclidean3 (CappedSpace c.boundaryMap) :=
    Classical.choice (actual_cap_atlas charts openInterior c)
  exact {
    toTopCat := TopCat.of (CappedSpace c.boundaryMap)
    hausdorff := inferInstance
    secondCountable := ChartedSpace.secondCountable_of_sigmaCompact Euclidean3 _
    compact := inferInstance
    connected := inferInstance
    inhabitedSpace := inferInstance
    charts := inferInstance }
def cappedIdentification (charts : CapChartStatement.{u})
    (openInterior : CapInteriorOpenStatement.{u}) (c : RegularCollaredPiece.{u}) :
    CappedSpace c.boundaryMap ≃ₜ cappedManifold charts openInterior c := Homeomorph.refl _
#print axioms actual_cap_connected
#print axioms actual_cap_atlas
#print axioms cappedManifold
#print axioms cappedIdentification
end PoincareConjecture.ProofContract.Refinement20260927
