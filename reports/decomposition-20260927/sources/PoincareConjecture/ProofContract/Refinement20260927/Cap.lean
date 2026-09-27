import PoincareConjecture.ParallelImplementation.CappedSpaceTopology
import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open Set V1
open PoincareConjecture.ParallelImplementation.CappedSpaceTopology
open scoped Topology
/-- A compact piece with its actual one-sided boundary collar. No cap chart is assumed. -/
structure CollaredPiece where
  carrier : Type u
  topology : TopologicalSpace carrier
  compact : @CompactSpace carrier topology
  hausdorff : @T2Space carrier topology
  boundaryMap : Sphere2 → carrier
  boundaryEmbedding : @Topology.IsEmbedding Sphere2 carrier _ topology boundaryMap
  collar : Sphere2 × Ico (0 : ℝ) 1 → carrier
  collarEmbedding : @Topology.IsOpenEmbedding _ carrier _ topology collar
  collarZero : ∀ s, collar (s, ⟨0, by norm_num⟩) = boundaryMap s
instance (c : CollaredPiece) : TopologicalSpace c.carrier := c.topology
instance (c : CollaredPiece) : CompactSpace c.carrier := c.compact
instance (c : CollaredPiece) : T2Space c.carrier := c.hausdorff
abbrev capInterior (c : CollaredPiece) : Metric.ball (0 : Euclidean3) 1 →
    CappedSpace c.boundaryMap := fun x => Quot.mk (capSeam c.boundaryMap)
      (Sum.inr (interiorPoint x))
/-- Explicit coordinate construction; fixes the entire closed unit ball. -/
def CapChartStatement : Prop := ∀ c : CollaredPiece.{u},
  ∃ e : OpenPartialHomeomorph Euclidean3 (CappedSpace c.boundaryMap),
    Metric.closedBall 0 2 ⊆ e.source ∧
    ∀ (x : Euclidean3) (hx : x ∈ Metric.closedBall 0 1),
      e x = Quot.mk (capSeam c.boundaryMap) (Sum.inr (⟨x, hx⟩ : Ball))
/-- Independent of a chart: deleting the actual cap interior recovers the piece. -/
def CapComplementStatement : Prop := ∀ c : CollaredPiece.{u},
  ∃ H : c.carrier ≃ₜ {q : CappedSpace c.boundaryMap // q ∉ Set.range (capInterior c)},
    ∀ x, (H x).val = Quot.mk (capSeam c.boundaryMap) (Sum.inl x)
/-- Raw seam of two original pieces, before any coordinate ball is selected. -/
def rawSeam {C D : Type u} (bC : Sphere2 → C) (bD : Sphere2 → D)
    (g : Sphere2 ≃ₜ Sphere2) (x y : C ⊕ D) : Prop :=
  ∃ s, x = Sum.inl (bC s) ∧ y = Sum.inr (bD (g s))
/-- Universal marked-quotient transport, not an assumed connected-sum presentation. -/
def MarkedGluingStatement : Prop :=
  ∀ (A B M : ClosedThreeManifold.{u}) (C D : Type u)
    [TopologicalSpace C] [TopologicalSpace D]
    (bC : Sphere2 → C) (bD : Sphere2 → D) (g : Sphere2 ≃ₜ Sphere2)
    (a : CoordinateBall A) (b : CoordinateBall B)
    (L : C ≃ₜ a.Complement) (R : D ≃ₜ b.Complement),
    (∀ s, L (bC s) = a.boundary s) →
    (∀ s, R (bD s) = b.boundary s) →
    Nonempty (M ≃ₜ Quot (rawSeam bC bD g)) →
    Nonempty (ConnectedSumPresentation A B M)
/-- Genuine cap identification supplied by the geometric construction. -/
structure CappedPiece (A : ClosedThreeManifold.{u}) where
  piece : CollaredPiece.{u}
  identification : CappedSpace piece.boundaryMap ≃ₜ A
structure RawCutPresentation (A B M : ClosedThreeManifold.{u}) where
  left : CappedPiece A
  right : CappedPiece B
  gluing : Sphere2 ≃ₜ Sphere2
  realization : M ≃ₜ Quot (rawSeam left.piece.boundaryMap right.piece.boundaryMap gluing)
/-- The two independent cap leaves really produce a boundary-marked complement. -/
theorem cappedPiece_marked_complement
    (charts : CapChartStatement.{u}) (complements : CapComplementStatement.{u})
    {A : ClosedThreeManifold.{u}} (p : CappedPiece A) :
    ∃ a : CoordinateBall A, ∃ L : p.piece.carrier ≃ₜ a.Complement,
      ∀ s : Sphere2, L (p.piece.boundaryMap s) = a.boundary s := by
  let c := p.piece
  let E := p.identification
  obtain ⟨e, he2, he⟩ := charts c
  obtain ⟨H, hH⟩ := complements c
  let a : CoordinateBall A := ⟨e.transHomeomorph E, by
    simpa [OpenPartialHomeomorph.transHomeomorph_eq_trans] using he2⟩
  have hremoved : a.removed = E '' Set.range (capInterior c) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨capInterior c ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, ?_⟩
      change E (capInterior c ⟨x, hx⟩) = E (e x)
      rw [he x (Metric.ball_subset_closedBall hx)]
      rfl
    · rintro ⟨q, ⟨x, rfl⟩, rfl⟩
      refine ⟨x.val, x.property, ?_⟩
      change E (e x.val) = E (capInterior c x)
      rw [he x.val (Metric.ball_subset_closedBall x.property)]
      rfl
  have hiff (q : CappedSpace c.boundaryMap) :
      q ∉ Set.range (capInterior c) ↔ E q ∉ a.removed := by
    rw [hremoved, E.injective.mem_set_image]
  let J : {q : CappedSpace c.boundaryMap // q ∉ Set.range (capInterior c)} ≃ₜ
      a.Complement := E.subtype hiff
  let L : c.carrier ≃ₜ a.Complement := H.trans J
  refine ⟨a, L, ?_⟩
  intro s
  apply Subtype.ext
  change E (H (c.boundaryMap s)).val = E (e s.val)
  rw [hH, he s.val (Metric.sphere_subset_closedBall s.property)]
  apply congrArg E
  exact Quot.sound ⟨s, rfl, rfl⟩
/-- Checked reduction: three specific leaves give an actual V1 connected sum. -/
theorem rawCut_connectedSum
    (charts : CapChartStatement.{u}) (complements : CapComplementStatement.{u})
    (glue : MarkedGluingStatement.{u}) {A B M : ClosedThreeManifold.{u}}
    (p : RawCutPresentation A B M) : Nonempty (ConnectedSumPresentation A B M) := by
  obtain ⟨a, L, hL⟩ := cappedPiece_marked_complement charts complements p.left
  obtain ⟨b, R, hR⟩ := cappedPiece_marked_complement charts complements p.right
  exact glue A B M p.left.piece.carrier p.right.piece.carrier
    p.left.piece.boundaryMap p.right.piece.boundaryMap p.gluing a b L R hL hR
    ⟨p.realization⟩
#print axioms cappedPiece_marked_complement
#print axioms rawCut_connectedSum
end PoincareConjecture.ProofContract.Refinement20260927
