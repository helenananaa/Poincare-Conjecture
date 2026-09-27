import PoincareConjecture.ProofContract.Refinement20260927.SurgeryProjection
import PoincareConjecture.ProofContract.Proofs.AlexanderExtension
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open Set V1
open PoincareConjecture.ParallelImplementation.CappedSpaceTopology
/-- Independent leaf: cap quotient transport under an actual piece equivalence
and arbitrary boundary reparameterization. The ORIGINAL inclusion is preserved. -/
def CapRelabelingStatement : Prop :=
  ∀ (c d : CollaredPiece.{u}) (L : c.carrier ≃ₜ d.carrier) (g : Sphere2 ≃ₜ Sphere2),
    (∀ s, L (c.boundaryMap s) = d.boundaryMap (g s)) →
    ∃ H : CappedSpace c.boundaryMap ≃ₜ CappedSpace d.boundaryMap,
      ∀ x : c.carrier, H (Quot.mk (capSeam c.boundaryMap) (Sum.inl x)) =
        Quot.mk (capSeam d.boundaryMap) (Sum.inl (L x))
/-- A geometrically produced capped component can use a different piece model
and boundary marking. It does NOT assume identification with our canonical cap. -/
structure RelabeledCap (c : CollaredPiece.{u}) (A : ClosedThreeManifold.{u}) where
  piece : CollaredPiece.{u}
  pieceEquiv : c.carrier ≃ₜ piece.carrier
  marking : Sphere2 ≃ₜ Sphere2
  boundaryCompatible : ∀ s, pieceEquiv (c.boundaryMap s) = piece.boundaryMap (marking s)
  actualRealization : CappedSpace piece.boundaryMap ≃ₜ A
theorem relabeled_cap_identifies (relabel : CapRelabelingStatement.{u})
    (c : RegularCollaredPiece.{u}) {A : ClosedThreeManifold.{u}}
    (r : RelabeledCap c.toCollaredPiece A) :
    Nonempty (cappedManifold checked_cap_chart checked_interior_open c ≃ₜ A) := by
  obtain ⟨H,_⟩ := relabel c.toCollaredPiece r.piece r.pieceEquiv r.marking r.boundaryCompatible
  exact ⟨(cappedIdentification checked_cap_chart checked_interior_open c).symm.trans
    (H.trans r.actualRealization)⟩
inductive RelabeledSurgeryStep (atlas : SideInteriorAtlasStatement.{u})
    (negative : NegativeHalfCollarStatement.{u}) :
    List ClosedThreeManifold.{u} → List ClosedThreeManifold.{u} → Prop
  | regular {xs ys} : RepresentativeStep xs ys → RelabeledSurgeryStep atlas negative xs ys
  | discardCovered (before after : List ClosedThreeManifold.{u}) (M) : HasSphereCover M →
      RelabeledSurgeryStep atlas negative (before ++ M :: after) (before ++ after)
  | discardHandle (before after : List ClosedThreeManifold.{u}) (M) : IsSphereHandle M →
      RelabeledSurgeryStep atlas negative (before ++ M :: after) (before ++ after)
  | neck (before after : List ClosedThreeManifold.{u}) {M : ClosedThreeManifold.{u}}
      (hsc : SimplyConnectedSpace M) (f : Sphere2 × Icc (-1 : ℝ) 1 → M)
      (hf : Topology.IsEmbedding f) (p : Sphere2) (A B : ClosedThreeManifold.{u})
      (left : Nonempty (RelabeledCap
        (closedCut_of_neck atlas negative hsc f hf p).left.regularPiece.toCollaredPiece A))
      (right : Nonempty (RelabeledCap
        (closedCut_of_neck atlas negative hsc f hf p).right.regularPiece.toCollaredPiece B)) :
      RelabeledSurgeryStep atlas negative (before ++ M :: after) (before ++ A :: B :: after)
theorem relabeled_step_to_projected (relabel : CapRelabelingStatement.{u})
    (atlas : SideInteriorAtlasStatement.{u}) (negative : NegativeHalfCollarStatement.{u})
    {xs ys : List ClosedThreeManifold.{u}} (s : RelabeledSurgeryStep atlas negative xs ys) :
    ProjectedSurgeryStep atlas negative xs ys := by
  cases s with
  | regular h => exact .regular h
  | discardCovered b a M h => exact .discardCovered b a M h
  | discardHandle b a M h => exact .discardHandle b a M h
  | neck b a hsc f hf p A B l r =>
    obtain ⟨l⟩ := l
    obtain ⟨r⟩ := r
    exact .neck b a hsc f hf p A B (relabeled_cap_identifies relabel _ l)
      (relabeled_cap_identifies relabel _ r)
theorem relabeled_block_to_projected (relabel : CapRelabelingStatement.{u})
    (atlas : SideInteriorAtlasStatement.{u}) (negative : NegativeHalfCollarStatement.{u})
    {xs ys : List ClosedThreeManifold.{u}}
    (h : Relation.ReflTransGen (RelabeledSurgeryStep atlas negative) xs ys) :
    Relation.ReflTransGen (ProjectedSurgeryStep atlas negative) xs ys := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (relabeled_step_to_projected relabel atlas negative step)
/-- Same projection data, with the actual relabeled cap models at each jump. -/
structure RelabeledProjection (atlas : SideInteriorAtlasStatement.{u})
    (negative : NegativeHalfCollarStatement.{u}) (M : ClosedThreeManifold.{u}) where
  horizon : ℝ
  horizon_pos : 0 < horizon
  events : Set ℝ
  event_times : events ⊆ Ioo 0 horizon
  pre : ℝ → List ClosedThreeManifold.{u}
  post : ℝ → List ClosedThreeManifold.{u}
  initial : post 0 = [M]
  jumps : ∀ t ∈ events, Relation.ReflTransGen (RelabeledSurgeryStep atlas negative) (pre t) (post t)
  ordinary : ∀ s t, 0 ≤ s → s < t → t ≤ horizon → (events ∩ Ioo s t = ∅) →
    Relation.ReflTransGen RepresentativeStep (post s) (pre t)
def RelabeledProjection.toProjection (relabel : CapRelabelingStatement.{u})
    {atlas : SideInteriorAtlasStatement.{u}} {negative : NegativeHalfCollarStatement.{u}}
    {M : ClosedThreeManifold.{u}} (H : RelabeledProjection atlas negative M) :
    SurgeryProjection atlas negative M where
  horizon := H.horizon
  horizon_pos := H.horizon_pos
  events := H.events
  event_times := H.event_times
  pre := H.pre
  post := H.post
  initial := H.initial
  jumps := fun t ht => relabeled_block_to_projected relabel atlas negative (H.jumps t ht)
  ordinary := H.ordinary
/-- Budget uses the very same horizon/event set but is independent of cap choices. -/
def UniformEventBudget (T : ℝ) (events : Set ℝ) : Prop :=
  ∃ a delta initialVolume : ℝ, ∃ initialComponents : ℕ, 0 ≤ a ∧ 0 < delta ∧
    ∀ s : Finset ℝ, (↑s : Set ℝ) ⊆ events →
      ∃ n : ℕ, s.card ≤ n ∧ Nonempty
        (CriticalPath.SurgeryBudget.MeasuredSurgeryHistory.{u}
          n a T delta initialVolume initialComponents)
/-- Still a large RESEARCH obligation, not a claim of constructed Ricci flow. -/
def RelabeledProjectionProducerStatement : Prop :=
  ∀ (atlas : SideInteriorAtlasStatement.{u}) (negative : NegativeHalfCollarStatement.{u})
    (M : ClosedThreeManifold.{u}), IsSmooth M → SimplyConnectedSpace M →
    ∃ H : RelabeledProjection atlas negative M,
      H.pre H.horizon = [] ∧ UniformEventBudget.{u} H.horizon H.events
theorem projection_producer_of_relabeling (relabel : CapRelabelingStatement.{u})
    (producer : RelabeledProjectionProducerStatement.{u}) : SurgeryProjectionProducerStatement.{u} := by
  intro atlas negative M hsm hsc
  obtain ⟨H,hend,hbudget⟩ := producer atlas negative M hsm hsc
  exact ⟨H.toProjection relabel,hend,hbudget⟩
theorem public_of_relabeled_projection (triangulate : TriangulationProducerStatement.{u})
    (smoothPL : PLAtlasProducerStatement.{u}) (atlas : SideInteriorAtlasStatement.{u})
    (negative : NegativeHalfCollarStatement.{u}) (timeline : FiniteTimelineStatement.{u+1})
    (relabel : CapRelabelingStatement.{u}) (producer : RelabeledProjectionProducerStatement.{u}) :
    TopologicalPoincareStatement.{u} :=
  public_of_projection_frontier triangulate smoothPL atlas negative timeline
    (projection_producer_of_relabeling relabel producer)
#print axioms relabeled_cap_identifies
#print axioms relabeled_step_to_projected
#print axioms relabeled_block_to_projected
#print axioms RelabeledProjection.toProjection
#print axioms projection_producer_of_relabeling
#print axioms public_of_relabeled_projection
end PoincareConjecture.ProofContract.Refinement20260927
