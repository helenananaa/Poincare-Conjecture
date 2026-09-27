import PoincareConjecture.ProofContract.Refinement20260927.AcceptedFive
import PoincareConjecture.ProofContract.Refinement20260927.Neck
import PoincareConjecture.CriticalPath.SurgeryBudget.MeasuredHistory
set_option autoImplicit false
noncomputable section
universe u v
namespace PoincareConjecture.ProofContract.Refinement20260927
open Set V1
/-- Homeomorphism changes representatives, not the claimed geometric construction. -/
theorem standardDecomposition_homeomorph {M N : ClosedThreeManifold.{u}}
    (e : M ≃ₜ N) (d : StandardDecomposition M) : StandardDecomposition N := by
  cases d with
  | sphereCovered h =>
    obtain ⟨p,hp,hs⟩ := h
    exact .sphereCovered ⟨e ∘ p, hp.homeomorph_comp e, e.surjective.comp hs⟩
  | handle h =>
    obtain ⟨h⟩ := h
    exact .handle ⟨e.symm.trans h⟩
  | connectedSum h da db =>
    obtain ⟨p⟩ := h
    exact .connectedSum ⟨{ p with realization := e.symm.trans p.realization }⟩ da db
/-- Independent finite-order lemma. Finite event times are supplied separately;
local jumps and event-free intervals are for the SAME pre/post functions. -/
def FiniteTimelineStatement : Prop :=
  ∀ (X : Type v) (R : X → X → Prop) (pre post : ℝ → X) (a b : ℝ), a < b →
    ∀ E : Set ℝ, E.Finite → E ⊆ Ioo a b →
    (∀ t ∈ E, Relation.ReflTransGen R (pre t) (post t)) →
    (∀ s t, a ≤ s → s < t → t ≤ b → (E ∩ Ioo s t = ∅) →
      Relation.ReflTransGen R (post s) (pre t)) →
    Relation.ReflTransGen R (post a) (pre b)
/-- Ordinary stages change representatives/order only; no hidden surgery constructor. -/
inductive RepresentativeStep : List ClosedThreeManifold.{u} → List ClosedThreeManifold.{u} → Prop
  | change (before after : List ClosedThreeManifold.{u}) (M N : ClosedThreeManifold.{u})
      (e : Nonempty (M ≃ₜ N)) :
      RepresentativeStep (before ++ M :: after) (before ++ N :: after)
  | reorder {xs ys} : xs.Perm ys → RepresentativeStep xs ys
abbrev neckLeft (atlas : SideInteriorAtlasStatement.{u})
    (negative : NegativeHalfCollarStatement.{u}) {M : ClosedThreeManifold.{u}}
    (hsc : SimplyConnectedSpace M) (f : Sphere2 × Icc (-1 : ℝ) 1 → M)
    (hf : Topology.IsEmbedding f) (p : Sphere2) :=
  cappedManifold checked_cap_chart checked_interior_open
    (closedCut_of_neck atlas negative hsc f hf p).left.regularPiece
abbrev neckRight (atlas : SideInteriorAtlasStatement.{u})
    (negative : NegativeHalfCollarStatement.{u}) {M : ClosedThreeManifold.{u}}
    (hsc : SimplyConnectedSpace M) (f : Sphere2 × Icc (-1 : ℝ) 1 → M)
    (hf : Topology.IsEmbedding f) (p : Sphere2) :=
  cappedManifold checked_cap_chart checked_interior_open
    (closedCut_of_neck atlas negative hsc f hf p).right.regularPiece
/-- Concrete projected operations. Actual post-surgery representatives are allowed,
but genuine cap homeomorphisms must be supplied. No PDE existence is asserted. -/
inductive ProjectedSurgeryStep (atlas : SideInteriorAtlasStatement.{u})
    (negative : NegativeHalfCollarStatement.{u}) :
    List ClosedThreeManifold.{u} → List ClosedThreeManifold.{u} → Prop
  | regular {xs ys} : RepresentativeStep xs ys → ProjectedSurgeryStep atlas negative xs ys
  | discardCovered (before after : List ClosedThreeManifold.{u}) (M) : HasSphereCover M →
      ProjectedSurgeryStep atlas negative (before ++ M :: after) (before ++ after)
  | discardHandle (before after : List ClosedThreeManifold.{u}) (M) : IsSphereHandle M →
      ProjectedSurgeryStep atlas negative (before ++ M :: after) (before ++ after)
  | neck (before after : List ClosedThreeManifold.{u}) {M : ClosedThreeManifold.{u}}
      (hsc : SimplyConnectedSpace M) (f : Sphere2 × Icc (-1 : ℝ) 1 → M)
      (hf : Topology.IsEmbedding f) (p : Sphere2) (A B : ClosedThreeManifold.{u})
      (left : Nonempty (neckLeft atlas negative hsc f hf p ≃ₜ A))
      (right : Nonempty (neckRight atlas negative hsc f hf p ≃ₜ B)) :
      ProjectedSurgeryStep atlas negative (before ++ M :: after) (before ++ A :: B :: after)
def EveryStandard (xs : List ClosedThreeManifold.{u}) : Prop :=
  ∀ M ∈ xs, StandardDecomposition M
private theorem every_append (xs ys : List ClosedThreeManifold.{u}) :
    EveryStandard (xs ++ ys) ↔ EveryStandard xs ∧ EveryStandard ys := by
  constructor
  · intro h
    exact ⟨fun M hm => h M (List.mem_append.mpr (Or.inl hm)),
      fun M hm => h M (List.mem_append.mpr (Or.inr hm))⟩
  · rintro ⟨hx,hy⟩ M hm
    rcases List.mem_append.mp hm with h | h
    · exact hx M h
    · exact hy M h
private theorem every_cons (M : ClosedThreeManifold.{u}) (xs : List ClosedThreeManifold.{u}) :
    EveryStandard (M :: xs) ↔ StandardDecomposition M ∧ EveryStandard xs := by
  simp [EveryStandard]
theorem representative_reconstruct {xs ys : List ClosedThreeManifold.{u}}
    (s : RepresentativeStep xs ys) (h : EveryStandard ys) : EveryStandard xs := by
  cases s with
  | change before after M N e =>
    rw [every_append, every_cons] at h ⊢
    obtain ⟨e⟩ := e
    exact ⟨h.1, standardDecomposition_homeomorph e.symm h.2.1, h.2.2⟩
  | reorder p =>
    intro M hM
    exact h M (p.mem_iff.mp hM)
theorem projected_step_reconstruct (atlas : SideInteriorAtlasStatement.{u})
    (negative : NegativeHalfCollarStatement.{u}) {xs ys : List ClosedThreeManifold.{u}}
    (s : ProjectedSurgeryStep atlas negative xs ys) (h : EveryStandard ys) : EveryStandard xs := by
  cases s with
  | regular s => exact representative_reconstruct s h
  | discardCovered before after M hM =>
    rw [every_append] at h
    rw [every_append, every_cons]
    exact ⟨h.1, .sphereCovered hM, h.2⟩
  | discardHandle before after M hM =>
    rw [every_append] at h
    rw [every_append, every_cons]
    exact ⟨h.1, .handle hM, h.2⟩
  | neck before after hsc f hf p A B left right =>
    rw [every_append, every_cons, every_cons] at h
    rw [every_append, every_cons]
    obtain ⟨eA⟩ := left
    obtain ⟨eB⟩ := right
    have cut := checked_closedCut_connectedSum (closedCut_of_neck atlas negative hsc f hf p)
    exact ⟨h.1, .connectedSum cut
      (standardDecomposition_homeomorph eA.symm h.2.1)
      (standardDecomposition_homeomorph eB.symm h.2.2.1), h.2.2.2⟩
theorem projected_block_reconstruct (atlas : SideInteriorAtlasStatement.{u})
    (negative : NegativeHalfCollarStatement.{u}) {xs ys : List ClosedThreeManifold.{u}}
    (s : Relation.ReflTransGen (ProjectedSurgeryStep atlas negative) xs ys) :
    EveryStandard ys → EveryStandard xs := by
  induction s with
  | refl => exact id
  | tail _ step ih => exact fun h => ih (projected_step_reconstruct atlas negative step h)
/-- Potentially infinitely many real event times. This is a TOPOLOGICAL
projection obligation, never a definition of Ricci flow or a finite trace. -/
structure SurgeryProjection (atlas : SideInteriorAtlasStatement.{u})
    (negative : NegativeHalfCollarStatement.{u}) (M : ClosedThreeManifold.{u}) where
  horizon : ℝ
  horizon_pos : 0 < horizon
  events : Set ℝ
  event_times : events ⊆ Ioo 0 horizon
  pre : ℝ → List ClosedThreeManifold.{u}
  post : ℝ → List ClosedThreeManifold.{u}
  initial : post 0 = [M]
  jumps : ∀ t ∈ events, Relation.ReflTransGen (ProjectedSurgeryStep atlas negative) (pre t) (post t)
  ordinary : ∀ s t, 0 ≤ s → s < t → t ≤ horizon → (events ∩ Ioo s t = ∅) →
    Relation.ReflTransGen RepresentativeStep (post s) (pre t)
/-- Uniform measured coverage of ALL finite samples of this SAME event set.
No assumption that all events have already been enumerated. -/
def ProjectionBudget {atlas : SideInteriorAtlasStatement.{u}}
    {negative : NegativeHalfCollarStatement.{u}} {M : ClosedThreeManifold.{u}}
    (H : SurgeryProjection atlas negative M) : Prop :=
  ∃ a delta initialVolume : ℝ, ∃ initialComponents : ℕ, 0 ≤ a ∧ 0 < delta ∧
    ∀ s : Finset ℝ, (↑s : Set ℝ) ⊆ H.events →
      ∃ n : ℕ, s.card ≤ n ∧ Nonempty
        (CriticalPath.SurgeryBudget.MeasuredSurgeryHistory.{u}
          n a H.horizon delta initialVolume initialComponents)
theorem projection_events_finite {atlas : SideInteriorAtlasStatement.{u}}
    {negative : NegativeHalfCollarStatement.{u}} {M : ClosedThreeManifold.{u}}
    (H : SurgeryProjection atlas negative M) (budget : ProjectionBudget H) : H.events.Finite := by
  obtain ⟨a,delta,volume,components,ha,hd,hcover⟩ := budget
  exact (CriticalPath.SurgeryBudget.finite_event_set_of_measured_histories H.events ha hd hcover).1
theorem regular_block_to_projected (atlas : SideInteriorAtlasStatement.{u})
    (negative : NegativeHalfCollarStatement.{u}) {xs ys : List ClosedThreeManifold.{u}}
    (h : Relation.ReflTransGen RepresentativeStep xs ys) :
    Relation.ReflTransGen (ProjectedSurgeryStep atlas negative) xs ys := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact .tail ih (.regular hstep)
/-- Finite time alone is NOT used to infer finitely many events. -/
theorem projection_trace (timeline : FiniteTimelineStatement.{u+1})
    (atlas : SideInteriorAtlasStatement.{u}) (negative : NegativeHalfCollarStatement.{u})
    {M : ClosedThreeManifold.{u}} (H : SurgeryProjection atlas negative M)
    (empty_end : H.pre H.horizon = []) (budget : ProjectionBudget H) : FiniteExtinctionTrace [M] := by
  have chain := timeline (List ClosedThreeManifold.{u}) (ProjectedSurgeryStep atlas negative)
    H.pre H.post 0 H.horizon H.horizon_pos H.events (projection_events_finite H budget)
    H.event_times H.jumps (fun s t hs hst ht he =>
      regular_block_to_projected atlas negative (H.ordinary s t hs hst ht he))
  have last : EveryStandard (H.pre H.horizon) := by rw [empty_end]; simp [EveryStandard]
  have first := projected_block_reconstruct atlas negative chain last
  rw [H.initial] at first
  exact standard_eliminates_context (first M (by simp)) [] [] .empty
/-- Still RESEARCH. Must construct actual projected geometry and prove empty end
and uniform measured sample coverage together for the SAME projection.
Neither a finite trace nor event finiteness is a field. PDE/flow is not claimed built. -/
def SurgeryProjectionProducerStatement : Prop :=
  ∀ (atlas : SideInteriorAtlasStatement.{u}) (negative : NegativeHalfCollarStatement.{u})
    (M : ClosedThreeManifold.{u}), IsSmooth M → SimplyConnectedSpace M →
    ∃ H : SurgeryProjection atlas negative M, H.pre H.horizon = [] ∧ ProjectionBudget H
theorem geometric_of_projection_producer (timeline : FiniteTimelineStatement.{u+1})
    (atlas : SideInteriorAtlasStatement.{u}) (negative : NegativeHalfCollarStatement.{u})
    (producer : SurgeryProjectionProducerStatement.{u}) : GeometricTraceStatement.{u} := by
  intro M hsm hsc
  obtain ⟨H,hempty,budget⟩ := producer atlas negative M hsm hsc
  exact projection_trace timeline atlas negative H hempty budget
/-- Versioned alternative adapter to the ORIGINAL V1 root. Six open inputs;
this is not an assertion that the geometric producer has been constructed. -/
theorem public_of_projection_frontier (triangulate : TriangulationProducerStatement.{u})
    (smoothPL : PLAtlasProducerStatement.{u}) (atlas : SideInteriorAtlasStatement.{u})
    (negative : NegativeHalfCollarStatement.{u}) (timeline : FiniteTimelineStatement.{u+1})
    (producer : SurgeryProjectionProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  Proofs.topological_of_two_contracts (smoothing_of_finitePL_producers triangulate smoothPL)
    (geometric_of_projection_producer timeline atlas negative producer)
#print axioms standardDecomposition_homeomorph
#print axioms representative_reconstruct
#print axioms projected_step_reconstruct
#print axioms projected_block_reconstruct
#print axioms projection_events_finite
#print axioms regular_block_to_projected
#print axioms projection_trace
#print axioms geometric_of_projection_producer
#print axioms public_of_projection_frontier
end PoincareConjecture.ProofContract.Refinement20260927
