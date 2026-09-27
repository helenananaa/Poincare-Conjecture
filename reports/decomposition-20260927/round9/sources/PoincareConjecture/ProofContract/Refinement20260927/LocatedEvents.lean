import PoincareConjecture.ProofContract.Refinement20260927.LocatedCut
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
/-- **Math.** Data of one actual cut. Its outputs refer to a cut certified to
have the subsets and markings of THIS metric neck, not an arbitrary chosen cut. -/
structure LocatedCutSite (embed : EpsilonNeckEmbeddingStatement.{u}) where
  source : ClosedThreeManifold.{u}
  simplyConnected : SimplyConnectedSpace source
  neck : AmbientMetricNeck source
  point : Sphere2
  leftResult : ClosedThreeManifold.{u}
  rightResult : ClosedThreeManifold.{u}
  leftCap : Nonempty (RelabeledCap
    (locatedNeckCut simplyConnected neck.closedCollar (embed source neck) point).cut.left.regularPiece.toCollaredPiece leftResult)
  rightCap : Nonempty (RelabeledCap
    (locatedNeckCut simplyConnected neck.closedCollar (embed source neck) point).cut.right.regularPiece.toCollaredPiece rightResult)
/-- **Math.** Site lists index the actual neck witnesses, not merely their count. -/
inductive LocatedMove (embed : EpsilonNeckEmbeddingStatement.{u}) :
    List ClosedThreeManifold.{u} → List ClosedThreeManifold.{u} → List (LocatedCutSite embed) → ℕ → Prop
  | regular {xs ys} : RepresentativeStep xs ys → LocatedMove embed xs ys [] 0
  | covered (before after : List ClosedThreeManifold.{u}) (M) : HasSphereCover M →
      LocatedMove embed (before ++ M :: after) (before ++ after) [] 1
  | handle (before after : List ClosedThreeManifold.{u}) (M) : IsSphereHandle M →
      LocatedMove embed (before ++ M :: after) (before ++ after) [] 1
  | cut (before after : List ClosedThreeManifold.{u}) (s : LocatedCutSite embed) :
      LocatedMove embed (before ++ s.source :: after)
        (before ++ s.leftResult :: s.rightResult :: after) [s] 0
inductive LocatedChain (embed : EpsilonNeckEmbeddingStatement.{u}) :
    List ClosedThreeManifold.{u} → List ClosedThreeManifold.{u} → List (LocatedCutSite embed) → ℕ → Prop
  | refl (xs) : LocatedChain embed xs xs [] 0
  | tail {xs zs ys cs ds d e} : LocatedChain embed xs zs cs d →
      LocatedMove embed zs ys ds e → LocatedChain embed xs ys (cs ++ ds) (d+e)
private theorem all_append (xs ys : List ClosedThreeManifold.{u}) :
    EveryStandard (xs ++ ys) ↔ EveryStandard xs ∧ EveryStandard ys := by
  constructor
  · intro h; exact ⟨fun M hm => h M (List.mem_append.mpr (Or.inl hm)),
      fun M hm => h M (List.mem_append.mpr (Or.inr hm))⟩
  · rintro ⟨hx,hy⟩ M hm
    exact (List.mem_append.mp hm).elim (hx M) (hy M)
private theorem all_cons (M : ClosedThreeManifold.{u}) (xs : List ClosedThreeManifold.{u}) :
    EveryStandard (M :: xs) ↔ StandardDecomposition M ∧ EveryStandard xs := by simp [EveryStandard]
theorem LocatedMove.balance {embed : EpsilonNeckEmbeddingStatement.{u}} {xs ys cs d}
    (m : LocatedMove embed xs ys cs d) : ys.length + d = xs.length + cs.length := by
  cases m with
  | regular h => simpa using representative_length h
  | covered => simp; omega
  | handle => simp; omega
  | cut => simp; omega
theorem LocatedChain.balance {embed : EpsilonNeckEmbeddingStatement.{u}} {xs ys cs d}
    (m : LocatedChain embed xs ys cs d) : ys.length + d = xs.length + cs.length := by
  induction m with
  | refl => simp
  | tail _ step ih => have hb := step.balance; simp only [List.length_append]; omega
theorem LocatedMove.reconstruct {embed : EpsilonNeckEmbeddingStatement.{u}} {xs ys cs d}
    (m : LocatedMove embed xs ys cs d) (h : EveryStandard ys) : EveryStandard xs := by
  cases m with
  | regular hstep => exact representative_reconstruct hstep h
  | covered before after M hM =>
    rw [all_append] at h
    rw [all_append,all_cons]
    exact ⟨h.1,.sphereCovered hM,h.2⟩
  | handle before after M hM =>
    rw [all_append] at h
    rw [all_append,all_cons]
    exact ⟨h.1,.handle hM,h.2⟩
  | cut before after site =>
    rw [all_append,all_cons,all_cons] at h
    rw [all_append,all_cons]
    let c := locatedNeckCut site.simplyConnected site.neck.closedCollar (embed _ site.neck) site.point
    obtain ⟨l⟩ := site.leftCap
    obtain ⟨r⟩ := site.rightCap
    obtain ⟨eL⟩ := relabeled_cap_identifies checked_cap_relabeling c.cut.left.regularPiece l
    obtain ⟨eR⟩ := relabeled_cap_identifies checked_cap_relabeling c.cut.right.regularPiece r
    exact ⟨h.1,.connectedSum (locatedCut_connectedSum c)
      (standardDecomposition_homeomorph eL.symm h.2.1)
      (standardDecomposition_homeomorph eR.symm h.2.2.1),h.2.2.2⟩
theorem LocatedChain.reconstruct {embed : EpsilonNeckEmbeddingStatement.{u}} {xs ys cs d}
    (m : LocatedChain embed xs ys cs d) : EveryStandard ys → EveryStandard xs := by
  induction m with
  | refl => exact id
  | tail _ step ih => exact fun h => ih (step.reconstruct h)
/-- **Math.** A real event retains the complete cut-site list and its operation word. -/
structure LocatedEvent (embed : EpsilonNeckEmbeddingStatement.{u})
    (xs ys : List ClosedThreeManifold.{u}) where
  sites : List (LocatedCutSite embed)
  discards : ℕ
  chain : LocatedChain embed xs ys sites discards
  nontrivial : sites ≠ [] ∨ 0 < discards
theorem LocatedEvent.active {embed : EpsilonNeckEmbeddingStatement.{u}} {xs ys}
    (e : LocatedEvent embed xs ys) : 1 ≤ e.sites.length + e.discards := by
  rcases e.nontrivial with hn | hd
  · have hp : 0 < e.sites.length := List.length_pos_iff.mpr hn; omega
  · omega
/-- **Math.** A potentially infinite set of actual event records. This is still
an output certificate to be produced by geometry, not a Ricci-flow construction. -/
structure LocatedProjection (embed : EpsilonNeckEmbeddingStatement.{u})
    (M : ClosedThreeManifold.{u}) where
  horizon : ℝ
  horizon_pos : 0 < horizon
  events : Set ℝ
  event_times : events ⊆ Ioo 0 horizon
  pre : ℝ → List ClosedThreeManifold.{u}
  post : ℝ → List ClosedThreeManifold.{u}
  initial : post 0 = [M]
  operations : ∀ t ∈ events, LocatedEvent embed (pre t) (post t)
  ordinary : ∀ s t, 0 ≤ s → s < t → t ≤ horizon → events ∩ Ioo s t = ∅ →
    Relation.ReflTransGen RepresentativeStep (post s) (pre t)
private theorem backwards_chain {xs ys : List ClosedThreeManifold.{u}}
    (h : Relation.ReflTransGen (fun a b => EveryStandard b → EveryStandard a) xs ys) :
    EveryStandard ys → EveryStandard xs := by
  induction h with | refl => exact id | tail _ hstep ih => exact fun h => ih (hstep h)
private theorem ordinary_backwards {xs ys : List ClosedThreeManifold.{u}}
    (h : Relation.ReflTransGen RepresentativeStep xs ys) : EveryStandard ys → EveryStandard xs := by
  induction h with
  | refl => exact id
  | tail _ step ih => exact fun h => ih (representative_reconstruct step h)
theorem locatedProjection_trace {embed : EpsilonNeckEmbeddingStatement.{u}}
    {M : ClosedThreeManifold.{u}} (H : LocatedProjection embed M)
    (hend : H.pre H.horizon = []) (budget : UniformEventBudget.{u} H.horizon H.events) :
    FiniteExtinctionTrace [M] := by
  obtain ⟨a,delta,V,c,ha,hd,hcover⟩ := budget
  have finite := (CriticalPath.SurgeryBudget.finite_event_set_of_measured_histories
    H.events ha hd hcover).1
  have chain := checked_finite_timeline (List ClosedThreeManifold.{u})
    (fun xs ys => EveryStandard ys → EveryStandard xs) H.pre H.post 0 H.horizon
    H.horizon_pos H.events finite H.event_times
    (fun t ht => Relation.ReflTransGen.single (H.operations t ht).chain.reconstruct)
    (fun s t hs hst ht he => Relation.ReflTransGen.single
      (ordinary_backwards (H.ordinary s t hs hst ht he)))
  have last : EveryStandard (H.pre H.horizon) := by rw [hend]; simp [EveryStandard]
  have first := backwards_chain chain last
  rw [H.initial] at first
  exact standard_eliminates_context (first M (by simp)) [] [] .empty
#print axioms LocatedMove.balance
#print axioms LocatedChain.balance
#print axioms LocatedMove.reconstruct
#print axioms LocatedChain.reconstruct
#print axioms LocatedEvent.active
#print axioms locatedProjection_trace
end PoincareConjecture.ProofContract.Refinement20260927
