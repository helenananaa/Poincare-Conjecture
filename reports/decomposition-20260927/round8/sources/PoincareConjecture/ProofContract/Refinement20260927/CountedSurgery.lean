import PoincareConjecture.ProofContract.Refinement20260927.GeometricNeck
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
/-- **Math.** The nontrivial moves have their actual geometric witnesses.
The two natural-number indices are their numbers of cuts and discards. -/
inductive MetricSurgeryMove (embed : EpsilonNeckEmbeddingStatement.{u}) :
    List ClosedThreeManifold.{u} → List ClosedThreeManifold.{u} → ℕ → ℕ → Prop
  | regular {xs ys} : RepresentativeStep xs ys → MetricSurgeryMove embed xs ys 0 0
  | covered (before after : List ClosedThreeManifold.{u}) (M) : HasSphereCover M →
      MetricSurgeryMove embed (before ++ M :: after) (before ++ after) 0 1
  | handle (before after : List ClosedThreeManifold.{u}) (M) : IsSphereHandle M →
      MetricSurgeryMove embed (before ++ M :: after) (before ++ after) 0 1
  | neck (before after : List ClosedThreeManifold.{u}) {M : ClosedThreeManifold.{u}}
      (hsc : SimplyConnectedSpace M) (n : AmbientMetricNeck M) (p : Sphere2)
      (A B : ClosedThreeManifold.{u})
      (left : Nonempty (RelabeledCap (metricNeckCut embed hsc n p).left.regularPiece.toCollaredPiece A))
      (right : Nonempty (RelabeledCap (metricNeckCut embed hsc n p).right.regularPiece.toCollaredPiece B)) :
      MetricSurgeryMove embed (before ++ M :: after) (before ++ A :: B :: after) 1 0
/-- **Math.** A finite word of genuine moves, allowing harmless representative changes. -/
inductive MetricSurgeryChain (embed : EpsilonNeckEmbeddingStatement.{u}) :
    List ClosedThreeManifold.{u} → List ClosedThreeManifold.{u} → ℕ → ℕ → Prop
  | refl (xs) : MetricSurgeryChain embed xs xs 0 0
  | tail {xs zs ys k d k' d'} : MetricSurgeryChain embed xs zs k d →
      MetricSurgeryMove embed zs ys k' d' → MetricSurgeryChain embed xs ys (k+k') (d+d')
theorem representative_length {xs ys : List ClosedThreeManifold.{u}}
    (h : RepresentativeStep xs ys) : ys.length = xs.length := by
  cases h with
  | change => simp
  | reorder p => exact p.length_eq.symm
theorem representative_chain_length {xs ys : List ClosedThreeManifold.{u}}
    (h : Relation.ReflTransGen RepresentativeStep xs ys) : ys.length = xs.length := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact (representative_length step).trans ih
theorem MetricSurgeryMove.balance {embed : EpsilonNeckEmbeddingStatement.{u}}
    {xs ys : List ClosedThreeManifold.{u}} {k d : ℕ} (h : MetricSurgeryMove embed xs ys k d) :
    ys.length + d = xs.length + k := by
  cases h with
  | regular h => simpa using representative_length h
  | covered => simp; omega
  | handle => simp; omega
  | neck => simp; omega
theorem MetricSurgeryChain.balance {embed : EpsilonNeckEmbeddingStatement.{u}}
    {xs ys : List ClosedThreeManifold.{u}} {k d : ℕ} (h : MetricSurgeryChain embed xs ys k d) :
    ys.length + d = xs.length + k := by
  induction h with
  | refl => simp
  | tail _ step ih => have hb := step.balance; omega
theorem MetricSurgeryMove.toRelabeled {embed : EpsilonNeckEmbeddingStatement.{u}}
    {xs ys : List ClosedThreeManifold.{u}} {k d : ℕ} (h : MetricSurgeryMove embed xs ys k d) :
    RelabeledSurgeryStep checked_side_atlas checked_negative_collar xs ys := by
  cases h with
  | regular h => exact .regular h
  | covered b a M h => exact .discardCovered b a M h
  | handle b a M h => exact .discardHandle b a M h
  | neck b a hsc n p A B l r =>
    exact .neck b a hsc n.closedCollar (embed _ n) p A B l r
theorem MetricSurgeryChain.toRelabeled {embed : EpsilonNeckEmbeddingStatement.{u}}
    {xs ys : List ClosedThreeManifold.{u}} {k d : ℕ} (h : MetricSurgeryChain embed xs ys k d) :
    Relation.ReflTransGen (RelabeledSurgeryStep checked_side_atlas checked_negative_collar) xs ys := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih step.toRelabeled
/-- **Math.** At least one REAL surgery/discard is exhibited. No numeric
activity inequality is assumed; ordinary-only changes are not events. -/
inductive ActiveMetricEvent (embed : EpsilonNeckEmbeddingStatement.{u}) :
    List ClosedThreeManifold.{u} → List ClosedThreeManifold.{u} → ℕ → ℕ → Prop
  | cut {xs zs ws ys k d} : Relation.ReflTransGen RepresentativeStep xs zs →
      MetricSurgeryMove embed zs ws 1 0 → MetricSurgeryChain embed ws ys k d →
      ActiveMetricEvent embed xs ys (k+1) d
  | discard {xs zs ws ys k d} : Relation.ReflTransGen RepresentativeStep xs zs →
      MetricSurgeryMove embed zs ws 0 1 → MetricSurgeryChain embed ws ys k d →
      ActiveMetricEvent embed xs ys k (d+1)
theorem ActiveMetricEvent.balance {embed : EpsilonNeckEmbeddingStatement.{u}}
    {xs ys : List ClosedThreeManifold.{u}} {k d : ℕ} (h : ActiveMetricEvent embed xs ys k d) :
    ys.length + d = xs.length + k := by
  cases h with
  | cut pre step tail =>
    have hp := representative_chain_length pre
    have hs := step.balance
    have ht := tail.balance
    omega
  | discard pre step tail =>
    have hp := representative_chain_length pre
    have hs := step.balance
    have ht := tail.balance
    omega
theorem ActiveMetricEvent.active {embed : EpsilonNeckEmbeddingStatement.{u}}
    {xs ys : List ClosedThreeManifold.{u}} {k d : ℕ} (h : ActiveMetricEvent embed xs ys k d) :
    1 ≤ k+d := by cases h <;> omega
theorem representative_to_relabeled {xs ys : List ClosedThreeManifold.{u}}
    (h : Relation.ReflTransGen RepresentativeStep xs ys) :
    Relation.ReflTransGen (RelabeledSurgeryStep checked_side_atlas checked_negative_collar) xs ys := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (.regular step)
theorem ActiveMetricEvent.toRelabeled {embed : EpsilonNeckEmbeddingStatement.{u}}
    {xs ys : List ClosedThreeManifold.{u}} {k d : ℕ} (h : ActiveMetricEvent embed xs ys k d) :
    Relation.ReflTransGen (RelabeledSurgeryStep checked_side_atlas checked_negative_collar) xs ys := by
  cases h with
  | cut pre step tail =>
    exact (Relation.ReflTransGen.tail (representative_to_relabeled pre) step.toRelabeled).trans tail.toRelabeled
  | discard pre step tail =>
    exact (Relation.ReflTransGen.tail (representative_to_relabeled pre) step.toRelabeled).trans tail.toRelabeled
#print axioms representative_length
#print axioms representative_chain_length
#print axioms MetricSurgeryMove.balance
#print axioms MetricSurgeryChain.balance
#print axioms MetricSurgeryMove.toRelabeled
#print axioms MetricSurgeryChain.toRelabeled
#print axioms ActiveMetricEvent.balance
#print axioms ActiveMetricEvent.active
#print axioms representative_to_relabeled
#print axioms ActiveMetricEvent.toRelabeled
end PoincareConjecture.ProofContract.Refinement20260927
