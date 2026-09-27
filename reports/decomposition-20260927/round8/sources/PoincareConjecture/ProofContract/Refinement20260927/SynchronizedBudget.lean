import PoincareConjecture.ProofContract.Refinement20260927.CountedSurgery
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory CriticalPath.SurgeryBudget
/-- **Math.** The topological disjoint union of the ACTUAL recorded components. -/
abbrev ComponentCarrier (xs : List ClosedThreeManifold.{u}) :=
  (i : Fin xs.length) × (xs.get i)
/-- **Math.** A measured slice has exactly the recorded topology, with its Borel
sigma algebra. This alone does NOT identify every local neck tensor. -/
structure ComponentRealization (X : MeasuredSlice.{u}) (xs : List ClosedThreeManifold.{u}) where
  topology : TopologicalSpace X
  borel_eq : X.measurable = @borel X topology
  identification : @Homeomorph (ComponentCarrier xs) X inferInstance topology
/-- **Math.** Counts and component lists come from the SAME projected events.
Unlike the previous history, neither component_step nor event_active is a field. -/
structure CountedNeckHistory (embed : EpsilonNeckEmbeddingStatement.{u})
    {M : ClosedThreeManifold.{u}}
    (H : RelabeledProjection checked_side_atlas checked_negative_collar M)
    (n : ℕ) (a rho B epsilon0 initialVolume : ℝ) where
  pre : ℕ → MeasuredSlice.{u}
  post : ℕ → MeasuredSlice.{u}
  time : ℕ → ℝ
  cuts : ℕ → ℕ
  discards : ℕ → ℕ
  time_zero : time 0 = 0
  time_mono : Monotone time
  horizon : ∀ i ≤ n, time i ≤ H.horizon
  initial_volume : (post 0).volume = initialVolume
  event_times : ∀ i < n, time (i+1) ∈ H.events
  between : ∀ i < n, Relation.ReflTransGen RepresentativeStep
    (H.post (time i)) (H.pre (time (i+1)))
  operations : ∀ i < n, ActiveMetricEvent embed
    (H.pre (time (i+1))) (H.post (time (i+1))) (cuts i) (discards i)
  preTopology : ∀ i < n, ComponentRealization (pre i) (H.pre (time (i+1)))
  postTopology : ∀ i ≤ n, ComponentRealization (post i) (H.post (time i))
  evolution : ∀ i < n, Nonempty (RicciIntervalBridge (post i) (pre i) a (time (i+1)-time i))
  replacement : ∀ i < n, MeasuredReplacement (pre i) (post (i+1)) (cuts i)
  neckModels : ∀ i (hi : i < n) (j : Fin (cuts i)),
    NeckReplacementModel (pre i) (post (i+1))
      ((replacement i hi).old (some j)) ((replacement i hi).new (some j)) B epsilon0 rho
/-- **Math.** Two former numeric assumptions are derived from actual operations. -/
def CountedNeckHistory.toControlled {embed : EpsilonNeckEmbeddingStatement.{u}}
    {M : ClosedThreeManifold.{u}} {H : RelabeledProjection checked_side_atlas checked_negative_collar M}
    {n : ℕ} {a rho B epsilon0 V : ℝ} (h : CountedNeckHistory embed H n a rho B epsilon0 V) :
    NeckControlledHistory.{u} n a H.horizon rho B epsilon0 V 1 where
  pre := h.pre
  post := h.post
  time := h.time
  cuts := h.cuts
  discards := h.discards
  components := fun i => (H.post (h.time i)).length
  time_zero := h.time_zero
  time_mono := h.time_mono
  horizon := h.horizon
  initial_volume := h.initial_volume
  initial_components := by rw [h.time_zero,H.initial]; rfl
  evolution := h.evolution
  replacement := h.replacement
  neckModels := h.neckModels
  component_step := by
    intro i hi
    have hb := (h.operations i hi).balance
    have ho := representative_chain_length (h.between i hi)
    exact le_of_eq (hb.trans (congrArg (fun k : ℕ => k+h.cuts i) ho))
  event_active := fun i hi => (h.operations i hi).active
/-- **Math.** The same projected states determine the counts in each sample history. -/
def CountedNeckBudget (embed : EpsilonNeckEmbeddingStatement.{u})
    (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M)
    (B epsilon0 : ℝ) (H : RelabeledProjection checked_side_atlas checked_negative_collar M) : Prop :=
  ∃ a rho : ℝ, d.scalarConstant ≤ a ∧ 0 < rho ∧
    ∀ s : Finset ℝ, (↑s : Set ℝ) ⊆ H.events → ∃ n : ℕ,
      ∃ h : CountedNeckHistory embed H n a rho B epsilon0 (initialMetricSlice M d.metric).volume,
        h.post 0 = initialMetricSlice M d.metric ∧
        ∀ t ∈ s, ∃ i : Fin n, h.time (i.val+1) = t
theorem counted_budget_to_anchored {embed : EpsilonNeckEmbeddingStatement.{u}}
    (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M) {B epsilon0 : ℝ}
    (H : RelabeledProjection checked_side_atlas checked_negative_collar M)
    (h : CountedNeckBudget embed M d B epsilon0 H) :
    AnchoredNeckBudget M d B epsilon0 H.horizon H.events := by
  obtain ⟨a,rho,ha,hr,samples⟩ := h
  refine ⟨a,rho,ha,hr,?_⟩
  intro s hs
  obtain ⟨n,h,start,cover⟩ := samples s hs
  exact ⟨n,h.toControlled,start,cover⟩
/-- **Math.** Still a RESEARCH producer. Counts and global measured carriers
are synchronized; local neck tensors and unaffected-core maps still need construction. -/
def CountedGeometryProducerStatement (embed : EpsilonNeckEmbeddingStatement.{u}) : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M),
    SimplyConnectedSpace M → ∃ B : ℝ, 0 ≤ B ∧ ∀ epsilon0 : ℝ, 0 < epsilon0 →
      ∃ H : RelabeledProjection checked_side_atlas checked_negative_collar M,
        H.pre H.horizon = [] ∧ CountedNeckBudget embed M d B epsilon0 H
theorem neck_loss_producer_of_counted (embed : EpsilonNeckEmbeddingStatement.{u})
    (producer : CountedGeometryProducerStatement embed) : NeckLossGeometryProducerStatement.{u} := by
  intro M hsm d hsc
  obtain ⟨B,hB,run⟩ := producer M d hsc
  refine ⟨B,hB,?_⟩
  intro eps heps
  obtain ⟨H,hend,hbudget⟩ := run eps heps
  exact ⟨H,hend,counted_budget_to_anchored M d H hbudget⟩
/-- **Math.** Checked parent from the refined inputs to the unchanged V1 goal. -/
theorem public_of_counted_frontier (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (embed : EpsilonNeckEmbeddingStatement.{u})
    (geometry : CountedGeometryProducerStatement embed) : TopologicalPoincareStatement.{u} :=
  public_after_twelve triangulate atlas (neck_loss_producer_of_counted embed geometry)
#print axioms CountedNeckHistory.toControlled
#print axioms counted_budget_to_anchored
#print axioms neck_loss_producer_of_counted
#print axioms public_of_counted_frontier
end PoincareConjecture.ProofContract.Refinement20260927
