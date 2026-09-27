import PoincareConjecture.ProofContract.Refinement20260927.LocatedEvents
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory CriticalPath.SurgeryBudget MorganTianLib
open scoped Manifold ContDiff
/-- **Math.** Exact common data used both in a topology cut and a volume-loss model.
Equality of these keys means the same region, metric, center, accuracy and neck chart. -/
structure NeckIdentity where
  region : SmoothVolumeRegion.{u}
  metric : Riemannian.RiemannianMetric (𝓡 3) region
  center : region
  epsilon : ℝ
  neck : EpsilonNeckStructure epsilon metric center
def AmbientMetricNeck.identity {M : ClosedThreeManifold.{u}} (n : AmbientMetricNeck M) :
    NeckIdentity.{u} := ⟨n.region,n.metric,n.center,n.epsilon,n.neck⟩
def NeckReplacementModel.identity {X Y : MeasuredSlice.{u}} {old : Set X} {new : Set Y}
    {B eps rho : ℝ} (w : NeckReplacementModel X Y old new B eps rho) : NeckIdentity.{u} :=
  ⟨w.space,w.metric,w.center,w.epsilon,w.neck⟩
/-- **Math.** Each loss model is indexed by, and equal in neck data to, the
corresponding site in the SAME event operation list. Local inclusion/measure
compatibility beyond this common neck remains an explicit construction obligation. -/
structure MatchedNeckHistory (embed : EpsilonNeckEmbeddingStatement.{u})
    {M : ClosedThreeManifold.{u}}
    (H : LocatedProjection embed M)
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
  cuts_eq : ∀ i (hi : i < n), cuts i = (H.operations (time (i+1)) (event_times i hi)).sites.length
  discards_eq : ∀ i (hi : i < n), discards i = (H.operations (time (i+1)) (event_times i hi)).discards
  preTopology : ∀ i < n, ComponentRealization (pre i) (H.pre (time (i+1)))
  postTopology : ∀ i ≤ n, ComponentRealization (post i) (H.post (time i))
  evolution : ∀ i < n, Nonempty (RicciIntervalBridge (post i) (pre i) a (time (i+1)-time i))
  replacement : ∀ i < n, MeasuredReplacement (pre i) (post (i+1)) (cuts i)
  neckModels : ∀ i (hi : i < n) (j : Fin (cuts i)),
    NeckReplacementModel (pre i) (post (i+1))
      ((replacement i hi).old (some j)) ((replacement i hi).new (some j)) B epsilon0 rho
  model_identity : ∀ i (hi : i < n) (j : Fin (cuts i)),
    (neckModels i hi j).identity =
      ((H.operations (time (i+1)) (event_times i hi)).sites.get (Fin.cast (cuts_eq i hi) j)).neck.identity
/-- **Math.** Two former numeric assumptions are derived from actual operations. -/
def MatchedNeckHistory.toControlled {embed : EpsilonNeckEmbeddingStatement.{u}}
    {M : ClosedThreeManifold.{u}} {H : LocatedProjection embed M}
    {n : ℕ} {a rho B epsilon0 V : ℝ} (h : MatchedNeckHistory embed H n a rho B epsilon0 V) :
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
    have hb := (H.operations (h.time (i+1)) (h.event_times i hi)).chain.balance
    rw [← h.cuts_eq i hi, ← h.discards_eq i hi] at hb
    have ho := representative_chain_length (h.between i hi)
    exact le_of_eq (hb.trans (congrArg (fun k : ℕ => k+h.cuts i) ho))
  event_active := by
    intro i hi
    have ha := (H.operations (h.time (i+1)) (h.event_times i hi)).active
    simpa only [← h.cuts_eq i hi, ← h.discards_eq i hi] using ha
/-- **Math.** The same projected states determine the counts in each sample history. -/
def MatchedNeckBudget (embed : EpsilonNeckEmbeddingStatement.{u})
    (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M)
    (B epsilon0 : ℝ) (H : LocatedProjection embed M) : Prop :=
  ∃ a rho : ℝ, d.scalarConstant ≤ a ∧ 0 < rho ∧
    ∀ s : Finset ℝ, (↑s : Set ℝ) ⊆ H.events → ∃ n : ℕ,
      ∃ h : MatchedNeckHistory embed H n a rho B epsilon0 (initialMetricSlice M d.metric).volume,
        h.post 0 = initialMetricSlice M d.metric ∧
        ∀ t ∈ s, ∃ i : Fin n, h.time (i.val+1) = t
theorem matched_budget_to_anchored {embed : EpsilonNeckEmbeddingStatement.{u}}
    (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M) {B epsilon0 : ℝ}
    (H : LocatedProjection embed M)
    (h : MatchedNeckBudget embed M d B epsilon0 H) :
    AnchoredNeckBudget M d B epsilon0 H.horizon H.events := by
  obtain ⟨a,rho,ha,hr,samples⟩ := h
  refine ⟨a,rho,ha,hr,?_⟩
  intro s hs
  obtain ⟨n,h,start,cover⟩ := samples s hs
  exact ⟨n,h.toControlled,start,cover⟩
/-- **Math.** RESEARCH: actual geometry must produce this fully labeled projection
and its matched histories. No claim of solved flow/smoothing/exhaustion is made. -/
def MatchedGeometryProducerStatement (embed : EpsilonNeckEmbeddingStatement.{u}) : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M),
    SimplyConnectedSpace M → ∃ B : ℝ, 0 ≤ B ∧ ∀ epsilon0 : ℝ, 0 < epsilon0 →
      ∃ H : LocatedProjection embed M,
        H.pre H.horizon = [] ∧ MatchedNeckBudget embed M d B epsilon0 H
theorem geometric_of_matched_producer (embed : EpsilonNeckEmbeddingStatement.{u})
    (producer : MatchedGeometryProducerStatement embed) : GeometricTraceStatement.{u} := by
  intro M hsm hsc
  letI : IsSmooth M := hsm
  obtain ⟨d⟩ := metric_initialData_exists M
  obtain ⟨B,hB,run⟩ := producer M d hsc
  obtain ⟨eps,heps,allowance⟩ := checked_uniform_neck_allowance B hB
  obtain ⟨H,hend,budget⟩ := run eps heps
  have anchored := matched_budget_to_anchored M d H budget
  have ricci := anchored_neck_to_ricci checked_finite_cap_scaling M d hB allowance anchored
  exact locatedProjection_trace H hend (anchored_budget_to_uniform checked_closed_scalar M d ricci)
/-- **Math.** Repair adapter: unchanged V1 root, located cut witnesses and site-indexed losses. -/
theorem public_of_matched_frontier (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (embed : EpsilonNeckEmbeddingStatement.{u})
    (geometry : MatchedGeometryProducerStatement embed) : TopologicalPoincareStatement.{u} :=
  Proofs.topological_of_two_contracts
    (smoothing_of_finitePL_producers triangulate (finitePLAtlasProducer_iff.mp atlas))
    (geometric_of_matched_producer embed geometry)
#print axioms MatchedNeckHistory.toControlled
#print axioms matched_budget_to_anchored
#print axioms geometric_of_matched_producer
#print axioms public_of_matched_frontier
end PoincareConjecture.ProofContract.Refinement20260927
