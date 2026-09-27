import PoincareConjecture.ProofContract.Refinement20260927.MetricPatchReplacement
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory CriticalPath.SurgeryBudget
/-- **Math.** The same located event and neck identities now carry actual metric
patches; old/new volume transport and the core inequality are derived below. -/
structure PatchNeckHistory (embed : EpsilonNeckEmbeddingStatement.{u})
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
  replacement : ∀ i < n, MetricReplacementPartition (pre i) (post (i+1)) (cuts i)
  neckModels : ∀ i (hi : i < n) (j : Fin (cuts i)),
    MetricPatchReplacement (pre i) (post (i+1))
      ((replacement i hi).old (some j)) ((replacement i hi).new (some j)) B epsilon0 rho
  model_identity : ∀ i (hi : i < n) (j : Fin (cuts i)),
    (neckModels i hi j).identity =
      ((H.operations (time (i+1)) (event_times i hi)).sites.get (Fin.cast (cuts_eq i hi) j)).neck.identity
/-- **Math.** Old and new maps, core inequality and recorded loss models are
constructed from the two independent transport leaves and actual patch data. -/
def PatchNeckHistory.toMatched (localDensity : LocalPatchDensityStatement.{u})
    (assemble : OpenPatchAssemblyStatement.{u}) {embed : EpsilonNeckEmbeddingStatement.{u}}
    {M : ClosedThreeManifold.{u}} {H : LocatedProjection embed M} {n : ℕ}
    {a rho B eps V : ℝ} (h : PatchNeckHistory embed H n a rho B eps V) :
    MatchedNeckHistory embed H n a rho B eps V where
  pre := h.pre
  post := h.post
  time := h.time
  cuts := h.cuts
  discards := h.discards
  time_zero := h.time_zero
  time_mono := h.time_mono
  horizon := h.horizon
  initial_volume := h.initial_volume
  event_times := h.event_times
  between := h.between
  cuts_eq := h.cuts_eq
  discards_eq := h.discards_eq
  preTopology := h.preTopology
  postTopology := h.postTopology
  evolution := h.evolution
  replacement := fun i hi => (h.replacement i hi).toMeasured localDensity assemble
  neckModels := fun i hi j => (h.neckModels i hi j).toModel localDensity assemble
  model_identity := h.model_identity
/-- **Math.** Same initial metric, same event set, constants fixed before all samples. -/
def PatchNeckBudget (embed : EpsilonNeckEmbeddingStatement.{u})
    (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M)
    (B eps : ℝ) (H : LocatedProjection embed M) : Prop :=
  ∃ a rho : ℝ, d.scalarConstant ≤ a ∧ 0 < rho ∧
    ∀ s : Finset ℝ, (↑s : Set ℝ) ⊆ H.events → ∃ n : ℕ,
      ∃ h : PatchNeckHistory embed H n a rho B eps (initialMetricSlice M d.metric).volume,
        h.post 0 = initialMetricSlice M d.metric ∧
        ∀ t ∈ s, ∃ i : Fin n, h.time (i.val+1) = t
theorem patch_budget_to_matched (localDensity : LocalPatchDensityStatement.{u})
    (assemble : OpenPatchAssemblyStatement.{u}) {embed : EpsilonNeckEmbeddingStatement.{u}}
    (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M) {B eps : ℝ}
    (H : LocatedProjection embed M) (h : PatchNeckBudget embed M d B eps H) :
    MatchedNeckBudget embed M d B eps H := by
  obtain ⟨a,rho,ha,hr,samples⟩ := h
  refine ⟨a,rho,ha,hr,?_⟩
  intro s hs
  obtain ⟨n,h,start,cover⟩ := samples s hs
  exact ⟨n,h.toMatched localDensity assemble,start,cover⟩
/-- **Math.** RESEARCH: geometric production and metric realization remain open.
The new transport leaves do not assert that any actual flow or these patches exist. -/
def PatchGeometryProducerStatement (embed : EpsilonNeckEmbeddingStatement.{u}) : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M),
    SimplyConnectedSpace M → ∃ B : ℝ, 0 ≤ B ∧ ∀ eps : ℝ, 0 < eps →
      ∃ H : LocatedProjection embed M, H.pre H.horizon = [] ∧ PatchNeckBudget embed M d B eps H
theorem patch_producer_to_matched (localDensity : LocalPatchDensityStatement.{u})
    (assemble : OpenPatchAssemblyStatement.{u}) (embed : EpsilonNeckEmbeddingStatement.{u})
    (p : PatchGeometryProducerStatement embed) : MatchedGeometryProducerStatement embed := by
  intro M hsm d hsc
  obtain ⟨B,hB,run⟩ := p M d hsc
  refine ⟨B,hB,?_⟩
  intro eps heps
  obtain ⟨H,hend,budget⟩ := run eps heps
  exact ⟨H,hend,patch_budget_to_matched localDensity assemble M d H budget⟩
/-- **Math.** Exact V1 root: two independent local proof leaves and three
uncompleted research inputs. Earlier frozen declarations are unchanged. -/
theorem public_of_metric_patch_frontier (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u})
    (localDensity : LocalPatchDensityStatement.{u}) (assemble : OpenPatchAssemblyStatement.{u})
    (geometry : PatchGeometryProducerStatement.{u} checked_epsilon_neck_embedding.{u}) :
    TopologicalPoincareStatement.{u} :=
  public_after_thirteen triangulate atlas
    (patch_producer_to_matched localDensity assemble checked_epsilon_neck_embedding geometry)
#print axioms PatchNeckHistory.toMatched
#print axioms patch_budget_to_matched
#print axioms patch_producer_to_matched
#print axioms public_of_metric_patch_frontier
end PoincareConjecture.ProofContract.Refinement20260927
