import PoincareConjecture.ProofContract.Refinement20260927.AcceptedNine
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
open scoped Topology Manifold ContDiff
/-- Finite TOPological candidate on the original space. No smoothness field. -/
structure FiniteAtlasCandidate (M : ClosedThreeManifold.{u}) where
  indices : Finset M
  chart : indices → OpenPartialHomeomorph M Euclidean3
  covers : ∀ x : M, ∃ i : indices, x ∈ (chart i).source
/-- Exact independent overlap obligation for a fixed candidate. Both directions
are encoded by the ordinary smooth structure groupoid. -/
def SmoothTransition {M : ClosedThreeManifold.{u}} (c : FiniteAtlasCandidate M)
    (i j : c.indices) : Prop :=
  (c.chart i).symm.trans (c.chart j) ∈ contDiffGroupoid ∞ (𝓡 3)
/-- The finite overlap proofs are actually assembled into the exact V1 smoothing. -/
def finiteAtlas_smoothing {M : ClosedThreeManifold.{u}} (c : FiniteAtlasCandidate M)
    (compatible : ∀ i j, SmoothTransition c i j) : Smoothing M := by
  let chosen (x : M) : c.indices := Classical.choose (c.covers x)
  let a : ChartedSpace Euclidean3 M := {
    atlas := Set.range c.chart
    chartAt := fun x => c.chart (chosen x)
    mem_chart_source := fun x => Classical.choose_spec (c.covers x)
    chart_mem_atlas := fun x => ⟨chosen x,rfl⟩ }
  refine ⟨a, ?_⟩
  refine { compatible := ?_ }
  rintro e f ⟨i,rfl⟩ ⟨j,rfl⟩
  exact compatible i j
/-- Compactness reduces any actual smoothing to finite chart data. This does not
create a smoothing from a merely topological atlas. -/
theorem finiteAtlas_of_smoothing {M : ClosedThreeManifold.{u}} (s : Smoothing M) :
    ∃ c : FiniteAtlasCandidate M, ∀ i j, SmoothTransition c i j := by
  letI : ChartedSpace Euclidean3 M := s.atlas
  letI : IsManifold (𝓡 3) ∞ M := s.smooth
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (chartAt Euclidean3 x).source)
    (fun x => (chartAt Euclidean3 x).open_source)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x,mem_chart_source Euclidean3 x⟩)
  let c : FiniteAtlasCandidate M := {
    indices := t
    chart := fun i => chartAt Euclidean3 i.val
    covers := by
      intro x
      obtain ⟨i,hi,hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
      exact ⟨⟨i,hi⟩,hx⟩ }
  refine ⟨c, ?_⟩
  intro i j
  exact (contDiffGroupoid ∞ (𝓡 3)).compatible
    (chart_mem_atlas Euclidean3 i.val) (chart_mem_atlas Euclidean3 j.val)
theorem smoothing_iff_finite_compatible_atlas (M : ClosedThreeManifold.{u}) :
    Nonempty (Smoothing M) ↔ ∃ c : FiniteAtlasCandidate M, ∀ i j, SmoothTransition c i j := by
  constructor
  · rintro ⟨s⟩; exact finiteAtlas_of_smoothing s
  · rintro ⟨c,hc⟩; exact ⟨finiteAtlas_smoothing c hc⟩
/-- A precise delivery format, equivalent to the existing producer rather than
a newly proved producer. No independently selected atlas may be substituted. -/
def FinitePLAtlasProducerStatement : Prop :=
  ∀ M : ClosedThreeManifold.{u}, FinitePLPresentation M →
    ∃ c : FiniteAtlasCandidate M, ∀ i j, SmoothTransition c i j
theorem finitePLAtlasProducer_iff :
    FinitePLAtlasProducerStatement.{u} ↔ PLAtlasProducerStatement.{u} := by
  constructor
  · intro h M p
    exact (smoothing_iff_finite_compatible_atlas M).mpr (h M p)
  · intro h M p
    exact (smoothing_iff_finite_compatible_atlas M).mp (h M p)
theorem public_of_finite_atlas_producer (triangulate : TriangulationProducerStatement.{u})
    (finiteAtlas : FinitePLAtlasProducerStatement.{u})
    (geometry : RelabeledProjectionProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  public_after_nine triangulate (finitePLAtlasProducer_iff.mp finiteAtlas) geometry
#print axioms finiteAtlas_smoothing
#print axioms finiteAtlas_of_smoothing
#print axioms smoothing_iff_finite_compatible_atlas
#print axioms finitePLAtlasProducer_iff
#print axioms public_of_finite_atlas_producer
end PoincareConjecture.ProofContract.Refinement20260927
