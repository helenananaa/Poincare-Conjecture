import PoincareConjecture.ProofContract.Refinement20260927.MetricPatchTransport
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory CriticalPath.SurgeryBudget
open scoped Manifold ContDiff Topology
/-- **Math.** A recorded measure is explicitly the pushforward of an actual metric
measure through its topological realization. Existence of this realization is
not asserted for arbitrary records. Empty final records need no cap presentation. -/
structure MetricSlicePresentation (X : MeasuredSlice.{u}) where
  space : SmoothVolumeRegion.{u}
  metric : Riemannian.RiemannianMetric (𝓡 3) space
  topology : TopologicalSpace X
  borel_eq : X.measurable = @borel X topology
  realization : @Homeomorph space X inferInstance topology
  measure_eq : X.measure = Measure.map realization (regionMeasure metric)
/-- **Math.** The fixed realization transports restrictions to its actual image. -/
theorem MetricSlicePresentation.preserves_image {X : MeasuredSlice.{u}}
    (p : MetricSlicePresentation X) (s : Set p.space) :
    MeasurePreserving p.realization ((regionMeasure p.metric).restrict s)
      (X.measure.restrict (p.realization '' s)) := by
  letI : TopologicalSpace X := p.topology
  letI : BorelSpace X := ⟨p.borel_eq⟩
  let e : p.space ≃ᵐ X := p.realization.toMeasurableEquiv
  refine ⟨e.measurable, ?_⟩
  rw [p.measure_eq]
  change Measure.map e ((regionMeasure p.metric).restrict s) =
    (Measure.map e (regionMeasure p.metric)).restrict (e '' s)
  rw [e.restrict_map, e.injective.preimage_image]
/-- **Math.** The actual smooth map and metric identity replace an arbitrary
measure-preserving map. The target record fixes its topology and canonical volume. -/
structure RecordedIsometricPatch (X : MeasuredSlice.{u}) (M : SmoothVolumeRegion.{u})
    (g : Riemannian.RiemannianMetric (𝓡 3) M) where
  target : MetricSlicePresentation X
  inclusion : M → target.space
  smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ inclusion
  openEmbedding : Topology.IsOpenEmbedding inclusion
  pullsBack : PatchMetricPullback M target.space g target.metric inclusion
def RecordedIsometricPatch.map {X : MeasuredSlice.{u}} {M : SmoothVolumeRegion.{u}}
    {g : Riemannian.RiemannianMetric (𝓡 3) M} (p : RecordedIsometricPatch X M g) : M → X :=
  fun x => p.target.realization (p.inclusion x)
def RecordedIsometricPatch.image {X : MeasuredSlice.{u}} {M : SmoothVolumeRegion.{u}}
    {g : Riemannian.RiemannianMetric (𝓡 3) M} (p : RecordedIsometricPatch X M g) (s : Set M) : Set X :=
  p.target.realization '' (p.inclusion '' s)
theorem RecordedIsometricPatch.preserves (localDensity : LocalPatchDensityStatement.{u})
    (assemble : OpenPatchAssemblyStatement.{u}) {X : MeasuredSlice.{u}} {M : SmoothVolumeRegion.{u}}
    {g : Riemannian.RiemannianMetric (𝓡 3) M} (p : RecordedIsometricPatch X M g)
    (s : Set M) (hs : MeasurableSet s) :
    MeasurePreserving p.map ((regionMeasure g).restrict s) (X.measure.restrict (p.image s)) :=
  (p.target.preserves_image (p.inclusion '' s)).comp
    (metric_patch_preserves_restrict localDensity assemble M p.target.space g p.target.metric
      p.inclusion p.smooth p.openEmbedding p.pullsBack s hs)
#print axioms MetricSlicePresentation.preserves_image
#print axioms RecordedIsometricPatch.preserves
end PoincareConjecture.ProofContract.Refinement20260927
