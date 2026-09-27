import PoincareConjecture.ProofContract.Refinement20260927.AcceptedThirteen
import MorganTianLib.Ch02.NeckVolume.PullbackMeasure
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
/-- **Math.** Pointwise pullback of the ACTUAL metric through the specified map. -/
def PatchMetricPullback (M N : SmoothVolumeRegion.{u})
    (gM : Riemannian.RiemannianMetric (𝓡 3) M)
    (gN : Riemannian.RiemannianMetric (𝓡 3) N) (f : M → N) : Prop :=
  ∀ p : M, ∀ v w : TangentSpace (𝓡 3) p,
    gM.metricInner p v w = gN.metricInner (f p)
      (mfderiv (𝓡 3) (𝓡 3) f p v) (mfderiv (𝓡 3) (𝓡 3) f p w)
/-- **Math.** Local coordinate derivative and volume density relation, with
source and target chart membership stated explicitly. -/
def LocalPatchDensity (M N : SmoothVolumeRegion.{u})
    (gM : Riemannian.RiemannianMetric (𝓡 3) M)
    (gN : Riemannian.RiemannianMetric (𝓡 3) N) (f : M → N) : Prop :=
  ∀ (alpha : M) (beta : N) (p : M), p ∈ (extChartAt (𝓡 3) alpha).source →
    f p ∈ (extChartAt (𝓡 3) beta).source → ∃ D : Euclidean3 →L[ℝ] Euclidean3,
      HasFDerivAt (fun y : Euclidean3 =>
        extChartAt (𝓡 3) beta (f ((extChartAt (𝓡 3) alpha).symm y))) D
        (extChartAt (𝓡 3) alpha p) ∧
      |D.det| * MorganTianLib.chartVolumeDensity gN beta (extChartAt (𝓡 3) beta (f p)) =
        MorganTianLib.chartVolumeDensity gM alpha (extChartAt (𝓡 3) alpha p)
/-- **Math.** Independent analytic leaf: tensor pullback gives the chart Jacobian identity. -/
def LocalPatchDensityStatement : Prop :=
  ∀ (M N : SmoothVolumeRegion.{u})
    (gM : Riemannian.RiemannianMetric (𝓡 3) M)
    (gN : Riemannian.RiemannianMetric (𝓡 3) N) (f : M → N),
    ContMDiff (𝓡 3) (𝓡 3) ∞ f → PatchMetricPullback M N gM gN f →
    LocalPatchDensity M N gM gN f
/-- **Math.** Independent measure leaf: a local density certificate is sufficient
for countable-chart assembly. Surjectivity onto the ambient space is NOT assumed. -/
def OpenPatchAssemblyStatement : Prop :=
  ∀ (M N : SmoothVolumeRegion.{u})
    (gM : Riemannian.RiemannianMetric (𝓡 3) M)
    (gN : Riemannian.RiemannianMetric (𝓡 3) N) (f : M → N),
    Topology.IsOpenEmbedding f → LocalPatchDensity M N gM gN f →
    ∀ s : Set M, MeasurableSet s → regionMeasure gN (f '' s) = regionMeasure gM s
/-- **Math.** The specified map, not a newly chosen map, is volume-preserving. -/
theorem metric_patch_image (localDensity : LocalPatchDensityStatement.{u})
    (assemble : OpenPatchAssemblyStatement.{u}) (M N : SmoothVolumeRegion.{u})
    (gM : Riemannian.RiemannianMetric (𝓡 3) M)
    (gN : Riemannian.RiemannianMetric (𝓡 3) N) (f : M → N)
    (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f) (he : Topology.IsOpenEmbedding f)
    (hg : PatchMetricPullback M N gM gN f) (s : Set M) (hs : MeasurableSet s) :
    regionMeasure gN (f '' s) = regionMeasure gM s :=
  assemble M N gM gN f he (localDensity M N gM gN f hf hg) s hs
theorem metric_patch_preserves_restrict (localDensity : LocalPatchDensityStatement.{u})
    (assemble : OpenPatchAssemblyStatement.{u}) (M N : SmoothVolumeRegion.{u})
    (gM : Riemannian.RiemannianMetric (𝓡 3) M)
    (gN : Riemannian.RiemannianMetric (𝓡 3) N) (f : M → N)
    (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f) (he : Topology.IsOpenEmbedding f)
    (hg : PatchMetricPullback M N gM gN f) (s : Set M) (hs : MeasurableSet s) :
    MeasurePreserving f ((regionMeasure gM).restrict s)
      ((regionMeasure gN).restrict (f '' s)) := by
  have hm : Measurable f := he.continuous.measurable
  refine ⟨hm, ?_⟩
  ext t ht
  rw [Measure.map_apply hm ht, Measure.restrict_apply (ht.preimage hm), Measure.restrict_apply ht]
  have hv := metric_patch_image localDensity assemble M N gM gN f hf he hg
    (f ⁻¹' t ∩ s) ((ht.preimage hm).inter hs)
  rw [← hv]
  congr 1
  ext y
  constructor
  · rintro ⟨x,⟨hxt,hxs⟩,rfl⟩
    exact ⟨hxt,⟨x,hxs,rfl⟩⟩
  · rintro ⟨hyt,⟨x,hxs,rfl⟩⟩
    exact ⟨x,⟨hyt,hxs⟩,rfl⟩
#print axioms metric_patch_image
#print axioms metric_patch_preserves_restrict
end PoincareConjecture.ProofContract.Refinement20260927
