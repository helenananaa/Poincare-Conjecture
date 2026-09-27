import PoincareConjecture.ProofContract.Refinement20260927.RecordedMetricPatch
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory CriticalPath.SurgeryBudget MorganTianLib Function
open scoped Manifold ContDiff Topology ENNReal BigOperators
/-- **Math.** The measured neck patch is an actual open subset of the metric region. -/
theorem neck_removed_measurable {M : SmoothVolumeRegion.{u}}
    {g : Riemannian.RiemannianMetric (𝓡 3) M} {x : M} {eps : ℝ}
    (S : EpsilonNeckStructure eps g x) : MeasurableSet (neckRemovedRegion S) := by
  have hcoord : Continuous (fun p : epsilonNeckDomain eps => p.1.2 0) := by fun_prop
  have hopen : IsOpen {p : epsilonNeckDomain eps |
      -(eps⁻¹)/2 < p.1.2 0 ∧ p.1.2 0 < -(eps⁻¹)/4} :=
    (isOpen_lt continuous_const hcoord).inter (isOpen_lt hcoord continuous_const)
  exact (S.phi.toHomeomorph.isOpenMap _ hopen).measurableSet
/-- **Math.** No freely assumed old/new measure-preserving fields. Their maps are
specified smooth embeddings with differential pullback of actual metrics. -/
structure MetricPatchReplacement (X Y : MeasuredSlice.{u}) (old : Set X) (new : Set Y)
    (B epsilon0 rho : ℝ) where
  space : SmoothVolumeRegion.{u}
  metric : Riemannian.RiemannianMetric (𝓡 3) space
  center : space
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_small : epsilon < epsilon0
  neck : EpsilonNeckStructure epsilon metric center
  scale_lower : rho ≤ neck.scale
  oldPatch : RecordedIsometricPatch X space metric
  old_inside : oldPatch.image (neckRemovedRegion neck) ⊆ old
  capCount : ℕ
  caps : Fin capCount → CompactCapModel.{u}
  cap_bound : (∑ i, (caps i).baseVolume) ≤ B
  newPatches : ∀ i, RecordedIsometricPatch Y (caps i).space
    (rescaledMetric (caps i).metric (neck.scale^2)
      (sq_pos_of_pos (epsilonNeck_scale_pos_and_metric_normalization neck).1))
  newPieces : Fin capCount → Set Y
  new_measurable : ∀ i, MeasurableSet (newPieces i)
  new_disjoint : Pairwise (Disjoint on newPieces)
  new_cover : (⋃ i, newPieces i) = new
  new_image : ∀ i, (newPatches i).image (caps i).region = newPieces i
/-- **Math.** The conversion proves the two measure-preservation fields rather
than reading them from the input. Exact metric/neck data are preserved. -/
def MetricPatchReplacement.toModel (localDensity : LocalPatchDensityStatement.{u})
    (assemble : OpenPatchAssemblyStatement.{u}) {X Y : MeasuredSlice.{u}}
    {old : Set X} {new : Set Y} {B eps rho : ℝ}
    (w : MetricPatchReplacement X Y old new B eps rho) :
    NeckReplacementModel X Y old new B eps rho where
  space := w.space
  metric := w.metric
  center := w.center
  epsilon := w.epsilon
  epsilon_pos := w.epsilon_pos
  epsilon_small := w.epsilon_small
  neck := w.neck
  scale_lower := w.scale_lower
  oldPatch := w.oldPatch.image (neckRemovedRegion w.neck)
  oldPatch_subset := w.old_inside
  oldMap := w.oldPatch.map
  old_preserves := w.oldPatch.preserves localDensity assemble _ (neck_removed_measurable w.neck)
  capCount := w.capCount
  caps := w.caps
  cap_bound := w.cap_bound
  newPieces := w.newPieces
  new_measurable := w.new_measurable
  new_disjoint := w.new_disjoint
  new_cover := w.new_cover
  newMap := fun i => (w.newPatches i).map
  new_preserves := by
    intro i
    have hp := (w.newPatches i).preserves localDensity assemble
      (w.caps i).region (w.caps i).compact.isClosed.measurableSet
    rw [w.new_image i] at hp
    exact hp
def MetricPatchReplacement.identity {X Y : MeasuredSlice.{u}}
    {old : Set X} {new : Set Y} {B eps rho : ℝ}
    (w : MetricPatchReplacement X Y old new B eps rho) : NeckIdentity.{u} :=
  ⟨w.space,w.metric,w.center,w.epsilon,w.neck⟩
theorem MetricPatchReplacement.toModel_identity
    (localDensity : LocalPatchDensityStatement.{u}) (assemble : OpenPatchAssemblyStatement.{u})
    {X Y : MeasuredSlice.{u}} {old : Set X} {new : Set Y} {B eps rho : ℝ}
    (w : MetricPatchReplacement X Y old new B eps rho) :
    (w.toModel localDensity assemble).identity = w.identity := rfl
/-- **Math.** Unaffected material has the same metric model. Complete deletion
is a separate constructor, allowing an empty final slice without fake charts. -/
inductive MetricCore (X Y : MeasuredSlice.{u}) (old : Set X) (new : Set Y) : Type (u+1)
  | empty : new = ∅ → MetricCore X Y old new
  | retained (M : SmoothVolumeRegion.{u}) (g : Riemannian.RiemannianMetric (𝓡 3) M)
      (s : Set M) (hs : MeasurableSet s)
      (left : RecordedIsometricPatch X M g) (right : RecordedIsometricPatch Y M g)
      (old_subset : left.image s ⊆ old) (new_eq : right.image s = new) : MetricCore X Y old new
theorem MetricCore.nonincrease (localDensity : LocalPatchDensityStatement.{u})
    (assemble : OpenPatchAssemblyStatement.{u}) {X Y : MeasuredSlice.{u}}
    {old : Set X} {new : Set Y} (c : MetricCore X Y old new) :
    (Y.measure new).toReal ≤ (X.measure old).toReal := by
  cases c with
  | empty h => simpa [h] using (ENNReal.toReal_nonneg : (0 : ℝ) ≤ (X.measure old).toReal)
  | retained M g s hs left right old_subset new_eq =>
    have hl := (left.preserves localDensity assemble s hs).measure_preimage
      MeasurableSet.univ.nullMeasurableSet
    have hr := (right.preserves localDensity assemble s hs).measure_preimage
      MeasurableSet.univ.nullMeasurableSet
    have hl' : regionMeasure g s = X.measure (left.image s) := by simpa using hl
    have hr' : regionMeasure g s = Y.measure new := by simpa [new_eq] using hr
    have hle : Y.measure new ≤ X.measure old :=
      hr'.symm.le.trans (hl'.le.trans (measure_mono old_subset))
    exact ENNReal.toReal_mono (measure_ne_top X.measure old) hle
/-- **Math.** A real partition with a metric model of surviving material,
rather than an assumed numerical core_nonincrease. -/
structure MetricReplacementPartition (X Y : MeasuredSlice.{u}) (k : ℕ) where
  old : Option (Fin k) → Set X
  new : Option (Fin k) → Set Y
  old_measurable : ∀ i, MeasurableSet (old i)
  new_measurable : ∀ i, MeasurableSet (new i)
  old_disjoint : Pairwise (Disjoint on old)
  new_disjoint : Pairwise (Disjoint on new)
  old_cover : (⋃ i, old i) = Set.univ
  new_cover : (⋃ i, new i) = Set.univ
  core : MetricCore X Y (old none) (new none)
def MetricReplacementPartition.toMeasured (localDensity : LocalPatchDensityStatement.{u})
    (assemble : OpenPatchAssemblyStatement.{u}) {X Y : MeasuredSlice.{u}} {k : ℕ}
    (p : MetricReplacementPartition X Y k) : MeasuredReplacement X Y k where
  old := p.old
  new := p.new
  old_measurable := p.old_measurable
  new_measurable := p.new_measurable
  old_disjoint := p.old_disjoint
  new_disjoint := p.new_disjoint
  old_cover := p.old_cover
  new_cover := p.new_cover
  core_nonincrease := p.core.nonincrease localDensity assemble
#print axioms neck_removed_measurable
#print axioms MetricPatchReplacement.toModel
#print axioms MetricPatchReplacement.toModel_identity
#print axioms MetricCore.nonincrease
#print axioms MetricReplacementPartition.toMeasured
end PoincareConjecture.ProofContract.Refinement20260927
