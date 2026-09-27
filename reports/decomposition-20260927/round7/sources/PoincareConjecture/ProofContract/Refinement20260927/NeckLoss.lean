import PoincareConjecture.ProofContract.Refinement20260927.AcceptedTen
import MorganTianLib.Ch02.NeckVolume.CompactCapGap
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory Riemannian MorganTianLib Function
open CriticalPath.SurgeryBudget
open scoped Topology Manifold ContDiff ENNReal BigOperators
/-- **Math.** A possibly noncompact smooth region. A whole closed manifold is NOT a neck. -/
structure SmoothVolumeRegion extends TopCat.{u} where
  hausdorff : T2Space toTopCat
  secondCountable : SecondCountableTopology toTopCat
  sigmaCompact : SigmaCompactSpace toTopCat
  nonempty : Nonempty toTopCat
  charts : ChartedSpace Euclidean3 toTopCat
  smooth : @IsManifold ℝ _ Euclidean3 _ _ Euclidean3 _ (𝓡 3) ∞ toTopCat _ charts
instance : CoeSort SmoothVolumeRegion.{u} (Type u) := ⟨fun M => M.toTopCat⟩
instance (M : SmoothVolumeRegion) : TopologicalSpace M := M.toTopCat.str
instance (M : SmoothVolumeRegion) : T2Space M := M.hausdorff
instance (M : SmoothVolumeRegion) : SecondCountableTopology M := M.secondCountable
instance (M : SmoothVolumeRegion) : SigmaCompactSpace M := M.sigmaCompact
instance (M : SmoothVolumeRegion) : Nonempty M := M.nonempty
instance (M : SmoothVolumeRegion) : ChartedSpace Euclidean3 M := M.charts
instance (M : SmoothVolumeRegion) : IsManifold (𝓡 3) ∞ M := M.smooth
instance (M : SmoothVolumeRegion) : MeasurableSpace M := borel M
instance (M : SmoothVolumeRegion) : BorelSpace M := ⟨rfl⟩
local instance : NeZero (Module.finrank ℝ Euclidean3) := ⟨by simp [Euclidean3]⟩
abbrev regionMeasure {M : SmoothVolumeRegion.{u}}
    (g : Riemannian.RiemannianMetric (𝓡 3) M) : Measure M :=
  riemannianMeasure (I := 𝓡 3) g (volume : Measure Euclidean3)
/-- **Math.** A compact cap piece inside an actual smooth model; no volume bound field. -/
structure CompactCapModel where
  space : SmoothVolumeRegion.{u}
  metric : Riemannian.RiemannianMetric (𝓡 3) space
  region : Set space
  compact : IsCompact region
def CompactCapModel.baseVolume (c : CompactCapModel.{u}) : ℝ :=
  (regionMeasure c.metric c.region).toReal
def CompactCapModel.scaledMeasure (c : CompactCapModel.{u}) (r : ℝ) (hr : 0 < r) : Measure c.space :=
  regionMeasure (rescaledMetric c.metric (r^2) (sq_pos_of_pos hr))
def CompactCapModel.scaledVolume (c : CompactCapModel.{u}) (r : ℝ) (hr : 0 < r) : ℝ≥0∞ :=
  c.scaledMeasure r hr c.region
/-- **Math.** Actual volumes of ALL inserted caps scale cubically, including two-cap surgery. -/
def FiniteCapScalingStatement : Prop :=
  ∀ (n : ℕ) (caps : Fin n → CompactCapModel.{u}) (r : ℝ) (hr : 0 < r),
    (∑ i, (caps i).scaledVolume r hr) =
      ENNReal.ofReal (r^3 * ∑ i, (caps i).baseVolume)
def neckRemovedRegion {M : SmoothVolumeRegion.{u}}
    {g : Riemannian.RiemannianMetric (𝓡 3) M} {x : M} {epsilon : ℝ}
    (S : EpsilonNeckStructure epsilon g x) : Set M :=
  S.phi '' {p : epsilonNeckDomain epsilon |
    -(epsilon⁻¹)/2 < p.1.2 0 ∧ p.1.2 0 < -(epsilon⁻¹)/4}
/-- **Math.** The bound concerns actual neck volume, uniform over cap models with total volume ≤ B. -/
def NeckAllowance (B epsilon0 : ℝ) : Prop :=
  ∀ (M : SmoothVolumeRegion.{u}) (g : Riemannian.RiemannianMetric (𝓡 3) M)
    (x : M) (epsilon : ℝ), 0 < epsilon → epsilon < epsilon0 →
    ∀ S : EpsilonNeckStructure epsilon g x,
      ENNReal.ofReal (S.scale^3*(B+1)) ≤ regionMeasure g (neckRemovedRegion S)
def UniformNeckAllowanceStatement : Prop :=
  ∀ B : ℝ, 0 ≤ B → ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ NeckAllowance.{u} B epsilon0
/-- **Math.** Actual measure correspondences for one replacement, not an assumed loss inequality.
The caps partition the inserted region; the old region CONTAINS the measured neck patch. -/
structure NeckReplacementModel (X Y : MeasuredSlice.{u}) (old : Set X) (new : Set Y)
    (B epsilon0 rho : ℝ) where
  space : SmoothVolumeRegion.{u}
  metric : Riemannian.RiemannianMetric (𝓡 3) space
  center : space
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_small : epsilon < epsilon0
  neck : EpsilonNeckStructure epsilon metric center
  scale_lower : rho ≤ neck.scale
  oldPatch : Set X
  oldPatch_subset : oldPatch ⊆ old
  oldMap : space → X
  old_preserves : MeasurePreserving oldMap
    ((regionMeasure metric).restrict (neckRemovedRegion neck)) (X.measure.restrict oldPatch)
  capCount : ℕ
  caps : Fin capCount → CompactCapModel.{u}
  cap_bound : (∑ i, (caps i).baseVolume) ≤ B
  newPieces : Fin capCount → Set Y
  new_measurable : ∀ i, MeasurableSet (newPieces i)
  new_disjoint : Pairwise (Disjoint on newPieces)
  new_cover : (⋃ i, newPieces i) = new
  newMap : ∀ i, (caps i).space → Y
  new_preserves : ∀ i, MeasurePreserving (newMap i)
    (((caps i).scaledMeasure neck.scale
      (epsilonNeck_scale_pos_and_metric_normalization neck).1).restrict (caps i).region)
    (Y.measure.restrict (newPieces i))
theorem neckReplacement_recorded_masses {X Y : MeasuredSlice.{u}}
    {old : Set X} {new : Set Y} {B epsilon0 rho : ℝ}
    (w : NeckReplacementModel X Y old new B epsilon0 rho) :
    regionMeasure w.metric (neckRemovedRegion w.neck) ≤ X.measure old ∧
    Y.measure new = ∑ i, (w.caps i).scaledVolume w.neck.scale
      (epsilonNeck_scale_pos_and_metric_normalization w.neck).1 := by
  constructor
  · have h := w.old_preserves.measure_preimage MeasurableSet.univ.nullMeasurableSet
    have heq : regionMeasure w.metric (neckRemovedRegion w.neck) = X.measure w.oldPatch := by
      simpa using h
    exact heq.le.trans (measure_mono w.oldPatch_subset)
  · calc
      Y.measure new = Y.measure (⋃ i, w.newPieces i) := congrArg Y.measure w.new_cover.symm
      _ = ∑ i, Y.measure (w.newPieces i) := by
        rw [measure_iUnion w.new_disjoint w.new_measurable, tsum_fintype]
      _ = _ := ?_
    apply Finset.sum_congr rfl
    intro i _
    have h := (w.new_preserves i).measure_preimage MeasurableSet.univ.nullMeasurableSet
    simpa [CompactCapModel.scaledVolume] using h.symm
/-- **Math.** Uniform positive LOSS is derived from real neck and all-cap volumes. -/
theorem neckReplacement_local_loss (scaling : FiniteCapScalingStatement.{u})
    {X Y : MeasuredSlice.{u}} {old : Set X} {new : Set Y} {B epsilon0 rho : ℝ}
    (hB : 0 ≤ B) (hrho : 0 < rho) (allowance : NeckAllowance.{u} B epsilon0)
    (w : NeckReplacementModel X Y old new B epsilon0 rho) :
    rho^3 + (Y.measure new).toReal ≤ (X.measure old).toReal := by
  obtain ⟨hold,hnew⟩ := neckReplacement_recorded_masses w
  have hr : 0 < w.neck.scale := (epsilonNeck_scale_pos_and_metric_normalization w.neck).1
  have hsum0 : 0 ≤ ∑ i, (w.caps i).baseVolume :=
    Finset.sum_nonneg (fun i _ => ENNReal.toReal_nonneg)
  have hnewReal : (Y.measure new).toReal = w.neck.scale^3 * ∑ i, (w.caps i).baseVolume := by
    rw [hnew, scaling w.capCount w.caps w.neck.scale hr,
      ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg hr.le 3) hsum0)]
  have hlower := allowance w.space w.metric w.center w.epsilon w.epsilon_pos w.epsilon_small w.neck
  have hlower := hlower.trans hold
  have hreal := ENNReal.toReal_mono (measure_ne_top X.measure old) hlower
  rw [ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg hr.le 3) (by linarith))] at hreal
  have hc : rho^3 ≤ w.neck.scale^3 := pow_le_pow_left₀ hrho.le w.scale_lower 3
  have hcap : w.neck.scale^3 * (∑ i, (w.caps i).baseVolume) ≤ w.neck.scale^3 * B :=
    mul_le_mul_of_nonneg_left w.cap_bound (pow_nonneg hr.le 3)
  rw [hnewReal]
  nlinarith
#print axioms neckReplacement_recorded_masses
#print axioms neckReplacement_local_loss
end PoincareConjecture.ProofContract.Refinement20260927
