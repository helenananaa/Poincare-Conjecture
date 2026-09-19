import PoincareConjecture.ParallelMath.Transfer.Core
import ReferenceBridges.Quantitative.EpsilonSpeedComparison
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.MetricBridge
import Mathlib.Geometry.Manifold.Riemannian.PathELength
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set MeasureTheory Riemannian Manifold
open scoped Topology Manifold ContDiff ENNReal Bundle
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
/-- **Math.** The original manifold path-length primitive with the chosen metric bundle installed explicitly. -/
def metricPathLength (g : RiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) : ℝ≥0∞ :=
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  Manifold.pathELength I γ a b
/-- **Math.** The original manifold Riemannian extended distance, keeping the pre-existing topology and charts. -/
def metricEDist (g : RiemannianMetric I M) (x y : M) : ℝ≥0∞ :=
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  Manifold.riemannianEDist I x y
/-- **Math.** Genuine C1 joining curves on the standard unit time interval. -/
abbrev JoiningCurve (I : ModelWithCorners ℝ E H) (x y : M) :=
  {γ : ℝ → M // γ 0 = x ∧ γ 1 = y ∧ ContMDiffOn 𝓘(ℝ,ℝ) I 1 γ (Icc 0 1)}
/-- **Math.** The same metric tensor as an algebraic bilinear form, with no change to values or topology. -/
def metricForm (g : RiemannianMetric I M) (p : M) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => g.metricInner p v w)
    (fun v w z => g.metricInner_add_left p v w z)
    (fun c v w => g.metricInner_smul_left p c v w)
    (fun v w z => g.metricInner_add_right p v w z)
    (fun c v w => g.metricInner_smul_right p c v w)
/-- **Math.** Actual differential Gram area density of a parametrized surface. -/
def paramAreaDensity (g : RiemannianMetric I M)
    (F : EuclideanSpace ℝ (Fin 2) → M) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  gramArea (metricForm g (F x))
    (mfderiv (𝓡 2) I F x (EuclideanSpace.single 0 1))
    (mfderiv (𝓡 2) I F x (EuclideanSpace.single 1 1))
end PoincareConjecture.ParallelMath.Transfer
