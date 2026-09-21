import MorganTianLib.Ch02.SurgeryCap.WarpedProduct

open Riemannian
open scoped Manifold ContDiff
noncomputable section
namespace MorganTianLib.SurgeryCap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {N : Type*} [TopologicalSpace N]
  [ChartedSpace H N] [IsManifold I ∞ N] [SigmaCompactSpace N] [T2Space N]

/-- **Math.** The canonical Levi-Civita connection of the constructed warped metric. -/
def warpedConnection (g : RiemannianMetric I N) (w : ℝ → ℝ)
    (hw : ContDiff ℝ ∞ w) (hwpos : ∀ r, 0 < r → 0 < w r) :
    AffineConnection (I.prod 𝓘(ℝ, ℝ)) (N × ↥positiveReal) :=
  leviCivitaConnectionGeneral (warpedMetric g w hw hwpos)

/-- **Math.** The constructed connection is torsion-free and metric-compatible. -/
theorem warpedConnection_isLeviCivita (g : RiemannianMetric I N) (w : ℝ → ℝ)
    (hw : ContDiff ℝ ∞ w) (hwpos : ∀ r, 0 < r → 0 < w r) :
    (warpedConnection g w hw hwpos).IsLeviCivita (warpedMetric g w hw hwpos) :=
  leviCivitaConnectionGeneral_isLeviCivita (warpedMetric g w hw hwpos)

end MorganTianLib.SurgeryCap
