import PoincareConjecture.ProofContract.Refinement20260927.FiniteSmoothingAtlas
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh1
import MorganTianLib.Ch04.ScalarMinimumBounds
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set Riemannian MorganTianLib
open scoped Topology Manifold ContDiff
local instance : NeZero (Module.finrank ℝ Euclidean3) := ⟨by simp [Euclidean3]⟩
/-- Reuses the actual partition-of-unity construction, on the original atlas. -/
theorem global_initial_metric (M : ClosedThreeManifold.{u}) [IsSmooth M] :
    Nonempty (Riemannian.RiemannianMetric (𝓡 3) M) := Riemannian.exists_riemannianMetric
/-- A genuine scalar lower bound for one global metric, not coordinate normalization. -/
theorem global_initial_scalar_bound (M : ClosedThreeManifold.{u}) [IsSmooth M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : M,
      -C ≤ scalarCurvatureAt g g.leviCivitaConnection (canonicalLeviCivita_isLeviCivita g) p := by
  refine ⟨max 0 (-scalarCurvatureMinimum g), le_max_left _ _, ?_⟩
  intro p
  have hmin := scalarCurvatureMinimum_le_scalarCurvatureAt g
    (canonicalLeviCivita_isLeviCivita g) p
  have hmax := le_max_right (0 : ℝ) (-scalarCurvatureMinimum g)
  linarith
/-- Complete actual input data for scalar/volume estimates; no flow or sphere conclusion. -/
structure MetricInitialData (M : ClosedThreeManifold.{u}) [IsSmooth M] where
  metric : Riemannian.RiemannianMetric (𝓡 3) M
  scalarConstant : ℝ
  scalarConstant_nonneg : 0 ≤ scalarConstant
  scalar_lower : ∀ p : M, -scalarConstant ≤ scalarCurvatureAt metric
    metric.leviCivitaConnection (canonicalLeviCivita_isLeviCivita metric) p
theorem metric_initialData_exists (M : ClosedThreeManifold.{u}) [IsSmooth M] :
    Nonempty (MetricInitialData M) := by
  obtain ⟨g⟩ := global_initial_metric M
  obtain ⟨C,hC,hscalar⟩ := global_initial_scalar_bound M g
  exact ⟨⟨g,C,hC,hscalar⟩⟩
#print axioms global_initial_metric
#print axioms global_initial_scalar_bound
#print axioms metric_initialData_exists
end PoincareConjecture.ProofContract.Refinement20260927
