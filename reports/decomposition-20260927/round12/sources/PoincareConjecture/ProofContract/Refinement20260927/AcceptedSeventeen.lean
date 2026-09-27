import PoincareConjecture.ProofContract.Refinement20260927.WidthExtinctionRoot
import PoincareConjecture.ParallelImplementation.RefinedLocalPatchDensity
import PoincareConjecture.ParallelImplementation.RefinedOpenPatchAssembly
import PoincareConjecture.ParallelImplementation.RefinedWidthDiniComparison
import PoincareConjecture.ParallelImplementation.RefinedWidthFiniteHorizon
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
/-- **Math.** Bind the four exact independently recompiled fixed targets. -/
theorem checked_local_patch_density : LocalPatchDensityStatement.{u} :=
  ParallelImplementation.RefinedLocalPatchDensity.local_patch_density
theorem checked_open_patch_assembly : OpenPatchAssemblyStatement.{u} :=
  ParallelImplementation.RefinedOpenPatchAssembly.open_patch_assembly
theorem checked_width_comparison : WidthIntervalComparisonStatement :=
  ParallelImplementation.RefinedWidthDiniComparison.width_dini_comparison
theorem checked_width_horizon : WidthHorizonStatement :=
  ParallelImplementation.RefinedWidthFiniteHorizon.width_finite_horizon
/-- **Math.** Extinction still needs a genuine surviving profile; its scalar
comparison is no longer a pending parameter. -/
theorem checked_empty_end {M : ClosedThreeManifold.{u}}
    (H : LocatedProjection checked_epsilon_neck_embedding.{u} M) (finite : H.events.Finite)
    {a c w0 : ℝ} (ha : 0 < a) (hc : 0 < c)
    (late : widthPotential a c 0 w0 < 4*a*(H.horizon+c)^((1:ℝ)/4))
    (realize : H.pre H.horizon ≠ [] → Nonempty (ExtinctionProfile a c w0 H.horizon H.events)) :
    H.pre H.horizon = [] := empty_end_of_width_comparison checked_width_comparison H finite ha hc late realize
/-- **Math.** Seventeen local leaves are consumed. Three major research inputs
remain; no unconditional Poincare claim. -/
theorem public_after_seventeen (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u})
    (geometry : WidthControlledGeometryProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  public_of_width_frontier triangulate atlas checked_local_patch_density
    checked_open_patch_assembly checked_width_comparison checked_width_horizon geometry
#print axioms checked_local_patch_density
#print axioms checked_open_patch_assembly
#print axioms checked_width_comparison
#print axioms checked_width_horizon
#print axioms checked_empty_end
#print axioms public_after_seventeen
end PoincareConjecture.ProofContract.Refinement20260927
