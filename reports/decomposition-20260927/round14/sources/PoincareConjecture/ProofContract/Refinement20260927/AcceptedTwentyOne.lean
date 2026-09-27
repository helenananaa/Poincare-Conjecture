import PoincareConjecture.ProofContract.Refinement20260927.EnergyContinuityRoot
import PoincareConjecture.ParallelImplementation.RefinedUniformNearMaxTaylor
import PoincareConjecture.ParallelImplementation.RefinedMinimaxDiniLimit
import PoincareConjecture.ParallelImplementation.RefinedCompactQuadraticLower
import PoincareConjecture.ParallelImplementation.RefinedCompactMetricTimeVariation
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1
 theorem checked_near_max : UniformNearMaxTaylorStatement :=
  ParallelImplementation.RefinedUniformNearMaxTaylor.uniform_near_max_taylor
 theorem checked_minimax_limit : MinimaxDiniLimitStatement :=
  ParallelImplementation.RefinedMinimaxDiniLimit.minimax_dini_limit
 theorem checked_compact_coercivity : CompactQuadraticLowerStatement.{u} :=
  ParallelImplementation.RefinedCompactQuadraticLower.compact_quadratic_lower
 theorem checked_compact_time_variation : CompactMetricTimeVariationStatement.{u} :=
  ParallelImplementation.RefinedCompactMetricTimeVariation.compact_metric_time_variation
/-- **Math.** All four returned leaves are used here; three large producers remain. -/
theorem public_after_twenty_one (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u})
    (geometry : EnergyControlledGeometryProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  public_of_energy_continuity_frontier triangulate atlas checked_near_max checked_minimax_limit
    checked_compact_coercivity checked_compact_time_variation geometry
#print axioms checked_near_max
#print axioms checked_minimax_limit
#print axioms checked_compact_coercivity
#print axioms checked_compact_time_variation
#print axioms public_after_twenty_one
end PoincareConjecture.ProofContract.Refinement20260927
