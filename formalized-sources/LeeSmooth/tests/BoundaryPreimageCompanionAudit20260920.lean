import LeeSmoothLib.Ch05.Sec05_37.RegularPreimageWithBoundaryCorrected
import Lean

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[
    ``Manifold.regular_preimage_has_cInfinity_halfspace_structure_with_boundary,
    ``Manifold.InteriorRegularPreimageChart.exists_interiorEuclideanStraightening,
    ``Manifold.BoundaryPreimageCharts.interiorChartTarget_subset,
    ``Manifold.BoundaryRegularPreimageChart.exists_boundary_cInfinityNeatSliceChart,
    ``Manifold.CInfinityNeatSliceFamily.exists_structure_of_neatSliceFamily]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in targets do
    unless (← getEnv).contains name do throwError "Missing target {name}"
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter (fun a ↦ !allowed.contains a)
    unless unexpected.isEmpty do throwError "Unexpected axioms for {name}: {unexpected}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"BOUNDARY_PREIMAGE_COMPANION_GUARD_PASS {targets.size}"
