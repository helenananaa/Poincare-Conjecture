import LeeSmoothLib.Ch05.Sec05_37.Problem_5_8
import Lean

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[
    ``unit_exterior_signed_shell_boundary_slice_chart_at_sphere_point_succSucc,
    ``euclidean_exterior_ball_has_boundary_slice_chart_at_sphere_point,
    ``ball_exterior_boundary_slice_chart_in_basis_model,
    ``regular_coordinate_ball_frontier_has_boundary_sliceChart_for_compl_of_pos,
    ``regular_coordinate_ball_frontier_has_boundary_sliceChart_for_compl,
    ``regular_coordinate_ball_frontier_homeomorph_to_boundarySphere,
    ``regularCoordinateBall_compl_exists_smoothManifoldWithBoundary,
    ``regularCoordinateBall_compl_boundary_diffeomorph_sphere]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in targets do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Unaccepted axioms for {name}: {bad}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"EXTERIOR_BALL_AXIOM_GUARD_PASS {targets.size}"
