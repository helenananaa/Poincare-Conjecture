import LeeSmoothLib.Ch05.Sec05_35.Exercise_5_40
import LeeSmoothLib.Ch05.Sec05_37.Problem_5_7
import Lean

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[
    ``tangentSpace_eq_ker_mfderiv_of_level_set_of_hasConstantRank,
    ``exists_local_defining_map_on_nhds_to_fin_of_level_set_of_has_constant_rank,
    ``problem_5_7_regularDomain_scalar_isSmoothSubmersion,
    ``problem_5_7_zero_branch_witnesses_in_ball,
    ``problem_5_7_preconnected_zero_fiber_no_mixed_x_sign,
    ``problem_5_7_preconnected_zero_fiber_no_mixed_y_sign,
    ``problem_5_7_regular_level_embedded_submanifold_r1,
    ``problem_5_7_levelSet_is_embedded_submanifold_iff]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in targets do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Unaccepted axioms for {name}: {bad}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"TANGENT_FIBER_AXIOM_GUARD_PASS {targets.size}"
