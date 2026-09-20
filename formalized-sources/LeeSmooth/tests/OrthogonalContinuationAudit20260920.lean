import LeeSmoothLib.Ch08.Sec08_62.Example_8_47
import LeeSmoothLib.Verified.LevelSets.EmptyFiberDimension
import Lean

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[``orthogonal_group_lie_isomorphic_to_so,
    ``orthogonal_group_lie_isomorphic_to_so_apply,
    ``orthogonal_groupLieSubalgebra_eq_so,
    ``orthogonal_groupLieSubalgebra_mem_iff_transpose_add_eq_zero,
    ``ker_orthogonalLevelMapOneDeriv_eq_so,
    ``orthogonalSubgroupInGeneralLinearGroup_has_lieSubgroup_structure,
    ``LeeLevelSetEmptyFiber.regular_value_does_not_force_dimension_bound,
    ``LeeLevelSetEmptyFiber.empty_embedded_codimension_zero]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in targets do
    unless (← getEnv).contains n do throwError "Missing declaration: {n}"
    let axs ← Lean.collectAxioms n
    let bad := axs.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Nonstandard axioms for {n}: {bad}"
    logInfo m!"PASS {n}: {axs}"
  logInfo m!"ORTHOGONAL_EMPTY_FIBER_GUARD_PASS {targets.size}"
