import LeeSmoothLib.Ch04.Sec04_21.ImmersionModelObstruction
import LeeSmoothLib.Ch04.Sec04_23.Theorem_4_12
import LeeSmoothLib.Ch04.Sec04_26.Corollary_4_43
import LeeSmoothLib.Ch04.Sec04_26.Exercise_4_45
import LeeSmoothLib.Ch04.Sec04_27.Problem_4_13
import LeeSmoothLib.Ch05.Sec05_29.Example_5_9
import LeeSmoothLib.Ch05.Sec05_29.Remark_5_29_extra_2
import LeeSmoothLib.Ch05.Sec05_33.Theorem_5_33
import LeeSmoothLib.Ch05.Sec05_36.Proposition_5_49
import LeeSmoothLib.Ch05.Sec05_36.Theorem_5_51
import LeeSmoothLib.Ch04.Sec04_21.Example_4_2
import Lean

-- Audit accepted endpoints, not merely the number of textual placeholders.
open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[
    ``ImmersionModelObstruction.zero_mem_interior_range_of_immersion,
    ``ImmersionModelObstruction.not_immersion_of_zero_notMem_interior_range,
    ``rank_normal_form_apply_of_lt,
    ``LocalCoordinateNormalFormAt.mapsTo_source,
    ``constant_rank_local_coordinate_normal_form,
    ``smooth_submersion_local_projection_form,
    ``smooth_immersion_local_inclusion_form,
    ``unitSphere_subtype_val_isImmersion,
    ``local_slice_condition_unique_submanifold_structure,
    ``Manifold.SweepRestriction.isImmersion_comp_subtype,
    ``smooth_embedding_range_has_manifold_with_boundary,
    ``immersed_submanifold_has_embedded_neighborhood,
    ``exists_universal_smooth_covering_manifold,
    ``exists_universal_smooth_covering_manifold_with_boundary,
    ``sphere_to_realProjectiveSpace_isSmoothCoveringMap,
    ``real_projective_plane_exists_isSmoothEmbedding_to_R4,
    ``Manifold.is_immersion_iff_forall_injective_mfderiv,
    ``torus_revolution_map_isImmersion,
    ``immersed_submanifold_structure_unique_of_same_carrier,
    ``weakly_embedded_submanifold_structure_unique,
    ``smooth_embedding_subtype_val_has_local_slice_at_of_isInteriorPoint,
    ``smooth_embedding_subtype_val_has_local_half_slice_at_of_isBoundaryPoint,
    ``satisfiesLocalSliceConditionWithBoundary_has_manifold_with_boundary_structure,
    ``smooth_embedding_subtype_val_satisfiesLocalSliceConditionWithBoundary,
    ``local_slice_criterion_for_embedded_submanifold_with_boundary]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in targets do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Unaccepted axioms for {name}: {bad}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"GROK_PRIORITY_AXIOM_GUARD_PASS {targets.size}"
