import Lean
import LeeSmoothLib.Ch01.Sec01_06.SeeleyMoments
import LeeSmoothLib.Ch01.Sec01_06.WithinTaylorSums
import LeeSmoothLib.Ch04.Sec04_21.Example_4_2
import LeeSmoothLib.Ch04.Sec04_21.ImmersionModelObstruction
import LeeSmoothLib.Ch04.Sec04_21.Proposition_4_1
import LeeSmoothLib.Ch04.Sec04_22.Proposition_4_6
import LeeSmoothLib.Ch04.Sec04_23.Theorem_4_12
import LeeSmoothLib.Ch04.Sec04_26.Corollary_4_43
import LeeSmoothLib.Ch04.Sec04_26.Exercise_4_45
import LeeSmoothLib.Ch04.Sec04_27.Problem_4_13
import LeeSmoothLib.Ch05.Sec05_28.Proposition_5_3
import LeeSmoothLib.Ch05.Sec05_29.Example_5_9
import LeeSmoothLib.Ch05.Sec05_29.Remark_5_29_extra_2
import LeeSmoothLib.Ch05.Sec05_33.Theorem_5_33
import LeeSmoothLib.Ch05.Sec05_35.Exercise_5_40
import LeeSmoothLib.Ch05.Sec05_35.Proposition_5_38
import LeeSmoothLib.Ch05.Sec05_36.Proposition_5_49
import LeeSmoothLib.Ch05.Sec05_36.Theorem_5_51
import LeeSmoothLib.Ch05.Sec05_37.Problem_5_7
import LeeSmoothLib.Ch05.Sec05_37.Problem_5_8
import LeeSmoothLib.Ch08.Sec08_62.Example_8_47
import LeeSmoothLib.Verified.LevelSets.AnalyticRegularValue
import LeeSmoothLib.Verified.LevelSets.EmptyFiberDimension

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[``ImmersionModelObstruction.not_immersion_of_zero_notMem_interior_range,
    ``ImmersionModelObstruction.zero_mem_interior_range_of_immersion,
    ``LeeLevelSetEmptyFiber.empty_embedded_codimension_zero,
    ``LeeLevelSetEmptyFiber.model_finrank_le_of_nonempty_regular_fiber,
    ``LeeLevelSetEmptyFiber.no_codimension_one_bundle_for_avoidsZero,
    ``LeeLevelSetEmptyFiber.regular_value_does_not_force_dimension_bound,
    ``LeeSmooth.SeeleyExtension.seeley_weighted_multilinear_tsum,
    ``LeeSmooth.SeeleyExtension.summable_abs_seeleyCoeff_mul_pow,
    ``LeeSmooth.SeeleyExtension.tsum_seeleyCoeff_mul_seeleyNode_pow,
    ``LeeSmooth.WithinTaylorSums.continuousOn_tsum_taylorCoeff,
    ``LeeSmooth.WithinTaylorSums.hasFDerivWithinAt_tsum,
    ``LeeSmooth.WithinTaylorSums.hasFTaylorSeriesUpToOn_tsum,
    ``LeeSmooth.WithinTaylorSums.iteratedFDerivWithin_tsum,
    ``LeeSmooth.WithinTaylorSums.iteratedFDerivWithin_tsum_of_interior,
    ``LeeSmooth.WithinTaylorSums.summable_taylorCoeff,
    ``LeeSmooth.WithinTaylorSums.tendstoUniformlyOn_tsum_taylorCoeff,
    ``LeeSmooth.WithinTaylorSums.tsum_curry0_of_hasFTaylorSeriesUpToOn,
    ``LeeSmooth.WithinTaylorSums.tsum_curryLeft_taylorCoeff,
    ``LeeSmooth.WithinTaylorSums.tsum_taylorCoeff_eqOn,
    ``LeeVerifiedAnalyticLevelSets.analytic_regular_level_set_has_embedded_submanifold_structure,
    ``LeeVerifiedAnalyticLevelSets.analytic_regular_level_set_isProperlyEmbedded,
    ``LeeVerifiedAnalyticLevelSets.euclideanChartedSpaceSelf_isManifold,
    ``LeeVerifiedAnalyticLevelSets.euclidean_analytic_regular_level_set_has_embedded_submanifold_structure,
    ``LeeVerifiedAnalyticLevelSets.euclidean_analytic_regular_level_set_isProperlyEmbedded,
    ``LocalCoordinateNormalFormAt.mapsTo_source,
    ``Manifold.SweepRestriction.isImmersion_comp_subtype,
    ``Manifold.exists_open_restriction_isImmersion_of_injective_mfderiv,
    ``Manifold.exists_open_restriction_isSmoothSubmersion_of_surjective_mfderiv,
    ``Manifold.is_immersion_iff_forall_injective_mfderiv,
    ``ball_exterior_boundary_slice_chart_in_basis_model,
    ``constant_rank_local_coordinate_normal_form,
    ``euclidean_exterior_ball_has_boundary_slice_chart_at_sphere_point,
    ``exists_local_defining_map_on_nhds_to_fin_of_level_set_of_has_constant_rank,
    ``exists_universal_smooth_covering_manifold,
    ``exists_universal_smooth_covering_manifold_with_boundary,
    ``immersed_submanifold_has_embedded_neighborhood,
    ``immersed_submanifold_structure_unique_of_same_carrier,
    ``isLocalDiffeomorph_comp,
    ``isLocalDiffeomorph_iff_writtenInExtChartAt,
    ``isLocalDiffeomorph_pi,
    ``ker_orthogonalLevelMapOneDeriv_eq_so,
    ``local_slice_condition_unique_submanifold_structure,
    ``local_slice_criterion_for_embedded_submanifold_with_boundary,
    ``orthogonalSubgroupInGeneralLinearGroup_has_lieSubgroup_structure,
    ``orthogonal_groupLieSubalgebra_eq_so,
    ``orthogonal_groupLieSubalgebra_mem_iff_transpose_add_eq_zero,
    ``orthogonal_group_lie_isomorphic_to_so,
    ``orthogonal_group_lie_isomorphic_to_so_apply,
    ``problem_5_7_levelSet_is_embedded_submanifold_iff,
    ``problem_5_7_preconnected_zero_fiber_no_mixed_x_sign,
    ``problem_5_7_preconnected_zero_fiber_no_mixed_y_sign,
    ``problem_5_7_regularDomain_scalar_isSmoothSubmersion,
    ``problem_5_7_regular_level_embedded_submanifold_r1,
    ``problem_5_7_zero_branch_witnesses_in_ball,
    ``productSliceMap_isSmoothEmbedding,
    ``product_slice_has_induced_manifold_structure,
    ``range_productSliceMap_eq_univ_prod_singleton,
    ``rank_normal_form_apply_of_lt,
    ``real_projective_plane_exists_isSmoothEmbedding_to_R4,
    ``regularCoordinateBall_compl_boundary_diffeomorph_sphere,
    ``regularCoordinateBall_compl_exists_smoothManifoldWithBoundary,
    ``regular_coordinate_ball_frontier_has_boundary_sliceChart_for_compl,
    ``regular_coordinate_ball_frontier_has_boundary_sliceChart_for_compl_of_pos,
    ``regular_coordinate_ball_frontier_homeomorph_to_boundarySphere,
    ``satisfiesLocalSliceConditionWithBoundary_has_manifold_with_boundary_structure,
    ``smooth_embedding_range_has_manifold_with_boundary,
    ``smooth_embedding_subtype_val_has_local_half_slice_at_of_isBoundaryPoint,
    ``smooth_embedding_subtype_val_has_local_slice_at_of_isInteriorPoint,
    ``smooth_embedding_subtype_val_satisfiesLocalSliceConditionWithBoundary,
    ``smooth_immersion_local_inclusion_form,
    ``smooth_submersion_local_projection_form,
    ``sphere_to_realProjectiveSpace_isSmoothCoveringMap,
    ``tangentSpace_eq_ker_mfderiv_of_isLocalDefiningMapOn,
    ``tangentSpace_eq_ker_mfderiv_of_level_set_of_hasConstantRank,
    ``torus_revolution_map_isImmersion,
    ``unitSphere_subtype_val_isImmersion,
    ``unit_exterior_signed_shell_boundary_slice_chart_at_sphere_point_succSucc,
    ``weakly_embedded_submanifold_structure_unique]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in targets do
    unless (← getEnv).contains n do throwError "Missing declaration: {n}"
    let axs ← Lean.collectAxioms n
    let bad := axs.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Nonstandard axioms for {n}: {bad}"
    logInfo m!"PASS {n}: {axs}"
  logInfo m!"COMBINED_CONTINUATION_GUARD_PASS {targets.size}"
