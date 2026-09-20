import LeeSmoothLib.Ch01.Sec01_06.Definition_1_6_extra_1
import LeeSmoothLib.Ch05.Sec05_30.Corollary_5_14
import LeeSmoothLib.Ch05.Sec05_30.Theorem_5_12
import LeeSmoothLib.Ch05.Sec05_37.Problem_5_6
import LeeSmoothLib.Ch06.Sec06_44.Corollary_6_31
import LeeSmoothLib.Ch06.Sec06_44.Theorem_6_30
import LeeSmoothLib.Ch06.Sec06_45.Problem_6_10
import LeeSmoothLib.Ch06.Sec06_45.Problem_6_9
import LeeSmoothLib.Ch07.Sec07_49.Proposition_7_16
import LeeSmoothLib.Ch07.Sec07_49.Proposition_7_17
import LeeSmoothLib.Ch07.Sec07_53.Problem_7_19
import LeeSmoothLib.Verified.LevelSets.DiffeomorphTransport
import LeeSmoothLib.Verified.LevelSets.Generic
import LeeSmoothLib.Verified.LevelSets.ModelTransport
import Lean

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``ContMDiffMonoidMorphism.kerEmbeddedData,
    ``ContMDiffMonoidMorphism.kerLieSubgroupStructure,
    ``ContMDiffMonoidMorphism.kerSmoothLieSubgroup,
    ``ContMDiffMonoidMorphism.kerSmoothLieSubgroup_codimension_eq_rank,
    ``ContMDiffMonoidMorphism.kerSmoothLieSubgroup_spec,
    ``LeeSmooth.SeeleyExtension.contDiffOn_closedUpperHalfSpace_exists_open_extension_at,
    ``LeeSmooth.SeeleyExtension.finite_contDiffOn_closedUpperHalfSpace_exists_open_extension_at,
    ``LeeSmooth.SeeleyExtension.seeleyLower_hasFTaylorSeriesUpToOn,
    ``LeeVerifiedLevelSets.DiffeomorphTransport.hasConstantRank_comp_diffeomorphs_iff,
    ``LeeVerifiedLevelSets.DiffeomorphTransport.isRegularValue_comp_diffeomorphs_iff,
    ``LeeVerifiedLevelSets.DiffeomorphTransport.mfderiv_comp_diffeomorphs,
    ``LeeVerifiedLevelSets.DiffeomorphTransport.rankAt_comp_diffeomorphs,
    ``LeeVerifiedLevelSets.DiffeomorphTransport.surjective_mfderiv_comp_diffeomorphs_iff,
    ``LeeVerifiedLevelSets.EmbeddingTransport.image_has_smooth_embedded_structure,
    ``LeeVerifiedLevelSets.Generic.constant_rank_level_set_smooth_structure,
    ``LeeVerifiedLevelSets.Generic.constant_rank_level_set_smooth_structure_of_le,
    ``LeeVerifiedLevelSets.Generic.regular_level_set_smooth_structure,
    ``LeeVerifiedLevelSets.InjectiveRank.rank_eq_source_finrank_of_injective,
    ``LeeVerifiedLevelSets.ModelTransport.chartedSpaceCongr_isManifold,
    ``LeeVerifiedLevelSets.ModelTransport.contMDiff_euclideanRechart_mk,
    ``LeeVerifiedLevelSets.ModelTransport.contMDiff_euclideanRechart_val,
    ``LeeVerifiedLevelSets.ModelTransport.contMDiff_rechartMap,
    ``LeeVerifiedLevelSets.ModelTransport.euclideanChartedSpace_isManifold,
    ``LeeVerifiedLevelSets.ModelTransport.euclideanRechartDiffeomorph,
    ``LeeVerifiedLevelSets.ModelTransport.euclideanRechart_isManifold,
    ``LeeVerifiedLevelSets.ModelTransport.hasConstantRank_rechartMap,
    ``LeeVerifiedLevelSets.ModelTransport.isRegularValue_rechartMap,
    ``boundary_halfSpace_image_exists_local_ambient_extension,
    ``constant_rank_level_set_has_embedded_submanifold_structure,
    ``constant_rank_level_set_isProperlyEmbedded,
    ``contDiffOn_range_halfSpace_exists_open_extension_at,
    ``contDiffOn_range_halfSpace_exists_open_extension_at_finite,
    ``contMDiffOn_halfSpace_iff_forall_exists_smoothAmbientExtension,
    ``forall_exists_smoothAmbientExtension_of_contDiffOn_halfSpace_image,
    ``injectiveLieGroupHomIsImmersion,
    ``injective_lie_group_hom_range_has_lie_subgroup_structure,
    ``lie_group_isomorphic_to_semidirect_product_iff_exists_split_lie_homs,
    ``positiveSphere_isEmbeddedSubmanifold,
    ``problem_6_9_preimage_is_embedded_submanifold,
    ``problem_6_9_scalarRegularLevel_isEmbeddedCurve,
    ``problem_6_9_transverse_to_sphere_iff,
    ``problem_6_9_transverse_to_sphere_iff_regularValue,
    ``rankAtOne_eq_sourceFinrank_of_injectiveLieGroupHom,
    ``regular_level_set_has_embedded_submanifold_structure,
    ``regular_level_set_isProperlyEmbedded,
    ``smooth_submersion_preimage_has_embedded_submanifold_structure,
    ``tangentSpace_inter_eq_inf_of_transverse,
    ``tangentSpace_preimage_eq_comap_of_transverse,
    ``transportEmbeddedSubmanifoldR1ToReal,
    ``transverse_codimension_le_source_finrank,
    ``transverse_intersection_has_embedded_submanifold_structure,
    ``transverse_preimage_has_embedded_submanifold_structure,
    ``unitTangentBundle_exists_isSmoothEmbedding]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Nonstandard axioms in {name}: {bad}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"CONTINUATION_VERIFIED_CORE_GUARD_PASS {names.size}"
