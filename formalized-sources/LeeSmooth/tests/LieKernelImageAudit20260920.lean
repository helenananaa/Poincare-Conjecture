import LeeSmoothLib.Ch07.Sec07_49.Proposition_7_16
import LeeSmoothLib.Ch07.Sec07_49.Proposition_7_17
import LeeSmoothLib.Ch07.Sec07_53.Problem_7_19
import Lean

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``LeeVerifiedLevelSets.InjectiveRank.rank_eq_source_finrank_of_injective,
    ``ContMDiffMonoidMorphism.kerEmbeddedData,
    ``ContMDiffMonoidMorphism.kerLieSubgroupStructure,
    ``ContMDiffMonoidMorphism.kerSmoothLieSubgroup,
    ``ContMDiffMonoidMorphism.kerSmoothLieSubgroup_spec,
    ``ContMDiffMonoidMorphism.kerSmoothLieSubgroup_codimension_eq_rank,
    ``rankAtOne_eq_sourceFinrank_of_injectiveLieGroupHom,
    ``injectiveLieGroupHomIsImmersion,
    ``injective_lie_group_hom_range_has_lie_subgroup_structure,
    ``lie_group_isomorphic_to_semidirect_product_iff_exists_split_lie_homs]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Nonstandard axioms: {name}: {bad}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"LIE_KERNEL_IMAGE_GUARD_PASS {names.size}"
