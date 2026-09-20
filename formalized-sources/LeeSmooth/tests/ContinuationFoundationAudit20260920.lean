import LeeSmoothLib.Verified.LevelSets.AnalyticRegularValue
import LeeSmoothLib.Ch01.Sec01_06.SeeleyMoments
import Lean

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[``LeeVerifiedAnalyticLevelSets.analytic_regular_level_set_has_embedded_submanifold_structure,
    ``LeeVerifiedAnalyticLevelSets.euclidean_analytic_regular_level_set_has_embedded_submanifold_structure,
    ``LeeVerifiedAnalyticLevelSets.euclideanChartedSpaceSelf_isManifold,
    ``LeeVerifiedAnalyticLevelSets.euclidean_analytic_regular_level_set_isProperlyEmbedded,
    ``LeeVerifiedAnalyticLevelSets.analytic_regular_level_set_isProperlyEmbedded,
    ``LeeSmooth.SeeleyExtension.summable_abs_seeleyCoeff_mul_pow,
    ``LeeSmooth.SeeleyExtension.tsum_seeleyCoeff_mul_seeleyNode_pow,
    ``LeeSmooth.SeeleyExtension.seeley_weighted_multilinear_tsum]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in targets do
    unless (← getEnv).contains n do throwError "Missing declaration: {n}"
    let axs ← Lean.collectAxioms n
    let bad := axs.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Nonstandard axioms for {n}: {bad}"
    logInfo m!"PASS {n}: {axs}"
  logInfo m!"CONTINUATION_FOUNDATION_GUARD_PASS {targets.size}"
