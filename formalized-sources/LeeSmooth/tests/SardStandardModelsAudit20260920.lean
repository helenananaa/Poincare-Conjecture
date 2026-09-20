import LeeSmoothLib.Ch06.Sec06_39.SardStandardModels
import LeeSmoothLib.Ch06.Sec06_39.Theorem_6_10
import Lean

-- The legacy chapter module is deliberately imported as a compatibility check.
-- Only the selected new endpoints are required to have the standard axiom set.
open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[
    ``SardStandardModels.ambientCriticalImage_measureZero_of_localAmbientExtension,
    ``SardStandardModels.finiteDimensionalSelfModel_criticalImage_measureZero,
    ``SardStandardModels.halfSpace_criticalImage_measureZero,
    ``SardStandardModels.criticalValues_has_measure_zero_in_manifold_of_contMDiff_selfModel]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in targets do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Unaccepted axioms for {name}: {bad}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"SARD_STANDARD_MODELS_GUARD_PASS {targets.size}"

#check SardStandardModels.halfSpace_criticalImage_measureZero
#check SardStandardModels.criticalValues_has_measure_zero_in_manifold_of_contMDiff_selfModel
