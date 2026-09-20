import LeeSmoothLib.Ch07.Sec07_50.Proposition_7_26
import LeeSmoothLib.Ch07.Sec07_50.Remark_7_50_extra_5
import Lean

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``StabilizerSmoothFiber.stabilizer_has_smooth_embedded_structure,
    ``stabilizer_has_embeddedSubmanifold_data,
    ``stabilizerEmbeddedData_fromCurrentSection,
    ``stabilizerSmoothLieSubgroup,
    ``stabilizerSmoothLieSubgroup_isProperlyEmbedded,
    ``orbitMap_isImmersion_of_stabilizer_eq_bot,
    ``stabilizerEmbeddedData,
    ``stabilizerEmbeddedClosedData,
    ``stabilizerQuotientManifoldBridge,
    ``orbit_is_immersed_submanifold]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Nonstandard axioms: {name}: {bad}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"STABILIZER_ORBIT_GUARD_PASS {names.size}"
