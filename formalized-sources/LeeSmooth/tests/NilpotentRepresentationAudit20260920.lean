import LeeSmoothLib.Ch08.Sec08_62.NilpotentFaithfulRepresentation
import Lean

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``LeeNilpotentPBWWeightedBridge.highWeightOrderedRewrite,
    ``LeeNilpotentPBWWeightedBridge.realPBW_hasOrderedPBWBasis,
    ``LeeNilpotentPBWWeightedBridge.finiteDimensional_nilpotentWeightedQuotient,
    ``LeeNilpotentPBWWeightedBridge.iota_not_mem_nilpotentWeightedLeftIdeal_of_PBW,
    ``LeeNilpotentPBWWeightedBridge.existsFaithfulFiniteDimensional_of_nilpotent_of_PBW,
    ``LeeNilpotentPBWWeightedBridge.existsFaithfulFiniteDimensionalNilpotentRepresentation]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    unless (axioms.filter (fun a ↦ !allowed.contains a)).isEmpty do
      throwError "Unexpected axioms for {name}: {axioms}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"NILPOTENT_REPRESENTATION_GUARD_PASS {names.size}"

#check LeeNilpotentPBWWeightedBridge.existsFaithfulFiniteDimensionalNilpotentRepresentation
