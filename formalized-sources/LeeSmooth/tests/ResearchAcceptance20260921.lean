import LeeSmoothLib.Ch08.Sec08_62.NilpotentDerivationStableRepresentation
import LeeSmoothLib.Ch05.Sec05_36.Theorem_5_48
import Lean
open Lean Elab Command in
run_cmd do
  let names : Array Name := #[``LeeNilpotentDerivationStableRepresentation.existsFaithfulFiniteDimensionalNilpotentRepresentationWithDerivations, ``exists_definingFunction_of_isRegularDomain, ``exists_exhaustion_definingFunction_of_isCompact_regularDomain]
  for n in names do
    unless (← getEnv).contains n do throwError "Missing target: {n}"
    let a ← Lean.collectAxioms n
    unless (a.filter (fun x ↦ !(#[``propext, ``Classical.choice, ``Quot.sound]).contains x)).isEmpty do
      throwError "Unaccepted axioms: {n}: {a}"
    logInfo m!"PASS {n}: {a}"
  logInfo m!"RESEARCH_ACCEPTANCE_20260921_PASS {names.size}"
