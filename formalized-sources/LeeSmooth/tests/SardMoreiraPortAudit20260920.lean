import LeeSmoothLib.External.SardMoreira.MainTheorem
import Lean
open Lean Elab Command in
run_cmd do
  let names : Array Name := #[``hausdorffMeasure_sardMoreiraBound_image_null_of_finrank_le, ``dimH_image_le_sardMoreiraBound_of_finrank_le, ``addHaar_image_critical_eq_zero, ``addHaar_image_critical_eq_zero_of_contDiff, ``addHaar_image_critical_eq_zero_of_contDiffOn]
  for n in names do
    unless (← getEnv).contains n do throwError "Missing target: {n}"
    let a ← Lean.collectAxioms n
    unless (a.filter (fun x ↦ !(#[``propext, ``Classical.choice, ``Quot.sound]).contains x)).isEmpty do
      throwError "Unaccepted axioms: {n}: {a}"
    logInfo m!"PASS {n}: {a}"
  logInfo m!"SARD_PORT_GUARD_PASS {names.size}"
