import MorganTianLib.Ch03.RicciFlow.CompactVolumeScalarLower
import Lean

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[``MorganTianLib.riemannianMeasure_pos_of_nonempty_isOpen, ``MorganTianLib.riemannianMeasure_isLocallyFinite, ``MorganTianLib.riemannianMeasure_lt_top_of_isCompact, ``MorganTianLib.compact_real_volume_upper_of_scalar_lower]
  for n in names do
    unless (← getEnv).contains n do throwError "Missing declaration: {n}"
    let a ← Lean.collectAxioms n
    unless (a.filter (fun x ↦ !(#[``propext, ``Classical.choice, ``Quot.sound]).contains x)).isEmpty do
      throwError "Unapproved axioms {n}: {a}"
    logInfo m!"PASS {n}: {a}"
  logInfo "MEASURE_AND_COMPACT_VOLUME_GUARD_PASS 4"
