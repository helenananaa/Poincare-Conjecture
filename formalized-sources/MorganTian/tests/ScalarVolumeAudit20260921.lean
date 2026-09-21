import MorganTianLib.Ch03.RicciFlow.RealVolumeScalarLower
import Lean

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``MorganTianLib.volumeDensity_upper_of_scalar_lower,
    ``MorganTianLib.chartVolumeDensity_upper_of_scalar_lower,
    ``MorganTianLib.riemannianMeasure_upper_of_scalar_lower,
    ``MorganTianLib.finite_real_volume_upper_of_scalar_lower]
  for n in names do
    unless (← getEnv).contains n do throwError "Missing target: {n}"
    let a ← Lean.collectAxioms n
    unless (a.filter (fun x ↦ !(#[``propext, ``Classical.choice, ``Quot.sound]).contains x)).isEmpty do
      throwError "Unaccepted axioms: {n}: {a}"
    logInfo m!"PASS {n}: {a}"
  logInfo m!"SCALAR_VOLUME_GUARD_PASS {names.size}"

#check MorganTianLib.finite_real_volume_upper_of_scalar_lower
