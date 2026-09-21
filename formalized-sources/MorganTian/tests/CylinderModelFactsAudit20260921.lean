import MorganTianLib.Ch02.NeckVolume.ScaleNormalization
import Lean
open Lean Elab Command in
run_cmd do
  let names : Array Name := #[``MorganTianLib.boundaryless_model_transContinuousLinearEquiv, ``MorganTianLib.epsilonNeckCylinderModel_instBoundaryless, ``MorganTianLib.epsilonNeck_scale_pos_and_metric_normalization]
  for n in names do
    unless (← getEnv).contains n do throwError "Missing declaration: {n}"
    let a ← Lean.collectAxioms n
    unless (a.filter (fun x ↦ !(#[``propext, ``Classical.choice, ``Quot.sound]).contains x)).isEmpty do
      throwError "Unapproved axioms {n}: {a}"
    logInfo m!"PASS {n}: {a}"
  logInfo "CYLINDER_MODEL_GUARD_PASS 3"
