import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelZeroTrace
import MorganTianLib.Ch02.SurgeryCap.ScalarTraceThree
import Lean
open Lean Elab Command in
run_cmd do
  let names : Array Name := #[``MorganTianLib.ParabolicPDE.gaussianHeatKernel_duhamel_uniform_zero_trace, ``MorganTianLib.SurgeryCap.scalarCurvature_three_trace]
  for n in names do
    unless (← getEnv).contains n do throwError "Missing declaration: {n}"
    let a ← Lean.collectAxioms n
    unless (a.filter (fun x ↦ !(#[``propext, ``Classical.choice, ``Quot.sound]).contains x)).isEmpty do throwError "Invalid axioms for {n}: {a}"
    logInfo m!"PASS {n}: {a}"
  logInfo m!"LINEAR_HEAT_SUPPORT_GUARD_PASS {names.size}"
