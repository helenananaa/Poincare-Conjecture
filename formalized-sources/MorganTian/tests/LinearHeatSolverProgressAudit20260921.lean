import MorganTianLib.Ch02.SurgeryCap.ScalarTraceThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatOperator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHolderControl
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelZeroTrace
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HeatOperatorNorm
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalInitialTrace
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalMoment
import Lean

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[``MorganTianLib.ParabolicPDE.exists_three_dimensional_bounded_heat_operator, ``MorganTianLib.ParabolicPDE.exists_three_dimensional_bounded_heat_semigroup, ``MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_fractional_moment, ``MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_uniform_initial_trace, ``MorganTianLib.ParabolicPDE.gaussianHeatKernel_duhamel_holder_control, ``MorganTianLib.ParabolicPDE.gaussianHeatKernel_duhamel_uniform_zero_trace, ``MorganTianLib.SurgeryCap.scalarCurvature_three_trace, ``MorganTianLib.ParabolicPDE.exists_three_dimensional_heat_operator_norm_one]
  for n in names do
    unless (← getEnv).contains n do throwError "Missing declaration: {n}"
    let a ← Lean.collectAxioms n
    unless (a.filter (fun x ↦ !(#[``propext, ``Classical.choice, ``Quot.sound]).contains x)).isEmpty do throwError "Unaccepted axioms for {n}: {a}"
    logInfo m!"PASS {n}: {a}"
  logInfo m!"LINEAR_HEAT_SOLVER_PROGRESS_GUARD_PASS {names.size}"
