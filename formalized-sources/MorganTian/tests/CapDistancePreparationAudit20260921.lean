import MorganTianLib.Ch02.SurgeryCap.RadialControl
import MorganTianLib.Ch02.SurgeryCap.PolarDiffeomorphism
import Lean
open Lean Elab Command in
run_cmd do
  let names : Array Name := #[``MorganTianLib.SurgeryCap.exists_cap_polar_diffeomorph, ``MorganTianLib.SurgeryCap.RoundCapProfile.globalMetric_radial_cauchy, ``MorganTianLib.SurgeryCap.RoundCapProfile.globalMetric_regularized_radial_bound]
  for name in names do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axs ← Lean.collectAxioms name
    unless (axs.filter (fun x => !(#[``propext, ``Classical.choice, ``Quot.sound]).contains x)).isEmpty do throwError "Unaccepted axioms: {name}: {axs}"
    logInfo m!"PASS {name}: {axs}"
  logInfo m!"CAP_DISTANCE_PREPARATION_GUARD_PASS {names.size}"
