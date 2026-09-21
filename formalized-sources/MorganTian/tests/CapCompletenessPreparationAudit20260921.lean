import MorganTianLib.Ch02.SurgeryCap.RegularizedRadius
import MorganTianLib.Ch02.SurgeryCap.PolarDiffeomorphism
import MorganTianLib.Ch02.SurgeryCap.WarpedRadialConnection
import Lean
open Lean Elab Command in
run_cmd do
  let names : Array Name := #[``MorganTianLib.SurgeryCap.exists_cap_polar_diffeomorph, ``MorganTianLib.SurgeryCap.warpedConnection_radial_formulas, ``MorganTianLib.SurgeryCap.RoundCapProfile.globalMetric_radial_cauchy, ``MorganTianLib.SurgeryCap.RoundCapProfile.globalMetric_regularized_radial_bound, ``MorganTianLib.SurgeryCap.regularizedRadius_contDiff, ``MorganTianLib.SurgeryCap.regularizedRadius_fderiv, ``MorganTianLib.SurgeryCap.RoundCapProfile.regularizedRadius_differential_bound]
  for name in names do
    unless (← getEnv).contains name do throwError "Missing target {name}"
    let axs ← Lean.collectAxioms name
    unless (axs.filter (fun x => !(#[``propext, ``Classical.choice, ``Quot.sound]).contains x)).isEmpty do throwError "Unaccepted axioms {name}: {axs}"
    logInfo m!"PASS {name}: {axs}"
  logInfo m!"CAP_COMPLETENESS_PREPARATION_PASS {names.size}"
