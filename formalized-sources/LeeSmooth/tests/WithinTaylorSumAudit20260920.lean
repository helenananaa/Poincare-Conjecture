import LeeSmoothLib.Ch01.Sec01_06.WithinTaylorSums
import LeeSmoothLib.Verified.LevelSets.EmptyFiberDimension
import Lean

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[``LeeSmooth.WithinTaylorSums.hasFTaylorSeriesUpToOn_tsum,
    ``LeeSmooth.WithinTaylorSums.hasFDerivWithinAt_tsum,
    ``LeeSmooth.WithinTaylorSums.iteratedFDerivWithin_tsum,
    ``LeeSmooth.WithinTaylorSums.iteratedFDerivWithin_tsum_of_interior,
    ``LeeSmooth.WithinTaylorSums.tsum_curry0_of_hasFTaylorSeriesUpToOn,
    ``LeeSmooth.WithinTaylorSums.tsum_curryLeft_taylorCoeff,
    ``LeeSmooth.WithinTaylorSums.tendstoUniformlyOn_tsum_taylorCoeff,
    ``LeeSmooth.WithinTaylorSums.continuousOn_tsum_taylorCoeff,
    ``LeeSmooth.WithinTaylorSums.tsum_taylorCoeff_eqOn,
    ``LeeSmooth.WithinTaylorSums.summable_taylorCoeff,
    ``LeeLevelSetEmptyFiber.no_codimension_one_bundle_for_avoidsZero,
    ``LeeLevelSetEmptyFiber.model_finrank_le_of_nonempty_regular_fiber]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in targets do
    unless (← getEnv).contains n do throwError "Missing declaration: {n}"
    let axs ← Lean.collectAxioms n
    let bad := axs.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Nonstandard axioms for {n}: {bad}"
    logInfo m!"PASS {n}: {axs}"
  logInfo m!"WITHIN_SUMS_DIMENSION_GUARD_PASS {targets.size}"
