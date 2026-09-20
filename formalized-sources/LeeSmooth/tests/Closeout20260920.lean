import LeeSmoothLib.Ch04.Sec04_21.Proposition_4_1
import LeeSmoothLib.Ch04.Sec04_22.Proposition_4_6
import LeeSmoothLib.Ch05.Sec05_28.Proposition_5_3
import LeeSmoothLib.Ch05.Sec05_35.Proposition_5_38
import Lean

-- Fail if a target is absent, acquires a transitive proof hole, or uses a new axiom.
open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[
    ``Manifold.exists_open_restriction_isSmoothSubmersion_of_surjective_mfderiv,
    ``Manifold.exists_open_restriction_isImmersion_of_injective_mfderiv,
    ``isLocalDiffeomorph_comp,
    ``isLocalDiffeomorph_pi,
    ``isLocalDiffeomorph_iff_writtenInExtChartAt,
    ``range_productSliceMap_eq_univ_prod_singleton,
    ``productSliceMap_isSmoothEmbedding,
    ``product_slice_has_induced_manifold_structure,
    ``tangentSpace_eq_ker_mfderiv_of_isLocalDefiningMapOn]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in targets do
    unless (← getEnv).contains target do throwError "Missing target: {target}"
    let axioms ← Lean.collectAxioms target
    let unexpected := axioms.filter (fun a ↦ !allowed.contains a)
    if !unexpected.isEmpty then
      throwError "Nonstandard axioms for {target}: {unexpected}"
    logInfo m!"PASS {target}: {axioms}"
  logInfo m!"LEE_CLOSEOUT_20260920: {targets.size} target declarations passed."
