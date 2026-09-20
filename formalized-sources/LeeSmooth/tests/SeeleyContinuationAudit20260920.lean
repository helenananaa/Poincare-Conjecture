import LeeSmoothLib.Ch01.Sec01_06.Definition_1_6_extra_1
import Lean

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[``LeeSmooth.SeeleyExtension.seeleyLower_hasFTaylorSeriesUpToOn,
    ``LeeSmooth.SeeleyExtension.contDiffOn_closedUpperHalfSpace_exists_open_extension_at,
    ``LeeSmooth.SeeleyExtension.finite_contDiffOn_closedUpperHalfSpace_exists_open_extension_at,
    ``contDiffOn_range_halfSpace_exists_open_extension_at,
    ``contDiffOn_range_halfSpace_exists_open_extension_at_finite,
    ``boundary_halfSpace_image_exists_local_ambient_extension,
    ``forall_exists_smoothAmbientExtension_of_contDiffOn_halfSpace_image,
    ``contMDiffOn_halfSpace_iff_forall_exists_smoothAmbientExtension]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in targets do
    unless (← getEnv).contains n do throwError "Missing declaration: {n}"
    let axs ← Lean.collectAxioms n
    let bad := axs.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Nonstandard axioms for {n}: {bad}"
    logInfo m!"PASS {n}: {axs}"
  logInfo m!"SEELEY_CONTINUATION_GUARD_PASS {targets.size}"
