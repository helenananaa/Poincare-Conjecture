import LeeSmoothLib.Ch04.Sec04_22.Exercise_4_9
import Lean
open Lean Elab Command in
run_cmd do
  let names : Array Name := #[``mfderiv_isInvertible_of_immersion_and_submersion_target_boundary_point, ``is_local_diffeomorph_isImmersionAtOfComplement_target_boundary, ``is_local_diffeomorph_iff_is_immersion_and_is_smooth_submersion_target_boundary, ``is_local_diffeomorph_iff_is_mfderiv_injective_and_is_smooth_submersion_target_boundary, ``is_local_diffeomorph_of_is_immersion_of_eq_dim_target_boundary, ``is_local_diffeomorph_of_is_smooth_submersion_of_eq_dim_target_boundary, ``euclidean_half_space_inclusion_mfderiv_eq_id, ``euclidean_half_space_inclusion_is_immersion_not_local_diffeomorph]
  for n in names do
    unless (← getEnv).contains n do throwError "Missing target: {n}"
    let a ← Lean.collectAxioms n
    unless (a.filter (fun x ↦ !(#[``propext, ``Classical.choice, ``Quot.sound]).contains x)).isEmpty do
      throwError "Unaccepted axioms: {n}: {a}"
    logInfo m!"PASS {n}: {a}"
  logInfo m!"EX49_GUARD_PASS {names.size}"
