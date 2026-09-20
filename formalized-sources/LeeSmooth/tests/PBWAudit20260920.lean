import LeeSmoothLib.External.TauCetiPBW.Algebra.Lie.UniversalEnveloping.PBW.Basis
import Lean

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[
    ``TauCeti.UniversalEnvelopingAlgebra.PBWAction.act_map_lie,
    ``TauCeti.UniversalEnvelopingAlgebra.PBWAction.actMonomial_hard_eq,
    ``TauCeti.UniversalEnvelopingAlgebra.PBWAction.totalDegree_actMonomial_le,
    ``TauCeti.UniversalEnvelopingAlgebra.polyLieHom,
    ``TauCeti.UniversalEnvelopingAlgebra.polyRepresentation,
    ``TauCeti.UniversalEnvelopingAlgebra.evalAtOne_orderedBasisMonomial,
    ``TauCeti.UniversalEnvelopingAlgebra.linearIndependent_orderedBasisMonomial,
    ``TauCeti.UniversalEnvelopingAlgebra.linearIndependent_ordered_monomials_of_finite,
    ``TauCeti.UniversalEnvelopingAlgebra.orderedPBWBasis,
    ``TauCeti.UniversalEnvelopingAlgebra.evalAtOne_injective,
    ``TauCeti.UniversalEnvelopingAlgebra.evalAtOne_bijective]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in targets do
    unless (← getEnv).contains name do throwError "Missing target {name}"
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter (fun a ↦ !allowed.contains a)
    unless unexpected.isEmpty do throwError "Unexpected axioms for {name}: {unexpected}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"PBW_INDEPENDENT_GUARD_PASS {targets.size}"
