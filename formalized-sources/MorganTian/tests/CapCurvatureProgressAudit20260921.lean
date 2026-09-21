import MorganTianLib.Ch02.SurgeryCap.RegularizedRadius
import MorganTianLib.Ch02.SurgeryCap.PolarDiffeomorphism
import MorganTianLib.Ch02.SurgeryCap.WarpedHorizontalConnection
import MorganTianLib.Ch02.SurgeryCap.RadialSectional
import MorganTianLib.Ch02.SurgeryCap.PolarMetric
import Lean
open Set Riemannian
open scoped Manifold ContDiff Topology

/-- **Math.** Nonzero horizontal directions used by the sectional quotient really exist. -/
example : ∃ (p : MorganTianLib.EpsilonNeckSphere)
    (X : SmoothVectorField (𝓡 2) MorganTianLib.EpsilonNeckSphere), X p ≠ 0 := by
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty.mpr (show (0 : ℝ) ≤ 1 by norm_num) :
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty)
  let p : MorganTianLib.EpsilonNeckSphere := ⟨x, hx⟩
  haveI : Nontrivial (TangentSpace (𝓡 2) p) :=
    inferInstanceAs (Nontrivial (EuclideanSpace ℝ (Fin 2)))
  obtain ⟨v, hv⟩ := exists_ne (0 : TangentSpace (𝓡 2) p)
  obtain ⟨X, hX⟩ := exists_smoothVectorField_eq (I := 𝓡 2) p v
  exact ⟨p, X, by simpa only [hX] using hv⟩

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``MorganTianLib.SurgeryCap.exists_cap_polar_metric_preserving,
    ``MorganTianLib.SurgeryCap.exists_cap_polar_diffeomorph,
    ``MorganTianLib.SurgeryCap.warpedConnection_radial_formulas,
    ``MorganTianLib.SurgeryCap.warpedConnection_horizontal_formula,
    ``MorganTianLib.SurgeryCap.warpedConnection_radial_curvature,
    ``MorganTianLib.SurgeryCap.RoundCapProfile.globalMetric_radial_cauchy,
    ``MorganTianLib.SurgeryCap.RoundCapProfile.globalMetric_regularized_radial_bound,
    ``MorganTianLib.SurgeryCap.regularizedRadius_contDiff,
    ``MorganTianLib.SurgeryCap.regularizedRadius_fderiv,
    ``MorganTianLib.SurgeryCap.RoundCapProfile.regularizedRadius_differential_bound,
    ``MorganTianLib.SurgeryCap.RoundCapProfile.radial_curvature_pairing,
    ``MorganTianLib.SurgeryCap.RoundCapProfile.radial_curvature_nonneg,
    ``MorganTianLib.SurgeryCap.RoundCapProfile.radial_sectional_formula]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    unless (axioms.filter (fun a => !allowed.contains a)).isEmpty do
      throwError "Unaccepted axioms for {name}: {axioms}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"CAP_CURVATURE_PROGRESS_GUARD_PASS {names.size}"
