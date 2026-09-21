import MorganTianLib.Ch02.SurgeryCap.Completeness
import MorganTianLib.Ch02.SurgeryCap.CurvatureNaturality
import MorganTianLib.Ch02.SurgeryCap.GeneralPlaneCurvature
import MorganTianLib.Ch02.SurgeryCap.GeodesicCompleteness
import MorganTianLib.Ch02.SurgeryCap.LocalMetricNaturality
import MorganTianLib.Ch02.SurgeryCap.RadialDistance
import MorganTianLib.Ch02.SurgeryCap.SphereCovariantFormula
import MorganTianLib.Ch02.SurgeryCap.SphereInnerDerivative
import MorganTianLib.Ch02.SurgeryCap.SphereIntrinsicCurvature
import MorganTianLib.Ch02.SurgeryCap.SphereMetricPairing
import MorganTianLib.Ch03.RicciFlow.InitialScalarVolumeBound
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Basic
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Semigroup
import Lean
set_option backward.isDefEq.respectTransparency false
open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[``MorganTianLib.SurgeryCap.sphere_metricInner_eq_ambient, ``MorganTianLib.SurgeryCap.sphere_dir_inner_rule, ``MorganTianLib.SurgeryCap.sphereAmbientField_canonical_cov, ``MorganTianLib.SurgeryCap.unitRoundSphereMetric_intrinsic_curvature_one, ``MorganTianLib.SurgeryCap.warpedConnection_general_plane_curvature, ``MorganTianLib.SurgeryCap.local_metric_map_covariant_related, ``MorganTianLib.compact_real_volume_upper_of_initial_scalar_lower, ``MorganTianLib.ParabolicPDE.gaussianHeatKernel_mass_semigroup, ``MorganTianLib.SurgeryCap.globalCap_riemannianEDist_zero, ``MorganTianLib.SurgeryCap.globalCap_intrinsic_proper_complete, ``MorganTianLib.SurgeryCap.RoundCapProfile.globalMetric_geodesicallyComplete, ``MorganTianLib.SurgeryCap.local_metric_map_curvature_related, ``MorganTianLib.ParabolicPDE.gaussianHeatKernel_pos]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in targets do
    unless (← getEnv).contains n do throwError "Missing declaration: {n}"
    let axioms ← Lean.collectAxioms n
    let bad := axioms.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do throwError "Nonstandard axioms for {n}: {bad}"
    logInfo m!"PASS {n}: {axioms}"
  logInfo m!"CAP_PDE_CRITICAL_PATH_GUARD_PASS {targets.size}"
