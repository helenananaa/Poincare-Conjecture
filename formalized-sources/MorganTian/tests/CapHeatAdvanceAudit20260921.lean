import MorganTianLib.Ch02.SurgeryCap.CompleteBoundedCap
import MorganTianLib.Ch02.SurgeryCap.FullPuncturedCurvature
import MorganTianLib.Ch02.SurgeryCap.GlobalCurvatureBound
import MorganTianLib.Ch02.SurgeryCap.ReferenceCylinderProducer
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Equation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanBasic
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FractionalMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HessianCancellation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HessianEstimate
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderInitialTrace
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderTimeKernel
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.KernelScaling
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.UniformInitialTrace
import Lean
open Set MeasureTheory MorganTianLib MorganTianLib.SurgeryCap MorganTianLib.ParabolicPDE
open scoped Manifold ContDiff Topology
noncomputable section

/-- **Math.** The reference-cylinder result is usable on a nonempty actual cylinder. -/
example : ∃ _p : epsilonNeckDomain (1 : ℝ),
    ∃ g0 : Riemannian.RiemannianMetric EpsilonNeckCylinderModel (epsilonNeckDomain 1),
      IsRoundCylinderMetric 1 g0 := by
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty.mpr (show (0 : ℝ) ≤ 1 by norm_num) :
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty)
  let p : epsilonNeckDomain (1 : ℝ) :=
    ⟨(⟨x, hx⟩, (0 : EpsilonNeckAxis)), by
      change -(1 : ℝ)⁻¹ < (0 : EpsilonNeckAxis) 0 ∧ (0 : EpsilonNeckAxis) 0 < (1 : ℝ)⁻¹
      norm_num⟩
  obtain ⟨g0, hg0⟩ := exists_reference_round_cylinder_metric 1
  exact ⟨p, g0, hg0⟩

/-- **Math.** Zero integral of the Hessian is cancellation, not a zero function. -/
example : iteratedDeriv 2 (gaussianHeatKernel 1) 0 < 0 := by
  rw [((gaussianHeatKernel_derivatives (t := 1) (by norm_num)).2 0).2.1]
  have hp := gaussianHeatKernel_pos (t := 1) (by norm_num) 0
  norm_num [gaussianHeatHessian]
  nlinarith

/-- **Math.** The diagonal singularity has the expected nonzero finite integral. -/
example : (∫ s in (0 : ℝ)..1, (1 - s) ^ ((1 / 2 : ℝ) / 2 - 1)) = 4 := by
  have h := (holderTimeKernel_integrable_integral (alpha := 1 / 2) (T := 1) (by norm_num)).2
  norm_num at h ⊢
  exact h

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[``MorganTianLib.SurgeryCap.RoundCapProfile.punctured_curvature_nonneg_bounded,
    ``MorganTianLib.SurgeryCap.exists_reference_round_cylinder_metric,
    ``MorganTianLib.SurgeryCap.RoundCapProfile.global_curvature_nonneg_bounded,
    ``MorganTianLib.ParabolicPDE.gaussianHeatKernel_derivatives,
    ``MorganTianLib.ParabolicPDE.gaussianHeatKernel_fractional_moment,
    ``MorganTianLib.ParabolicPDE.gaussianHeatKernel_hessian_cancellation,
    ``MorganTianLib.ParabolicPDE.gaussianHeatKernel_holder_initial_trace,
    ``MorganTianLib.ParabolicPDE.gaussianHeatKernel_hessian_holder_bound,
    ``MorganTianLib.ParabolicPDE.euclideanHeatKernel_mass_semigroup,
    ``MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_heat_equation,
    ``MorganTianLib.SurgeryCap.exists_complete_nonnegative_bounded_global_cap,
    ``MorganTianLib.ParabolicPDE.holderTimeKernel_integrable_integral,
    ``MorganTianLib.ParabolicPDE.euclideanHeatKernel_pos,
    ``MorganTianLib.ParabolicPDE.gaussianHeatKernel_holder_uniform_initial_trace,
    ``MorganTianLib.ParabolicPDE.gaussianHeatKernel_sqrt_scale,
    ``MorganTianLib.ParabolicPDE.gaussianHeatHessian_sqrt_scale]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in names do
    unless (← getEnv).contains n do throwError "Missing declaration: {n}"
    let ax ← Lean.collectAxioms n
    unless (ax.filter (fun a ↦ !allowed.contains a)).isEmpty do throwError "Unexpected axioms: {n}: {ax}"
    logInfo m!"PASS {n}: {ax}"
  logInfo m!"CAP_HEAT_ADVANCE_GUARD_PASS {names.size}"
