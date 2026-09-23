import PoincareConjecture.ParallelImplementation.ConformalConnection
set_option autoImplicit false
noncomputable section
open Riemannian
open scoped ContDiff Manifold Topology Bundle
namespace PoincareConjecture.ParallelImplementation.ConformalHessian
open PoincareConjecture.ParallelImplementation.ConformalConnection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
theorem hessian_conformalMetric (g : RiemannianMetric I M)
    (u f : M → ℝ) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (X Y : SmoothVectorField I M) (p : M) :
    X.dir (Y.dir f) p - ((conformalMetric g u hu).leviCivitaConnection.cov X Y).dir f p =
      (X.dir (Y.dir f) p - (g.leviCivitaConnection.cov X Y).dir f p) -
      X.dir u p * Y.dir f p - Y.dir u p * X.dir f p +
      g.metricInner p (X p) (Y p) * (MorganTianLib.gradientField g u hu).dir f p :=
/- SWARM_PROOF_BEGIN -/
by
  have hcov := conformalMetric_leviCivitaConnection_cov g hu X Y p
  have hlin := congrArg (fun v : TangentSpace I p => (mfderiv% f p) v) hcov
  have hdir : ((conformalMetric g u hu).leviCivitaConnection.cov X Y).dir f p =
      (g.leviCivitaConnection.cov X Y).dir f p +
        X.dir u p * Y.dir f p + Y.dir u p * X.dir f p -
        g.metricInner p (X p) (Y p) *
          (MorganTianLib.gradientField g u hu).dir f p := by
    simpa only [SmoothVectorField.dir, map_add, map_sub, map_smul, smul_eq_mul]
      using hlin
  rw [hdir]
  ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ConformalHessian
