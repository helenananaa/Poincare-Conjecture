import PoincareConjecture.ParallelImplementation.ConformalConnection
import MorganTianLib.Ch01.CurvatureTensor
set_option autoImplicit false
noncomputable section
open Riemannian
open scoped ContDiff Manifold Topology Bundle
namespace PoincareConjecture.ParallelImplementation.ConformalCurvatureExpansion
open PoincareConjecture.ParallelImplementation.ConformalConnection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
theorem riemannCurvature_conformal_expansion (g : RiemannianMetric I M)
    (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (X Y Z : SmoothVectorField I M) :
    MorganTianLib.riemannCurvature (conformalMetric g u hu).leviCivitaConnection X Y Z =
      MorganTianLib.riemannCurvature g.leviCivitaConnection X Y Z +
      g.leviCivitaConnection.cov X (conformalCorrection g u hu Y Z) -
      g.leviCivitaConnection.cov Y (conformalCorrection g u hu X Z) +
      conformalCorrection g u hu X (g.leviCivitaConnection.cov Y Z) -
      conformalCorrection g u hu Y (g.leviCivitaConnection.cov X Z) +
      conformalCorrection g u hu X (conformalCorrection g u hu Y Z) -
      conformalCorrection g u hu Y (conformalCorrection g u hu X Z) -
      conformalCorrection g u hu (bracketField X Y) Z :=
/- SWARM_PROOF_BEGIN -/
by
  let nabla := g.leviCivitaConnection
  let A := conformalCorrection g u hu
  let nabla' := (conformalMetric g u hu).leviCivitaConnection
  have hcov (U V : SmoothVectorField I M) :
      nabla'.cov U V = nabla.cov U V + A U V := by
    apply SmoothVectorField.ext
    intro p
    change ((conformalMetric g u hu).leviCivitaConnection.cov U V) p = _
    rw [conformalMetric_leviCivitaConnection_cov]
    simp only [SmoothVectorField.add_apply, A, conformalCorrection_apply]
    module
  have hcovAt (U V : SmoothVectorField I M) (p : M) :
      (nabla'.cov U V) p = (nabla.cov U V) p + (A U V) p :=
    congrArg (fun W : SmoothVectorField I M => W p) (hcov U V)
  have hcovAdd (U V W : SmoothVectorField I M) (p : M) :
      (nabla.cov U (V + W)) p = (nabla.cov U V) p + (nabla.cov U W) p := by
    exact congrArg (fun T : SmoothVectorField I M => T p) (nabla.add_right U V W)
  have hAAdd (U V W : SmoothVectorField I M) (p : M) :
      (A U (V + W)) p = (A U V) p + (A U W) p := by
    simp only [A, conformalCorrection_apply, SmoothVectorField.add_apply,
      SmoothVectorField.dir_add_field, g.metricInner_add_right]
    module
  apply SmoothVectorField.ext
  intro p
  simp only [MorganTianLib.riemannCurvature, SmoothVectorField.sub_apply]
  rw [hcovAt X (nabla'.cov Y Z) p, hcovAt Y (nabla'.cov X Z) p,
    hcovAt (bracketField X Y) Z p]
  rw [hcov Y Z, hcov X Z]
  simp only [SmoothVectorField.add_apply, SmoothVectorField.sub_apply]
  rw [hcovAdd X (nabla.cov Y Z) (A Y Z) p,
    hcovAdd Y (nabla.cov X Z) (A X Z) p,
    hAAdd X (nabla.cov Y Z) (A Y Z) p,
    hAAdd Y (nabla.cov X Z) (A X Z) p]
  module
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ConformalCurvatureExpansion