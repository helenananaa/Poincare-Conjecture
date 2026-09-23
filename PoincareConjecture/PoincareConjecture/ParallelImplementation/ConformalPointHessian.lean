import PoincareConjecture.ParallelImplementation.ConformalHessian
import MorganTianLib.Ch02.Laplacian
set_option autoImplicit false
noncomputable section
open Riemannian
open scoped ContDiff Manifold Topology Bundle
namespace PoincareConjecture.ParallelImplementation.ConformalPointHessian
open PoincareConjecture.ParallelImplementation.ConformalConnection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
def scalarDifferential (f : M → ℝ) (p : M) (v : TangentSpace I p) : ℝ :=
  mfderiv I 𝓘(ℝ, ℝ) f p v

theorem hessianAt_conformalMetric (g : RiemannianMetric I M)
    (u f : M → ℝ) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) (v w : TangentSpace I p) :
    MorganTianLib.hessianAt (conformalMetric g u hu).leviCivitaConnection f p v w =
      MorganTianLib.hessianAt g.leviCivitaConnection f p v w -
      scalarDifferential u p v * scalarDifferential f p w -
      scalarDifferential u p w * scalarDifferential f p v +
      g.metricInner p v w * (MorganTianLib.gradientField g u hu).dir f p :=
/- SWARM_PROOF_BEGIN -/
by
  simp only [MorganTianLib.hessianAt_def]
  simpa [MorganTianLib.hessian, scalarDifferential,
    Riemannian.SmoothVectorField.dir, MorganTianLib.extendVector_apply] using
    PoincareConjecture.ParallelImplementation.ConformalHessian.hessian_conformalMetric
      g u f hu hf (MorganTianLib.extendVector p v) (MorganTianLib.extendVector p w) p
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ConformalPointHessian
