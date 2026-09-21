import MorganTianLib.Ch02.SurgeryCap.SphereFieldAlgebra
open Set Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
noncomputable section
namespace MorganTianLib.SurgeryCap
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Actual induced sphere metric equals the ambient inner product of inclusion derivatives. -/
theorem sphere_metricInner_eq_ambient
    (X Y : SmoothVectorField (𝓡 2) EpsilonNeckSphere) (p : EpsilonNeckSphere) :
    unitRoundSphereMetric.metricInner p (X p) (Y p) =
      inner ℝ (sphereAmbientField X p) (sphereAmbientField Y p) := by
/- SWARM_PROOF_BEGIN -/
  letI : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  rw [unitRoundSphereMetric]
  change DCInducedForm (DCEuclideanMetric (F := E3))
      ((↑) : EpsilonNeckSphere → E3) p (X p) (Y p) = _
  rw [DCInducedForm_apply, DCEuclideanMetric_apply]
  rfl
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
