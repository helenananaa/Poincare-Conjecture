import MorganTianLib.Ch02.EpsilonNeck
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh6Sphere
open Set Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
noncomputable section
namespace MorganTianLib.SurgeryCap
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** The inclusion differential reads a genuine sphere field as an
ambient vector field along the inclusion. This is not a connection assumption. -/
def sphereAmbientField (X : SmoothVectorField (𝓡 2) EpsilonNeckSphere)
    (p : EpsilonNeckSphere) : E3 :=
  mvfderiv (𝓡 2) (Subtype.val : EpsilonNeckSphere → E3) p (X p)

end MorganTianLib.SurgeryCap
