import MorganTianLib.Ch02.NeckVolume.CylinderModelFacts
open Set
open scoped ContDiff Manifold Topology
noncomputable section
namespace MorganTianLib

/-- **Math.** The transported finite-cylinder chart keeps the axial coordinate. -/
theorem roundCylinder_extChartAt_apply (epsilon : ℝ) (a p : epsilonNeckDomain epsilon) :
    extChartAt EpsilonNeckCylinderModel a p =
      epsilonNeckModelEquiv (extChartAt (𝓡 2) a.1.1 p.1.1, p.1.2) := by
  rfl

/-- **Math.** The inverse chart recovers the axis on its target; no claim is
made for the totalized inverse outside that target. -/
theorem roundCylinder_extChartAt_symm_axis
    (epsilon : ℝ) (a : epsilonNeckDomain epsilon)
    (u : EuclideanSpace ℝ (Fin 2)) (t : EpsilonNeckAxis)
    (hz : epsilonNeckModelEquiv (u, t) ∈ (extChartAt EpsilonNeckCylinderModel a).target) :
    ((extChartAt EpsilonNeckCylinderModel a).symm
      (epsilonNeckModelEquiv (u, t))).1.2 = t := by
  have h := (extChartAt EpsilonNeckCylinderModel a).right_inv hz
  rw [roundCylinder_extChartAt_apply] at h
  exact congrArg Prod.snd (epsilonNeckModelEquiv.injective h)

end MorganTianLib
