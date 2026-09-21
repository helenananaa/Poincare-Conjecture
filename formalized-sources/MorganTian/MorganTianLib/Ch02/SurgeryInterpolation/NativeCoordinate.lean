import MorganTianLib.Ch02.NeckVolume.CylinderModelFacts

open Riemannian
open scoped ContDiff Manifold Topology
noncomputable section
namespace MorganTianLib.SurgeryInterpolation

/-- **Math.** The genuine axial coordinate on the finite native neck. -/
def nativeAxis {epsilon : ℝ} (p : epsilonNeckDomain epsilon) : ℝ := p.1.2 0

/-- **Math.** Model transport preserves smoothness of the axial coordinate. -/
theorem nativeAxis_contMDiff (epsilon : ℝ) :
    ContMDiff EpsilonNeckCylinderModel 𝓘(ℝ, ℝ) ∞
      (nativeAxis : epsilonNeckDomain epsilon → ℝ) := by
  let changeModel := ContinuousLinearEquiv.toTransContinuousLinearEquiv
    (n := ∞) EpsilonNeckProductModel (epsilonNeckDomain epsilon) epsilonNeckModelEquiv
  have hprod : ContMDiff EpsilonNeckProductModel 𝓘(ℝ, ℝ) ∞
      (nativeAxis : epsilonNeckDomain epsilon → ℝ) := by
    exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).contDiff.contMDiff.comp
      (contMDiff_snd.comp contMDiff_subtype_val)
  exact hprod.comp changeModel.symm.contMDiff

end MorganTianLib.SurgeryInterpolation
