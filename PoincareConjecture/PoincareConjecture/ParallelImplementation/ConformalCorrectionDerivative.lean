import PoincareConjecture.ParallelImplementation.ConformalConnection
set_option autoImplicit false
noncomputable section
open Riemannian
open scoped ContDiff Manifold Topology Bundle
namespace PoincareConjecture.ParallelImplementation.ConformalCorrectionDerivative
open PoincareConjecture.ParallelImplementation.ConformalConnection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
theorem cov_conformalCorrection (g : RiemannianMetric I M)
    (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (nabla : AffineConnection I M)
    (W U V : SmoothVectorField I M) (p : M) :
    nabla.cov W (conformalCorrection g u hu U V) p =
      W.dir (U.dir u) p • V p + U.dir u p • nabla.cov W V p +
      W.dir (V.dir u) p • U p + V.dir u p • nabla.cov W U p -
      W.dir (fun q => g.metricInner q (U q) (V q)) p • MorganTianLib.gradientField g u hu p -
      g.metricInner p (U p) (V p) • nabla.cov W (MorganTianLib.gradientField g u hu) p :=
/- SWARM_PROOF_BEGIN -/
by
  have hneg (T : SmoothVectorField I M) :
      nabla.cov W (-T) p = -nabla.cov W T p := by
    have h := nabla.leibniz (fun _ : M => (-1 : ℝ)) contMDiff_const W T p
    have hdir : W.dir (fun _ : M => (-1 : ℝ)) p = 0 := by
      simp [SmoothVectorField.dir]
    have hfield :
        SmoothVectorField.smul (fun _ : M => (-1 : ℝ)) contMDiff_const T = -T := by
      apply SmoothVectorField.ext
      intro q
      simp [SmoothVectorField.smul_apply]
    rw [hfield] at h
    simpa [hdir] using h
  have hU := nabla.leibniz (U.dir u) (U.dir_contMDiff hu) W V p
  have hV := nabla.leibniz (V.dir u) (V.dir_contMDiff hu) W U p
  have hmetric := nabla.leibniz
    (fun q => g.metricInner q (U q) (V q))
    (g.metricInner_field_contMDiff U V) W (MorganTianLib.gradientField g u hu) p
  have hsub (S T : SmoothVectorField I M) : S - T = S + -T := by
    apply SmoothVectorField.ext
    intro q
    simp only [SmoothVectorField.sub_apply, SmoothVectorField.add_apply,
      sub_eq_add_neg]
    rfl
  change nabla.cov W
      ((SmoothVectorField.smul (U.dir u) (U.dir_contMDiff hu) V +
        SmoothVectorField.smul (V.dir u) (V.dir_contMDiff hu) U) -
        SmoothVectorField.smul (fun q => g.metricInner q (U q) (V q))
          (g.metricInner_field_contMDiff U V) (MorganTianLib.gradientField g u hu)) p = _
  rw [hsub]
  rw [nabla.add_right W _ _]
  rw [nabla.add_right W _ _]
  simp only [SmoothVectorField.add_apply]
  rw [hU, hV, hneg, hmetric]
  module
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ConformalCorrectionDerivative
