import PoincareConjecture.ParallelImplementation.ConformalConnection
set_option autoImplicit false
noncomputable section
open Riemannian
open scoped ContDiff Manifold Topology Bundle
namespace PoincareConjecture.ParallelImplementation.ConformalQuadraticContraction
open PoincareConjecture.ParallelImplementation.ConformalConnection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
theorem quadratic_conformal_correction (g : RiemannianMetric I M)
    (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (X Y : SmoothVectorField I M) (p : M)
    (hX : g.metricInner p (X p) (X p) = 1)
    (hY : g.metricInner p (Y p) (Y p) = 1)
    (hXY : g.metricInner p (X p) (Y p) = 0) :
    g.metricInner p ((conformalCorrection g u hu X (conformalCorrection g u hu Y Y) -
      conformalCorrection g u hu Y (conformalCorrection g u hu X Y)) p) (X p) =
      (X.dir u p)^2 + (Y.dir u p)^2 -
      g.metricInner p (MorganTianLib.gradientField g u hu p) (MorganTianLib.gradientField g u hu p) :=
/- SWARM_PROOF_BEGIN -/
by
  let G := MorganTianLib.gradientField g u hu p
  let a := X.dir u p
  let b := Y.dir u p
  have hGX : g.metricInner p G (X p) = a := by
    exact MorganTianLib.metricInner_gradientField_eq_dir g hu X p
  have hGY : g.metricInner p G (Y p) = b := by
    exact MorganTianLib.metricInner_gradientField_eq_dir g hu Y p
  have hXG : g.metricInner p (X p) G = a := by
    rw [g.metricInner_comm p (X p) G]
    exact hGX
  have hYG : g.metricInner p (Y p) G = b := by
    rw [g.metricInner_comm p (Y p) G]
    exact hGY
  have hYX : g.metricInner p (Y p) (X p) = 0 := by
    rw [g.metricInner_comm p (Y p) (X p)]
    exact hXY
  have hYY : conformalCorrection g u hu Y Y p = (2 * b) • Y p - G := by
    rw [conformalCorrection_apply]
    simp only [hY, b]
    module
  have hXYcorr : conformalCorrection g u hu X Y p = a • Y p + b • X p := by
    rw [conformalCorrection_apply]
    simp only [hXY, a, b]
    module
  have hdirYY : (conformalCorrection g u hu Y Y).dir u p =
      2 * b ^ 2 - g.metricInner p G G := by
    calc
      (conformalCorrection g u hu Y Y).dir u p =
          g.metricInner p G (conformalCorrection g u hu Y Y p) :=
        (MorganTianLib.metricInner_gradientField_eq_dir g hu
          (conformalCorrection g u hu Y Y) p).symm
      _ = g.metricInner p (conformalCorrection g u hu Y Y p) G :=
        g.metricInner_comm p G (conformalCorrection g u hu Y Y p)
      _ = 2 * b ^ 2 - g.metricInner p G G := by
        rw [hYY]
        simp only [g.metricInner_sub_left, g.metricInner_smul_left, hYG]
        ring
  have hdirXY : (conformalCorrection g u hu X Y).dir u p = 2 * a * b := by
    calc
      (conformalCorrection g u hu X Y).dir u p =
          g.metricInner p G (conformalCorrection g u hu X Y p) :=
        (MorganTianLib.metricInner_gradientField_eq_dir g hu
          (conformalCorrection g u hu X Y) p).symm
      _ = g.metricInner p (conformalCorrection g u hu X Y p) G :=
        g.metricInner_comm p G (conformalCorrection g u hu X Y p)
      _ = 2 * a * b := by
        rw [hXYcorr]
        simp only [g.metricInner_add_left, g.metricInner_smul_left, hYG, hXG]
        ring
  have hXYY : g.metricInner p (X p) (conformalCorrection g u hu Y Y p) = -a := by
    rw [hYY]
    simp only [g.metricInner_sub_right, g.metricInner_smul_right, hXY, hXG]
    ring
  have hYXY : g.metricInner p (Y p) (conformalCorrection g u hu X Y p) = a := by
    rw [hXYcorr]
    simp only [g.metricInner_add_right, g.metricInner_smul_right, hY, hYX]
    ring
  let Z : SmoothVectorField I M := conformalCorrection g u hu Y Y
  let W : SmoothVectorField I M := conformalCorrection g u hu X Y
  change g.metricInner p ((conformalCorrection g u hu X Z -
      conformalCorrection g u hu Y W) p) (X p) = _
  have hZ : Z p = (2 * b) • Y p - G := hYY
  have hW : W p = a • Y p + b • X p := hXYcorr
  have hdirZ : Z.dir u p = 2 * b ^ 2 - g.metricInner p G G := hdirYY
  have hdirW : W.dir u p = 2 * a * b := hdirXY
  have hXZ : g.metricInner p (X p) (Z p) = -a := hXYY
  have hYW : g.metricInner p (Y p) (W p) = a := hYXY
  rw [SmoothVectorField.sub_apply]
  have houterX := conformalCorrection_apply (g := g) (u := u) hu X Z p
  have houterY := conformalCorrection_apply (g := g) (u := u) hu Y W p
  rw [houterX, houterY]
  rw [hXZ, hYW, hZ, hW, hdirZ, hdirW]
  simp only [g.metricInner_sub_left, g.metricInner_add_left,
    g.metricInner_smul_left, hGX, hYX, hX, G, a, b]
  ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ConformalQuadraticContraction
