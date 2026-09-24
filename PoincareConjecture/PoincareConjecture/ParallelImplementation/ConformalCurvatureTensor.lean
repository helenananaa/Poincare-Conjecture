import PoincareConjecture.ParallelImplementation.ConformalCorrectionDerivative
import PoincareConjecture.ParallelImplementation.ConformalCurvatureExpansion
import PoincareConjecture.ParallelImplementation.ConformalSectionalRecovered
import MorganTianLib.Ch02.GradientNormSq
set_option autoImplicit false
noncomputable section
open Riemannian
open scoped ContDiff Manifold Topology Bundle
namespace PoincareConjecture.ParallelImplementation.ConformalCurvatureTensor
open PoincareConjecture.ParallelImplementation.ConformalConnection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
def conformalCorrectionTensor (g : RiemannianMetric I M) (u : M → ℝ)
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (X Y : SmoothVectorField I M) (p : M) : ℝ :=
  MorganTianLib.hessian g.leviCivitaConnection u X Y p - X.dir u p * Y.dir u p +
    (1/2 : ℝ) * g.metricInner p (MorganTianLib.gradientField g u hu p)
      (MorganTianLib.gradientField g u hu p) * g.metricInner p (X p) (Y p)
/-- The full genuine curvature tensor transforms by the Hessian-gradient correction. -/
theorem curvatureForm_conformalMetric (g : RiemannianMetric I M)
    (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (X Y Z W : SmoothVectorField I M) (p : M) :
    MorganTianLib.curvatureForm (conformalMetric g u hu)
      (conformalMetric g u hu).leviCivitaConnection X Y Z W p =
    Real.exp (2*u p) * (MorganTianLib.curvatureForm g g.leviCivitaConnection X Y Z W p -
      g.metricInner p (X p) (Z p) * conformalCorrectionTensor g u hu Y W p -
      g.metricInner p (Y p) (W p) * conformalCorrectionTensor g u hu X Z p +
      g.metricInner p (X p) (W p) * conformalCorrectionTensor g u hu Y Z p +
      g.metricInner p (Y p) (Z p) * conformalCorrectionTensor g u hu X W p) :=
/- SWARM_PROOF_BEGIN -/
by
  let nabla := g.leviCivitaConnection
  let A := conformalCorrection g u hu
  let G := MorganTianLib.gradientField g u hu
  have hLC : nabla.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun U V T q => g.koszulDualSection_dual U V T q)
  have hgrad (T : SmoothVectorField I M) :
      g.metricInner p (G p) (T p) = T.dir u p :=
    MorganTianLib.metricInner_gradientField_eq_dir g hu T p
  have hgradSym (T : SmoothVectorField I M) :
      g.metricInner p (T p) (G p) = T.dir u p := by
    rw [g.metricInner_comm p (T p) (G p)]
    exact hgrad T
  have hgradInner (T : SmoothVectorField I M) :
      g.inner p (G p) (T p) = T.dir u p := by
    change g.metricInner p (G p) (T p) = _
    exact hgrad T
  have hgradSymInner (T : SmoothVectorField I M) :
      g.inner p (T p) (G p) = T.dir u p := by
    change g.metricInner p (T p) (G p) = _
    exact hgradSym T
  have hgradCov (U V : SmoothVectorField I M) :
      g.metricInner p ((nabla.cov U G) p) (V p) =
        MorganTianLib.hessian nabla u U V p := by
    have hfun : (fun q => g.metricInner q (G q) (V q)) = V.dir u := by
      funext q
      exact MorganTianLib.metricInner_gradientField_eq_dir g hu V q
    have hcompat := hLC.2 U G V p
    rw [hfun, MorganTianLib.metricInner_gradientField_eq_dir g hu
      (nabla.cov U V) p] at hcompat
    unfold MorganTianLib.hessian
    linarith
  have hmetric (U V T : SmoothVectorField I M) :
      U.dir (fun q => g.metricInner q (V q) (T q)) p =
        g.metricInner p ((nabla.cov U V) p) (T p) +
          g.metricInner p (V p) ((nabla.cov U T) p) :=
    hLC.2 U V T p
  have htorsion : (bracketField X Y) p =
      (nabla.cov X Y) p - (nabla.cov Y X) p := by
    simpa [Riemannian.bracketField] using (hLC.1 X Y p).symm
  have hbracketDir : (bracketField X Y).dir u p =
      X.dir (Y.dir u) p - Y.dir (X.dir u) p :=
    bracketField_dir X Y hu p
  have hessDir (U V : SmoothVectorField I M) :
      U.dir (V.dir u) p = MorganTianLib.hessian nabla u U V p +
        (nabla.cov U V).dir u p := by
    unfold MorganTianLib.hessian
    ring
  have hbracketZ :
      g.metricInner p ((bracketField X Y) p) (Z p) =
        g.metricInner p ((nabla.cov X Y) p) (Z p) -
          g.metricInner p ((nabla.cov Y X) p) (Z p) := by
    rw [htorsion, g.metricInner_sub_left]
  have hbracketW :
      g.metricInner p ((bracketField X Y) p) (W p) =
        g.metricInner p ((nabla.cov X Y) p) (W p) -
          g.metricInner p ((nabla.cov Y X) p) (W p) := by
    rw [htorsion, g.metricInner_sub_left]
  have hDerivative :
      g.metricInner p
        ((nabla.cov X (A Y W) - nabla.cov Y (A X W) +
          A X (nabla.cov Y W) - A Y (nabla.cov X W) -
          A (bracketField X Y) W) p) (Z p) =
        -g.metricInner p (X p) (Z p) *
            MorganTianLib.hessian nabla u Y W p -
          g.metricInner p (Y p) (W p) *
            MorganTianLib.hessian nabla u X Z p +
          g.metricInner p (X p) (W p) *
            MorganTianLib.hessian nabla u Y Z p +
          g.metricInner p (Y p) (Z p) *
            MorganTianLib.hessian nabla u X W p := by
    change g.metricInner p
      ((nabla.cov X (conformalCorrection g u hu Y W) -
        nabla.cov Y (conformalCorrection g u hu X W) +
        conformalCorrection g u hu X (nabla.cov Y W) -
        conformalCorrection g u hu Y (nabla.cov X W) -
        conformalCorrection g u hu (bracketField X Y) W) p) (Z p) = _
    have hcovX :=
      PoincareConjecture.ParallelImplementation.ConformalCorrectionDerivative.cov_conformalCorrection
        g u hu nabla X Y W p
    have hcovY :=
      PoincareConjecture.ParallelImplementation.ConformalCorrectionDerivative.cov_conformalCorrection
        g u hu nabla Y X W p
    simp only [SmoothVectorField.sub_apply, SmoothVectorField.add_apply]
    rw [hcovX, hcovY]
    simp only [conformalCorrection_apply, g.metricInner_sub_left,
      g.metricInner_add_left, g.metricInner_smul_left]
    rw [hbracketZ, hbracketW, hbracketDir,
      hmetric X Y W, hmetric Y X W,
      hgradCov X Z, hgradCov Y Z,
      hessDir X Y, hessDir Y X, hessDir X W, hessDir Y W]
    ring
  let a := X.dir u p
  let b := Y.dir u p
  let c := W.dir u p
  let d := Z.dir u p
  let xz := g.metricInner p (X p) (Z p)
  let yw := g.metricInner p (Y p) (W p)
  let xw := g.metricInner p (X p) (W p)
  let yz := g.metricInner p (Y p) (Z p)
  let wz := g.metricInner p (W p) (Z p)
  let xy := g.metricInner p (X p) (Y p)
  let n := g.metricInner p (G p) (G p)
  have hAYW : A Y W p = b • W p + c • Y p - yw • G p := by
    change conformalCorrection g u hu Y W p = _
    rw [conformalCorrection_apply]
  have hAXW : A X W p = a • W p + c • X p - xw • G p := by
    change conformalCorrection g u hu X W p = _
    rw [conformalCorrection_apply]
  have hAYWZ : g.metricInner p (A Y W p) (Z p) =
      b * wz + c * yz - yw * d := by
    rw [hAYW]
    simp only [g.metricInner_sub_left, g.metricInner_add_left,
      g.metricInner_smul_left]
    dsimp [wz, yz, d]
    rw [hgradInner Z]
  have hAXWZ : g.metricInner p (A X W p) (Z p) =
      a * wz + c * xz - xw * d := by
    rw [hAXW]
    simp only [g.metricInner_sub_left, g.metricInner_add_left,
      g.metricInner_smul_left]
    dsimp [wz, xz, d]
    rw [hgradInner Z]
  have hXAYW : g.metricInner p (X p) (A Y W p) =
      b * xw + c * xy - yw * a := by
    rw [hAYW]
    simp only [g.metricInner_sub_right, g.metricInner_add_right,
      g.metricInner_smul_right]
    dsimp [xw, xy, a]
    rw [hgradSymInner X]
  have hYAXW : g.metricInner p (Y p) (A X W p) =
      a * yw + c * g.metricInner p (Y p) (X p) - xw * b := by
    rw [hAXW]
    simp only [g.metricInner_sub_right, g.metricInner_add_right,
      g.metricInner_smul_right]
    dsimp [yw, xy, b]
    rw [hgradSymInner Y]
  have hdirAYW : (A Y W).dir u p = 2 * b * c - yw * n := by
    calc
      (A Y W).dir u p = g.metricInner p (G p) (A Y W p) :=
        (MorganTianLib.metricInner_gradientField_eq_dir g hu (A Y W) p).symm
      _ = g.metricInner p (A Y W p) (G p) :=
        g.metricInner_comm p (G p) (A Y W p)
      _ = 2 * b * c - yw * n := by
        rw [hAYW]
        simp only [g.metricInner_sub_left, g.metricInner_add_left,
          g.metricInner_smul_left]
        rw [hgradSym W, hgradSym Y]
        dsimp [n]
        ring
  have hdirAXW : (A X W).dir u p = 2 * a * c - xw * n := by
    calc
      (A X W).dir u p = g.metricInner p (G p) (A X W p) :=
        (MorganTianLib.metricInner_gradientField_eq_dir g hu (A X W) p).symm
      _ = g.metricInner p (A X W p) (G p) :=
        g.metricInner_comm p (G p) (A X W p)
      _ = 2 * a * c - xw * n := by
        rw [hAXW]
        simp only [g.metricInner_sub_left, g.metricInner_add_left,
          g.metricInner_smul_left]
        rw [hgradSym W, hgradSym X]
        dsimp [n]
        ring
  have hOuter1 :
      g.metricInner p (A X (A Y W) p) (Z p) =
        a * g.metricInner p (A Y W p) (Z p) +
          (A Y W).dir u p * xz -
            g.metricInner p (X p) (A Y W p) * d := by
    have h := conformalCorrection_apply (g := g) (u := u) hu X (A Y W) p
    rw [h]
    simp only [g.metricInner_sub_left, g.metricInner_add_left,
      g.metricInner_smul_left]
    rw [MorganTianLib.metricInner_gradientField_eq_dir g hu Z p]
  have hOuter2 :
      g.metricInner p (A Y (A X W) p) (Z p) =
        b * g.metricInner p (A X W p) (Z p) +
          (A X W).dir u p * yz -
            g.metricInner p (Y p) (A X W p) * d := by
    have h := conformalCorrection_apply (g := g) (u := u) hu Y (A X W) p
    rw [h]
    simp only [g.metricInner_sub_left, g.metricInner_add_left,
      g.metricInner_smul_left]
    rw [MorganTianLib.metricInner_gradientField_eq_dir g hu Z p]
  have hXYcomm : g.inner p (Y p) (X p) = g.inner p (X p) (Y p) := by
    change g.metricInner p (Y p) (X p) = g.metricInner p (X p) (Y p)
    exact g.metricInner_comm p (Y p) (X p)
  have hQuadratic :
      g.metricInner p
        ((A X (A Y W) - A Y (A X W)) p) (Z p) =
        xz * b * c + yw * a * d - xw * b * d - yz * a * c +
          n * (xw * yz - xz * yw) := by
    change g.metricInner p
      ((conformalCorrection g u hu X (conformalCorrection g u hu Y W) -
        conformalCorrection g u hu Y (conformalCorrection g u hu X W)) p) (Z p) = _
    rw [SmoothVectorField.sub_apply, g.metricInner_sub_left,
      hOuter1, hOuter2, hAYWZ, hAXWZ, hXAYW, hYAXW, hdirAYW, hdirAXW]
    dsimp [a, b, c, d, xz, yw, xw, yz, xy, n]
    rw [hXYcomm]
    ring
  have hcurve :
      (MorganTianLib.riemannCurvature
        (conformalMetric g u hu).leviCivitaConnection X Y W) p =
        (MorganTianLib.riemannCurvature nabla X Y W) p +
          (nabla.cov X (A Y W) - nabla.cov Y (A X W) +
            A X (nabla.cov Y W) - A Y (nabla.cov X W) -
            A (bracketField X Y) W) p +
          (A X (A Y W) - A Y (A X W)) p := by
    rw [PoincareConjecture.ParallelImplementation.ConformalCurvatureExpansion.riemannCurvature_conformal_expansion]
    simp only [SmoothVectorField.add_apply, SmoothVectorField.sub_apply]
    abel
  change (conformalMetric g u hu).metricInner p
      ((MorganTianLib.riemannCurvature
        (conformalMetric g u hu).leviCivitaConnection X Y W) p) (Z p) = _
  simp only [MorganTianLib.curvatureForm]
  rw [conformalMetric_metricInner g hu p]
  rw [hcurve, g.metricInner_add_left, g.metricInner_add_left,
    hDerivative, hQuadratic]
  simp [conformalCorrectionTensor, conformalFactor, nabla, G, n, a, b, c, d,
    xz, yw, xw, yz, MorganTianLib.gradientField]; ring_nf
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ConformalCurvatureTensor
