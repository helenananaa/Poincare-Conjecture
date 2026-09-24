import PoincareConjecture.ParallelImplementation.ConformalCorrectionDerivative
import PoincareConjecture.ParallelImplementation.ConformalQuadraticContraction
import PoincareConjecture.ParallelImplementation.ConformalCurvatureExpansion
import MorganTianLib.Ch02.GradientNormSq
import MorganTianLib.Ch01.PointwiseCurvature
set_option autoImplicit false
noncomputable section
open Riemannian
open scoped ContDiff Manifold Topology Bundle
namespace PoincareConjecture.ParallelImplementation.ConformalSectionalRecovered
open PoincareConjecture.ParallelImplementation.ConformalConnection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
theorem sectionalCurvatureAt_conformalMetric (g : RiemannianMetric I M)
    (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (X Y : SmoothVectorField I M) (p : M)
    (hX : g.metricInner p (X p) (X p) = 1)
    (hY : g.metricInner p (Y p) (Y p) = 1)
    (hXY : g.metricInner p (X p) (Y p) = 0) :
    MorganTianLib.sectionalCurvatureAt (conformalMetric g u hu)
      (conformalMetric g u hu).leviCivitaConnection p (X p) (Y p) =
      Real.exp (-2 * u p) *
        (MorganTianLib.sectionalCurvatureAt g g.leviCivitaConnection p (X p) (Y p) -
         MorganTianLib.hessian g.leviCivitaConnection u X X p -
         MorganTianLib.hessian g.leviCivitaConnection u Y Y p +
         (X.dir u p)^2 + (Y.dir u p)^2 -
         g.metricInner p (MorganTianLib.gradientField g u hu p)
           (MorganTianLib.gradientField g u hu p)) :=
/- SWARM_PROOF_BEGIN -/
by
  let nabla := g.leviCivitaConnection
  let A := conformalCorrection g u hu
  let G := MorganTianLib.gradientField g u hu
  let a := X.dir u p
  let b := Y.dir u p
  let d := g.metricInner p ((nabla.cov Y X) p) (Y p)
  let e := g.metricInner p ((nabla.cov X X) p) (Y p)
  let f := g.metricInner p ((nabla.cov X Y) p) (Y p)
  let k := g.metricInner p ((nabla.cov X Y) p) (X p)
  let l := g.metricInner p ((nabla.cov Y X) p) (X p)
  have hLC : nabla.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun U V W q => g.koszulDualSection_dual U V W q)
  have hYX : g.metricInner p (Y p) (X p) = 0 := by
    rw [g.metricInner_comm p (Y p) (X p)]
    exact hXY
  have hGY : g.metricInner p (G p) (Y p) = b := by
    exact MorganTianLib.metricInner_gradientField_eq_dir g hu Y p
  have hbracket : (bracketField Y X) p =
      (nabla.cov Y X) p - (nabla.cov X Y) p := by
    simpa [Riemannian.bracketField] using (hLC.1 Y X p).symm
  have hbrY : g.metricInner p ((bracketField Y X) p) (Y p) = d - f := by
    rw [hbracket, g.metricInner_sub_left]
  have hbrX : g.metricInner p ((bracketField Y X) p) (X p) = l - k := by
    rw [hbracket, g.metricInner_sub_left]
  have hmetricXX :
      Y.dir (fun q => g.metricInner q (X q) (X q)) p = 2 * l := by
    rw [hLC.2 Y X X p]
    rw [g.metricInner_comm p (X p) ((nabla.cov Y X) p)]
    simp only [l]
    ring
  have hmetricYX :
      X.dir (fun q => g.metricInner q (Y q) (X q)) p = k + e := by
    rw [hLC.2 X Y X p]
    rw [g.metricInner_comm p (Y p) ((nabla.cov X X) p)]
  have hGYcov :
      g.metricInner p ((nabla.cov Y G) p) (Y p) =
        MorganTianLib.hessian nabla u Y Y p := by
    have hgrad : (fun q => g.metricInner q (G q) (Y q)) = Y.dir u := by
      funext q
      exact MorganTianLib.metricInner_gradientField_eq_dir g hu Y q
    have hcompat := hLC.2 Y G Y p
    rw [hgrad] at hcompat
    rw [MorganTianLib.metricInner_gradientField_eq_dir g hu
      (nabla.cov Y Y) p] at hcompat
    unfold MorganTianLib.hessian
    linarith
  have hcovXXdir :
      -(X.dir (X.dir u) p) + (nabla.cov X X).dir u p =
        -MorganTianLib.hessian nabla u X X p := by
    unfold MorganTianLib.hessian
    ring
  have hcovAxx :
      g.metricInner p ((nabla.cov Y (A X X)) p) (Y p) =
        2 * a * d - b * Y.dir (fun q => g.metricInner q (X q) (X q)) p -
          g.metricInner p ((nabla.cov Y G) p) (Y p) := by
    change g.metricInner p
      ((nabla.cov Y (conformalCorrection g u hu X X)) p) (Y p) = _
    rw [PoincareConjecture.ParallelImplementation.ConformalCorrectionDerivative.cov_conformalCorrection]
    simp only [G, a, b, d, g.metricInner_add_left, g.metricInner_sub_left,
      g.metricInner_smul_left, hXY, hX, hGY]
    ring
  have hcovAYX :
      g.metricInner p ((nabla.cov X (A Y X)) p) (Y p) =
        b * e + X.dir (X.dir u) p + a * f -
          b * X.dir (fun q => g.metricInner q (Y q) (X q)) p := by
    change g.metricInner p
      ((nabla.cov X (conformalCorrection g u hu Y X)) p) (Y p) = _
    rw [PoincareConjecture.ParallelImplementation.ConformalCorrectionDerivative.cov_conformalCorrection]
    simp only [G, a, b, e, f, g.metricInner_add_left, g.metricInner_sub_left,
      g.metricInner_smul_left, hYX, hXY, hY, hGY]
    ring
  have hcommXX : g.metricInner p (Y p) ((nabla.cov X X) p) = e := by
    rw [g.metricInner_comm p (Y p) ((nabla.cov X X) p)]
  have hcommYX : g.metricInner p (X p) ((nabla.cov Y X) p) = l := by
    rw [g.metricInner_comm p (X p) ((nabla.cov Y X) p)]
  have hA3 :
      g.metricInner p (A Y (nabla.cov X X) p) (Y p) =
        (nabla.cov X X).dir u p := by
    change g.metricInner p
      (conformalCorrection g u hu Y (nabla.cov X X) p) (Y p) = _
    rw [PoincareConjecture.ParallelImplementation.ConformalConnection.conformalCorrection_apply]
    simp only [G, b, g.metricInner_add_left, g.metricInner_sub_left,
      g.metricInner_smul_left, hY, hGY, hcommXX, e]
    ring
  have hA4 :
      g.metricInner p (A X (nabla.cov Y X) p) (Y p) = a * d - b * l := by
    change g.metricInner p
      (conformalCorrection g u hu X (nabla.cov Y X) p) (Y p) = _
    rw [PoincareConjecture.ParallelImplementation.ConformalConnection.conformalCorrection_apply]
    simp only [G, a, b, d, g.metricInner_add_left, g.metricInner_sub_left,
      g.metricInner_smul_left, hXY, hGY, hcommYX]
    ring
  have hA5 :
      g.metricInner p (A (bracketField Y X) X p) (Y p) =
        a * g.metricInner p ((bracketField Y X) p) (Y p) -
          b * g.metricInner p ((bracketField Y X) p) (X p) := by
    change g.metricInner p
      (conformalCorrection g u hu (bracketField Y X) X p) (Y p) = _
    rw [PoincareConjecture.ParallelImplementation.ConformalConnection.conformalCorrection_apply]
    simp only [g.metricInner_add_left, g.metricInner_sub_left,
      g.metricInner_smul_left, a, b, G, hXY, hGY]
    ring
  have hderiv :
      g.metricInner p
        ((nabla.cov Y (A X X) - nabla.cov X (A Y X) +
          A Y (nabla.cov X X) - A X (nabla.cov Y X) -
          A (bracketField Y X) X) p) (Y p) =
        -MorganTianLib.hessian nabla u Y Y p -
          MorganTianLib.hessian nabla u X X p := by
    simp only [SmoothVectorField.sub_apply, SmoothVectorField.add_apply,
      g.metricInner_sub_left, g.metricInner_add_left]
    rw [hcovAxx, hcovAYX, hA3, hA4, hA5, hmetricXX, hmetricYX,
      hbrY, hbrX, hGYcov]
    linear_combination hcovXXdir
  have hquad :=
    PoincareConjecture.ParallelImplementation.ConformalQuadraticContraction.quadratic_conformal_correction
      g u hu Y X p hY hX (by rw [g.metricInner_comm p (Y p) (X p)]; exact hXY)
  have hcurv :
      g.metricInner p
        ((MorganTianLib.riemannCurvature
          (conformalMetric g u hu).leviCivitaConnection Y X X) p) (Y p) =
        g.metricInner p ((MorganTianLib.riemannCurvature nabla Y X X) p) (Y p) -
          MorganTianLib.hessian nabla u Y Y p -
          MorganTianLib.hessian nabla u X X p +
          (X.dir u p) ^ 2 + (Y.dir u p) ^ 2 -
          g.metricInner p (G p) (G p) := by
    have hderiv' := hderiv
    simp only [nabla, A, SmoothVectorField.sub_apply, SmoothVectorField.add_apply,
      g.metricInner_sub_left, g.metricInner_add_left] at hderiv'
    have hquad' := hquad
    simp only [SmoothVectorField.sub_apply, g.metricInner_sub_left] at hquad'
    rw [PoincareConjecture.ParallelImplementation.ConformalCurvatureExpansion.riemannCurvature_conformal_expansion]
    simp only [SmoothVectorField.sub_apply, SmoothVectorField.add_apply,
      g.metricInner_sub_left, g.metricInner_add_left]
    linear_combination hderiv' + hquad'
  have hbrskew : bracketField X Y = -bracketField Y X := by
    apply SmoothVectorField.ext
    intro q
    have hxy : (bracketField X Y) q =
        (nabla.cov X Y) q - (nabla.cov Y X) q := by
      simpa [Riemannian.bracketField] using (hLC.1 X Y q).symm
    have hyx : (bracketField Y X) q =
        (nabla.cov Y X) q - (nabla.cov X Y) q := by
      simpa [Riemannian.bracketField] using (hLC.1 Y X q).symm
    rw [hxy]
    simp only [SmoothVectorField.neg_apply]
    rw [hyx]
    module
  have hcovNeg (conn : AffineConnection I M) (U V : SmoothVectorField I M) :
      conn.cov (-U) V = -conn.cov U V := by
    have hneg : SmoothVectorField.smul (fun _ : M => (-1 : ℝ))
        contMDiff_const U = -U := by
      ext q
      simp [SmoothVectorField.smul_apply]
    rw [← hneg, conn.smul_left]
    ext q
    simp [SmoothVectorField.smul_apply]
  have hnumOld :
      MorganTianLib.curvatureFormAt g g.leviCivitaConnection p
          (X p) (Y p) (X p) (Y p) =
        g.metricInner p
          ((MorganTianLib.riemannCurvature g.leviCivitaConnection Y X X) p) (Y p) := by
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    calc
      _ = g.leviCivitaConnection.curvatureForm g X Y X Y p :=
        MorganTianLib.curvatureFormAt_eq g g.leviCivitaConnection X Y X Y p
      _ = _ := by
        simp [AffineConnection.curvatureForm, AffineConnection.curvature,
          MorganTianLib.riemannCurvature]
        rw [hbrskew]
        rw [hcovNeg g.leviCivitaConnection (bracketField Y X) X]
        simp [SmoothVectorField.neg_apply]
        ring
  have hnumNew :
      MorganTianLib.curvatureFormAt (conformalMetric g u hu)
          (conformalMetric g u hu).leviCivitaConnection p
          (X p) (Y p) (X p) (Y p) =
        (conformalMetric g u hu).metricInner p
          ((MorganTianLib.riemannCurvature
            (conformalMetric g u hu).leviCivitaConnection Y X X) p) (Y p) := by
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(conformalMetric g u hu).toRiemannianMetric⟩
    calc
      _ = (conformalMetric g u hu).leviCivitaConnection.curvatureForm
            (conformalMetric g u hu) X Y X Y p :=
        MorganTianLib.curvatureFormAt_eq (conformalMetric g u hu)
          (conformalMetric g u hu).leviCivitaConnection X Y X Y p
      _ = _ := by
        simp [AffineConnection.curvatureForm, AffineConnection.curvature,
          MorganTianLib.riemannCurvature]
        rw [hbrskew]
        rw [hcovNeg (conformalMetric g u hu).leviCivitaConnection
          (bracketField Y X) X]
        simp [SmoothVectorField.neg_apply]
        ring
  have hnumScale :
      MorganTianLib.curvatureFormAt (conformalMetric g u hu)
          (conformalMetric g u hu).leviCivitaConnection p
          (X p) (Y p) (X p) (Y p) =
        Real.exp (2 * u p) *
          (MorganTianLib.curvatureFormAt g g.leviCivitaConnection p
              (X p) (Y p) (X p) (Y p) -
            MorganTianLib.hessian g.leviCivitaConnection u Y Y p -
            MorganTianLib.hessian g.leviCivitaConnection u X X p +
            (X.dir u p) ^ 2 + (Y.dir u p) ^ 2 -
            g.metricInner p (G p) (G p)) := by
    rw [hnumNew, conformalMetric_metricInner g hu p]
    rw [hcurv, ← hnumOld]
    simp [conformalFactor, nabla]
  have hdenOld := by
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hxx : inner ℝ (X p) (X p) = 1 := by
      change g.metricInner p (X p) (X p) = 1
      exact hX
    have hyy : inner ℝ (Y p) (Y p) = 1 := by
      change g.metricInner p (Y p) (Y p) = 1
      exact hY
    have hxy : inner ℝ (X p) (Y p) = 0 := by
      change g.metricInner p (X p) (Y p) = 0
      exact hXY
    change Riemannian.wedgeSq (X p) (Y p) = 1
    unfold Riemannian.wedgeSq
    rw [hxx, hyy, hxy]
    norm_num
  have hdenNew := by
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(conformalMetric g u hu).toRiemannianMetric⟩
    have hxx : inner ℝ (X p) (X p) = Real.exp (2 * u p) := by
      have hm : (conformalMetric g u hu).metricInner p (X p) (X p) =
          Real.exp (2 * u p) := by
        rw [conformalMetric_metricInner g hu p, hX, conformalFactor]
        ring
      change (conformalMetric g u hu).metricInner p (X p) (X p) = _
      exact hm
    have hyy : inner ℝ (Y p) (Y p) = Real.exp (2 * u p) := by
      have hm : (conformalMetric g u hu).metricInner p (Y p) (Y p) =
          Real.exp (2 * u p) := by
        rw [conformalMetric_metricInner g hu p, hY, conformalFactor]
        ring
      change (conformalMetric g u hu).metricInner p (Y p) (Y p) = _
      exact hm
    have hxy : inner ℝ (X p) (Y p) = 0 := by
      have hm : (conformalMetric g u hu).metricInner p (X p) (Y p) = 0 := by
        rw [conformalMetric_metricInner g hu p, hXY]
        simp [conformalFactor]
      change (conformalMetric g u hu).metricInner p (X p) (Y p) = 0
      exact hm
    change Riemannian.wedgeSq (X p) (Y p) = Real.exp (4 * u p)
    unfold Riemannian.wedgeSq
    rw [hxx, hyy, hxy]
    have hexp : Real.exp (2 * u p) * Real.exp (2 * u p) =
        Real.exp (4 * u p) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  unfold MorganTianLib.sectionalCurvatureAt Riemannian.sectionalCurvature
  rw [hnumScale, hdenNew, hdenOld]
  simp only [div_one]
  have hexp : Real.exp (2 * u p) / Real.exp (4 * u p) =
      Real.exp (-2 * u p) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [show Real.exp (2 * u p) *
      (MorganTianLib.curvatureFormAt g g.leviCivitaConnection p
          (X p) (Y p) (X p) (Y p) -
        MorganTianLib.hessian g.leviCivitaConnection u Y Y p -
        MorganTianLib.hessian g.leviCivitaConnection u X X p +
        (X.dir u p) ^ 2 + (Y.dir u p) ^ 2 -
        g.metricInner p (G p) (G p)) / Real.exp (4 * u p) =
      (Real.exp (2 * u p) / Real.exp (4 * u p)) *
        (MorganTianLib.curvatureFormAt g g.leviCivitaConnection p
            (X p) (Y p) (X p) (Y p) -
          MorganTianLib.hessian g.leviCivitaConnection u Y Y p -
          MorganTianLib.hessian g.leviCivitaConnection u X X p +
          (X.dir u p) ^ 2 + (Y.dir u p) ^ 2 -
          g.metricInner p (G p) (G p)) by ring]
  rw [hexp]
  ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ConformalSectionalRecovered
