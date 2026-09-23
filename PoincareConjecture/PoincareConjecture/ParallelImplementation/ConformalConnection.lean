import MorganTianLib.Ch01.LeviCivita
import MorganTianLib.Ch02.Gradient
import MorganTianLib.Ch02.SurgeryInterpolation.WeightedMetric

open Riemannian
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareConjecture.ParallelImplementation.ConformalConnection

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The actual positive pointwise metric factor for the conformal change `exp (2u) g`. -/
def conformalFactor (u : M → ℝ) : M → ℝ := fun p => Real.exp (2 * u p)

theorem conformalFactor_pos (u : M → ℝ) (p : M) : 0 < conformalFactor u p :=
  Real.exp_pos _

theorem conformalFactor_contMDiff {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (conformalFactor u) := by
  change ContMDiff I 𝓘(ℝ, ℝ) ∞ (Real.exp ∘ fun p => 2 * u p)
  exact Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul hu)

private theorem dir_exp (X : SmoothVectorField I M) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (p : M) :
    X.dir (fun q => Real.exp (u q)) p = Real.exp (u p) * X.dir u p := by
  have hExp (x : ℝ) :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.exp x =
        (Real.exp x) • ContinuousLinearMap.id ℝ ℝ := by
    have hclm : ContinuousLinearMap.toSpanSingleton ℝ (Real.exp x) =
        (Real.exp x) • ContinuousLinearMap.id ℝ ℝ := by
      ext
      simp [ContinuousLinearMap.toSpanSingleton_apply]
    have he : HasFDerivAt Real.exp
        ((Real.exp x) • ContinuousLinearMap.id ℝ ℝ) x := by
      rw [← hclm]
      exact (Real.hasDerivAt_exp x).hasFDerivAt
    rw [mfderiv_eq_fderiv, he.fderiv]
  have hexp : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.exp :=
    Real.contDiff_exp.contMDiff
  change mfderiv I 𝓘(ℝ, ℝ) (Real.exp ∘ u) p (X p) = _
  rw [mfderiv_comp_apply p (hexp.mdifferentiableAt (by simp))
    (hu.mdifferentiableAt (by simp)) (X p), hExp]
  change Real.exp (u p) * (ContinuousLinearMap.id ℝ ℝ)
    (mfderiv I 𝓘(ℝ, ℝ) u p (X p)) = _
  rfl

theorem conformalFactor_dir (X : SmoothVectorField I M) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (p : M) :
    X.dir (conformalFactor u) p =
      2 * conformalFactor u p * X.dir u p := by
  have he : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => Real.exp (u q)) :=
    Real.contDiff_exp.contMDiff.comp hu
  have hprod := X.dir_mul p (he.mdifferentiableAt (by simp))
    (he.mdifferentiableAt (by simp))
  calc
    X.dir (conformalFactor u) p =
        X.dir (fun q => Real.exp (u q) * Real.exp (u q)) p := by
          congr 1
          funext q
          simp [conformalFactor, two_mul, Real.exp_add]
    _ = Real.exp (u p) * X.dir (fun q => Real.exp (u q)) p +
        Real.exp (u p) * X.dir (fun q => Real.exp (u q)) p := by
          rw [hprod]
    _ = 2 * conformalFactor u p * X.dir u p := by
          rw [dir_exp X hu p, conformalFactor]
          have hsq : Real.exp (u p) * Real.exp (u p) = Real.exp (2 * u p) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [← hsq]
          ring

private theorem conformalMetric_exists (g : RiemannianMetric I M) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ∃ g' : RiemannianMetric I M, ∀ p v w,
      g'.metricInner p v w = conformalFactor u p * g.metricInner p v w := by
  obtain ⟨g', hg'⟩ := MorganTianLib.SurgeryInterpolation.exists_weighted_riemannianMetric
    g g (conformalFactor u) (fun _ => 0) (conformalFactor_contMDiff hu)
    contMDiff_const (fun p => (conformalFactor_pos u p).le) (fun _ => le_rfl)
    (fun p => by simpa using conformalFactor_pos u p)
  refine ⟨g', ?_⟩
  intro p v w
  rw [hg']
  simp

/-- **Math.** The pointwise conformal metric `g̃ = exp (2u) g`, built as an actual smooth
positive-definite Riemannian metric. -/
noncomputable def conformalMetric (g : RiemannianMetric I M) (u : M → ℝ)
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) : RiemannianMetric I M :=
  Classical.choose (conformalMetric_exists g hu)

theorem conformalMetric_metricInner (g : RiemannianMetric I M) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (p : M) (v w : TangentSpace I p) :
    (conformalMetric g u hu).metricInner p v w =
      conformalFactor u p * g.metricInner p v w :=
  (Classical.choose_spec (conformalMetric_exists g hu)) p v w

/-- **Math.** The symmetric tensor correction for the Levi-Civita connection under the
conformal metric `exp (2u) g`. -/
noncomputable def conformalCorrection (g : RiemannianMetric I M) (u : M → ℝ)
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (X Y : SmoothVectorField I M) :
    SmoothVectorField I M :=
  (SmoothVectorField.smul (X.dir u) (X.dir_contMDiff hu) Y
    + SmoothVectorField.smul (Y.dir u) (Y.dir_contMDiff hu) X)
    - SmoothVectorField.smul (fun p => g.metricInner p (X p) (Y p))
        (g.metricInner_field_contMDiff X Y) (MorganTianLib.gradientField g u hu)

@[simp] theorem conformalCorrection_apply (g : RiemannianMetric I M) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (X Y : SmoothVectorField I M) (p : M) :
    conformalCorrection g u hu X Y p =
      (X.dir u p) • Y p + (Y.dir u p) • X p -
        g.metricInner p (X p) (Y p) • MorganTianLib.gradientField g u hu p := by
  simp [conformalCorrection]

private theorem conformalCorrection_add_left (g : RiemannianMetric I M) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (X Y Z : SmoothVectorField I M) :
    conformalCorrection g u hu (X + Y) Z =
      conformalCorrection g u hu X Z + conformalCorrection g u hu Y Z := by
  apply SmoothVectorField.ext
  intro p
  simp only [conformalCorrection_apply, SmoothVectorField.add_apply,
    SmoothVectorField.dir_add_field, g.metricInner_add_left]
  module

private theorem conformalCorrection_smul_left (g : RiemannianMetric I M) {u f : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y : SmoothVectorField I M) :
    conformalCorrection g u hu (SmoothVectorField.smul f hf X) Y =
      SmoothVectorField.smul f hf (conformalCorrection g u hu X Y) := by
  apply SmoothVectorField.ext
  intro p
  simp only [conformalCorrection_apply, SmoothVectorField.smul_apply,
    SmoothVectorField.dir_smul_field, g.metricInner_smul_left]
  module

private theorem conformalCorrection_add_right (g : RiemannianMetric I M) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (X Y Z : SmoothVectorField I M) :
    conformalCorrection g u hu X (Y + Z) =
      conformalCorrection g u hu X Y + conformalCorrection g u hu X Z := by
  apply SmoothVectorField.ext
  intro p
  simp only [conformalCorrection_apply, SmoothVectorField.add_apply,
    SmoothVectorField.dir_add_field, g.metricInner_add_right]
  module

private theorem conformalCorrection_smul_right (g : RiemannianMetric I M) {u f : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y : SmoothVectorField I M) (p : M) :
    conformalCorrection g u hu X (SmoothVectorField.smul f hf Y) p =
      f p • conformalCorrection g u hu X Y p := by
  simp only [conformalCorrection_apply, SmoothVectorField.smul_apply,
    SmoothVectorField.dir_smul_field, g.metricInner_smul_right]
  module

/-- **Math.** The actual affine connection formed from the Levi-Civita connection of `g`
and its conformal correction tensor. -/
noncomputable def conformalConnection (g : RiemannianMetric I M) (u : M → ℝ)
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (nabla : AffineConnection I M) :
    AffineConnection I M :=
  AffineConnection.ofIsAffineConnectionMap
    (fun X Y => nabla.cov X Y + conformalCorrection g u hu X Y) <| by
    have hbase := nabla.isAffineConnectionMap
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro X Y Z
      apply SmoothVectorField.ext
      intro p
      change (nabla.cov (X + Y) Z + conformalCorrection g u hu (X + Y) Z) p = _
      rw [hbase.1 X Y Z, conformalCorrection_add_left]
      simp only [SmoothVectorField.add_apply]
      abel
    · intro f hf X Y
      apply SmoothVectorField.ext
      intro p
      change (nabla.cov (SmoothVectorField.smul f hf X) Y +
          conformalCorrection g u hu (SmoothVectorField.smul f hf X) Y) p = _
      rw [hbase.2.1 f hf X Y, conformalCorrection_smul_left]
      simp only [SmoothVectorField.smul_apply, SmoothVectorField.add_apply]
      module
    · intro X Y Z
      apply SmoothVectorField.ext
      intro p
      change (nabla.cov X (Y + Z) + conformalCorrection g u hu X (Y + Z)) p = _
      rw [hbase.2.2.1 X Y Z, conformalCorrection_add_right]
      simp only [SmoothVectorField.add_apply]
      abel
    · intro f hf X Y p
      simp only [SmoothVectorField.add_apply, conformalCorrection_smul_right]
      rw [hbase.2.2.2 f hf X Y p]
      module

@[simp] theorem conformalConnection_cov_apply (g : RiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (nabla : AffineConnection I M) (X Y : SmoothVectorField I M) (p : M) :
    (conformalConnection g u hu nabla).cov X Y p =
      (nabla.cov X Y) p + (X.dir u p) • Y p + (Y.dir u p) • X p -
        g.metricInner p (X p) (Y p) • MorganTianLib.gradientField g u hu p := by
  change (nabla.cov X Y) p + conformalCorrection g u hu X Y p = _
  rw [conformalCorrection_apply]
  module

private theorem conformalCorrection_comm (g : RiemannianMetric I M) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (X Y : SmoothVectorField I M) :
    conformalCorrection g u hu X Y = conformalCorrection g u hu Y X := by
  apply SmoothVectorField.ext
  intro p
  rw [conformalCorrection_apply, conformalCorrection_apply,
    g.metricInner_comm p (X p) (Y p)]
  module

/-- **Math.** The connection correction is torsion-free and compatible with the genuine
conformal metric. Consequently it is the Levi-Civita connection of `exp (2u)g`.
No conformal connection or curvature formula is assumed. -/
theorem conformalConnection_isLeviCivita (g : RiemannianMetric I M) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) :
    (conformalConnection g u hu nabla).IsLeviCivita (conformalMetric g u hu) := by
  constructor
  · intro X Y p
    have hbase := hLC.1 X Y p
    rw [conformalConnection_cov_apply, conformalConnection_cov_apply,
      g.metricInner_comm p (X p) (Y p)]
    calc
      (nabla.cov X Y) p +
          (X.dir u p) • Y p + (Y.dir u p) • X p -
            g.metricInner p (Y p) (X p) • MorganTianLib.gradientField g u hu p -
        ((nabla.cov Y X) p + (Y.dir u p) • X p + (X.dir u p) • Y p -
            g.metricInner p (Y p) (X p) • MorganTianLib.gradientField g u hu p)
          = (nabla.cov X Y) p - (nabla.cov Y X) p := by module
      _ = DCLieBracket X Y p := hbase
  · intro X Y Z p
    have hpair : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun q => g.metricInner q (Y q) (Z q)) p :=
      g.metricInner_field_mdifferentiableAt Y Z p
    have hfactor : MDifferentiableAt I 𝓘(ℝ, ℝ) (conformalFactor u) p :=
      (conformalFactor_contMDiff hu).mdifferentiableAt (by simp)
    have hfun : (fun q => (conformalMetric g u hu).metricInner q (Y q) (Z q)) =
        (fun q => conformalFactor u q * g.metricInner q (Y q) (Z q)) := by
      funext q
      exact conformalMetric_metricInner g hu q (Y q) (Z q)
    have hgradZ := MorganTianLib.metricInner_gradientField_eq_dir g hu Z p
    have hgradY : g.metricInner p (Y p) (MorganTianLib.gradientField g u hu p) =
        Y.dir u p := by
      rw [g.metricInner_comm]
      exact MorganTianLib.metricInner_gradientField_eq_dir g hu Y p
    rw [hfun, X.dir_mul p hfactor hpair, conformalFactor_dir X hu p,
      hLC.2 X Y Z p, conformalConnection_cov_apply,
      conformalConnection_cov_apply (g := g) (hu := hu) (nabla := nabla) X Z p,
      conformalMetric_metricInner g hu p, conformalMetric_metricInner g hu p]
    simp only [g.metricInner_add_left, g.metricInner_sub_left,
      g.metricInner_smul_left, g.metricInner_add_right,
      g.metricInner_sub_right, g.metricInner_smul_right, hgradZ, hgradY]
    rw [g.metricInner_comm p (Y p) (X p)]
    ring

/-- **Math.** The Levi-Civita connection of the conformal metric has the classical
pointwise formula, with the gradient defined by the metric Riesz map. -/
theorem conformalMetric_leviCivitaConnection_cov (g : RiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (X Y : SmoothVectorField I M) (p : M) :
    ((conformalMetric g u hu).leviCivitaConnection.cov X Y) p =
      (g.leviCivitaConnection.cov X Y) p + (X.dir u p) • Y p +
        (Y.dir u p) • X p - g.metricInner p (X p) (Y p) •
          MorganTianLib.gradientField g u hu p := by
  have hbase : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y Z p => g.koszulDualSection_dual X Y Z p)
  have hnew := conformalConnection_isLeviCivita g hu g.leviCivitaConnection hbase
  have heq := AffineConnection.leviCivita_unique' (conformalMetric g u hu)
    (conformalConnection g u hu g.leviCivitaConnection)
    (conformalMetric g u hu).leviCivitaConnection hnew
    ((conformalMetric g u hu).leviCivitaConnection.isLeviCivita_of_koszulDual
      (conformalMetric g u hu)
      (fun X Y Z p => (conformalMetric g u hu).koszulDualSection_dual X Y Z p))
  have hcov := congrArg (fun n : AffineConnection I M => (n.cov X Y) p) heq
  rw [conformalConnection_cov_apply] at hcov
  exact hcov.symm

end PoincareConjecture.ParallelImplementation.ConformalConnection
