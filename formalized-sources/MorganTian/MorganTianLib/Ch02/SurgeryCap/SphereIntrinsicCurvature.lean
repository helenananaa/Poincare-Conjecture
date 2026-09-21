import MorganTianLib.Ch02.SurgeryCap.SphereAmbient
import MorganTianLib.Ch02.SurgeryCap.SphereInnerDerivative
import MorganTianLib.Ch02.SurgeryCap.SphereMetricPairing
import MorganTianLib.Ch02.SurgeryCap.SphereFieldAlgebra
import MorganTianLib.Ch02.SurgeryCap.SphereCovariantFormula
open Set Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
noncomputable section
namespace MorganTianLib.SurgeryCap
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Actual intrinsic constant curvature, with all inclusion and connection bridges proved. -/
theorem unitRoundSphereMetric_intrinsic_curvature_one :
    unitRoundSphereMetric.leviCivitaConnection.IsConstantCurvature
      unitRoundSphereMetric (1 : ℝ) := by
/- SWARM_PROOF_BEGIN -/
  letI : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  intro X Y Z W p
  have hfields := sphereAmbientField_smooth_tangent_bracket
  have hsmooth : ∀ V : SmoothVectorField (𝓡 2) EpsilonNeckSphere,
      ContMDiff (𝓡 2) (𝓡 3) ∞ (sphereAmbientField V) := hfields.1
  have hLC : unitRoundSphereMetric.leviCivitaConnection.IsLeviCivita
      unitRoundSphereMetric :=
    unitRoundSphereMetric.leviCivitaConnection.isLeviCivita_of_koszulDual
      unitRoundSphereMetric
      (fun A B C q => unitRoundSphereMetric.koszulDualSection_dual A B C q)
  have hcoord_val : ∀ i : Fin 3,
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
        (fun q : EpsilonNeckSphere => ((q : E3) i)) := by
    intro i
    let proj : E3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
    have hproj : ContMDiff (𝓡 2) 𝓘(ℝ, E3 →L[ℝ] ℝ) ∞
        (fun _ : EpsilonNeckSphere => proj) := contMDiff_const
    have hcoe : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞
        (Subtype.val : EpsilonNeckSphere → E3) :=
      contMDiff_coe_sphere (E := E3) (n := 2)
    simpa [proj] using hproj.clm_apply hcoe
  have hcoord_smooth : ∀ (V : SmoothVectorField (𝓡 2) EpsilonNeckSphere)
      (i : Fin 3),
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
        (fun q : EpsilonNeckSphere => (sphereAmbientField V q) i) := by
    intro V i
    let proj : E3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
    have hproj : ContMDiff (𝓡 2) 𝓘(ℝ, E3 →L[ℝ] ℝ) ∞
        (fun _ : EpsilonNeckSphere => proj) := contMDiff_const
    simpa [proj] using hproj.clm_apply (hsmooth V)
  have hcoord_apply (V : SmoothVectorField (𝓡 2) EpsilonNeckSphere)
      (i : Fin 3) :
      (sphereAmbientField V p) i =
        V.dir (fun q : EpsilonNeckSphere => ((q : E3) i)) p := by
    let proj : E3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
    have hp : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) proj (p : E3) := by
      exact (ContinuousLinearMap.hasMFDerivAt proj).mdifferentiableAt
    have hcoe : MDifferentiableAt (𝓡 2) (𝓡 3)
        (Subtype.val : EpsilonNeckSphere → E3) p := by
      exact (contMDiff_coe_sphere (E := E3) (n := 2)).mdifferentiableAt one_ne_zero
    have hcomp := mfderiv_comp p hp hcoe
    have hproj : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) proj (p : E3) = proj := by
      exact (ContinuousLinearMap.hasMFDerivAt proj).mfderiv
    have hfun : (fun q : EpsilonNeckSphere => ((q : E3) i)) =
        (proj : E3 → ℝ) ∘ (Subtype.val : EpsilonNeckSphere → E3) := by
      funext q
      simp [proj]
    unfold sphereAmbientField SmoothVectorField.dir
    rw [hfun, hcomp, hproj]
    rfl
  have hambient_apply (V A : SmoothVectorField (𝓡 2) EpsilonNeckSphere)
      (i : Fin 3) (q : EpsilonNeckSphere) :
      (mvfderiv (𝓡 2) (sphereAmbientField V) q (A q)) i =
        A.dir (fun r : EpsilonNeckSphere =>
          (sphereAmbientField V r) i) q := by
    let proj : E3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
    have hp : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) proj
        ((sphereAmbientField V) q) := by
      exact (ContinuousLinearMap.hasMFDerivAt proj).mdifferentiableAt
    have hF : MDifferentiableAt (𝓡 2) (𝓡 3)
        (sphereAmbientField V) q :=
      (hsmooth V).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp q hp hF
    have hproj : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) proj
        ((sphereAmbientField V) q) = proj := by
      exact (ContinuousLinearMap.hasMFDerivAt proj).mfderiv
    have hfun : (fun r : EpsilonNeckSphere =>
        ((sphereAmbientField V r) i)) =
        (proj : E3 → ℝ) ∘ (sphereAmbientField V) := by
      funext r
      simp [proj]
    unfold SmoothVectorField.dir
    rw [hfun, hcomp, hproj]
    rfl
  have hDfun (A V : SmoothVectorField (𝓡 2) EpsilonNeckSphere)
      (i : Fin 3) :
      (fun q : EpsilonNeckSphere =>
        (mvfderiv (𝓡 2) (sphereAmbientField V) q (A q)) i) =
        (fun q : EpsilonNeckSphere =>
          A.dir (fun r : EpsilonNeckSphere =>
            (sphereAmbientField V r) i) q) := by
    funext q
    exact hambient_apply V A i q
  have hcanonical (A B : SmoothVectorField (𝓡 2) EpsilonNeckSphere)
      (q : EpsilonNeckSphere) :
      sphereAmbientField
          (unitRoundSphereMetric.leviCivitaConnection.cov A B) q =
        mvfderiv (𝓡 2) (sphereAmbientField B) q (A q) +
          unitRoundSphereMetric.metricInner q (A q) (B q) • (q : E3) :=
    sphereAmbientField_canonical_cov A B q
  have hcov_deriv (A B C : SmoothVectorField (𝓡 2) EpsilonNeckSphere)
      (i : Fin 3) :
      (mvfderiv (𝓡 2)
          (sphereAmbientField
            (unitRoundSphereMetric.leviCivitaConnection.cov A B)) p (C p)) i =
        C.dir (fun q : EpsilonNeckSphere =>
          A.dir (fun r : EpsilonNeckSphere =>
            (sphereAmbientField B r) i) q) p +
          unitRoundSphereMetric.metricInner p (A p) (B p) *
            (sphereAmbientField C p) i +
          (p : E3) i *
            C.dir (fun q : EpsilonNeckSphere =>
              unitRoundSphereMetric.metricInner q (A q) (B q)) p := by
    have hDdiff : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ)
        (fun q : EpsilonNeckSphere =>
          (mvfderiv (𝓡 2) (sphereAmbientField B) q (A q)) i) p := by
      have hfun :
          (fun q : EpsilonNeckSphere =>
            (mvfderiv (𝓡 2) (sphereAmbientField B) q (A q)) i) =
            (fun q : EpsilonNeckSphere =>
              (sphereAmbientField
                (unitRoundSphereMetric.leviCivitaConnection.cov A B) q) i -
                unitRoundSphereMetric.metricInner q (A q) (B q) *
                  ((q : E3) i)) := by
        funext q
        rw [hcanonical A B q]
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      rw [hfun]
      exact
        ((hcoord_smooth
          (unitRoundSphereMetric.leviCivitaConnection.cov A B) i).mdifferentiableAt
          (by simp)).sub
          ((unitRoundSphereMetric.metricInner_field_mdifferentiableAt A B p).mul
            ((hcoord_val i).mdifferentiableAt (by simp)))
    have hprod : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ)
        (fun q : EpsilonNeckSphere =>
          unitRoundSphereMetric.metricInner q (A q) (B q) * ((q : E3) i)) p :=
      (unitRoundSphereMetric.metricInner_field_mdifferentiableAt A B p).mul
        ((hcoord_val i).mdifferentiableAt (by simp))
    rw [hambient_apply
      (unitRoundSphereMetric.leviCivitaConnection.cov A B) C i p]
    have hfun : (fun q : EpsilonNeckSphere =>
          (sphereAmbientField
            (unitRoundSphereMetric.leviCivitaConnection.cov A B) q) i) =
        (fun q : EpsilonNeckSphere =>
          (mvfderiv (𝓡 2) (sphereAmbientField B) q (A q)) i +
            unitRoundSphereMetric.metricInner q (A q) (B q) * ((q : E3) i)) := by
      funext q
      rw [hcanonical A B q]
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hfun, C.dir_add p hDdiff hprod,
      hDfun A B i, C.dir_mul p
        (unitRoundSphereMetric.metricInner_field_mdifferentiableAt A B p)
        ((hcoord_val i).mdifferentiableAt (by simp)),
      ← hcoord_apply C i]
    ring
  have hrad (A B C : SmoothVectorField (𝓡 2) EpsilonNeckSphere) :
      C.dir (fun q : EpsilonNeckSphere =>
          unitRoundSphereMetric.metricInner q (A q) (B q)) p -
        A.dir (fun q : EpsilonNeckSphere =>
          unitRoundSphereMetric.metricInner q (C q) (B q)) p +
        unitRoundSphereMetric.metricInner p (C p)
          ((unitRoundSphereMetric.leviCivitaConnection.cov A B) p) -
        unitRoundSphereMetric.metricInner p (A p)
          ((unitRoundSphereMetric.leviCivitaConnection.cov C B) p) +
        unitRoundSphereMetric.metricInner p (DCLieBracket A C p) (B p) = 0 := by
    have h1 := hLC.2 C A B p
    have h2 := hLC.2 A C B p
    have hbr' : unitRoundSphereMetric.metricInner p (DCLieBracket A C p) (B p) =
        unitRoundSphereMetric.metricInner p
            ((unitRoundSphereMetric.leviCivitaConnection.cov A C) p) (B p) -
          unitRoundSphereMetric.metricInner p
            ((unitRoundSphereMetric.leviCivitaConnection.cov C A) p) (B p) := by
      rw [← hLC.1 A C p, unitRoundSphereMetric.metricInner_sub_left]
    rw [h1, h2, hbr']
    rw [unitRoundSphereMetric.metricInner_comm p (A p)
      ((unitRoundSphereMetric.leviCivitaConnection.cov C B) p),
      unitRoundSphereMetric.metricInner_comm p (C p)
      ((unitRoundSphereMetric.leviCivitaConnection.cov A B) p)]
    ring
  have hcurv (A B C : SmoothVectorField (𝓡 2) EpsilonNeckSphere)
      (i : Fin 3) :
      (sphereAmbientField
        (unitRoundSphereMetric.leviCivitaConnection.curvature A B C) p) i =
        unitRoundSphereMetric.metricInner p (A p) (C p) *
            (sphereAmbientField B p) i -
          unitRoundSphereMetric.metricInner p (B p) (C p) *
            (sphereAmbientField A p) i := by
    have hcurvS :
        sphereAmbientField
            (unitRoundSphereMetric.leviCivitaConnection.curvature A B C) p =
          sphereAmbientField
              (unitRoundSphereMetric.leviCivitaConnection.cov B
                (unitRoundSphereMetric.leviCivitaConnection.cov A C)) p -
            sphereAmbientField
              (unitRoundSphereMetric.leviCivitaConnection.cov A
                (unitRoundSphereMetric.leviCivitaConnection.cov B C)) p +
            sphereAmbientField
              (unitRoundSphereMetric.leviCivitaConnection.cov
                (bracketField A B) C) p := by
      unfold sphereAmbientField
      rw [AffineConnection.curvature_apply]
      rw [map_add, map_sub]
    have hcoord := congrArg (fun v : E3 => v i) hcurvS
    rw [hcanonical B
        (unitRoundSphereMetric.leviCivitaConnection.cov A C) p,
      hcanonical A
        (unitRoundSphereMetric.leviCivitaConnection.cov B C) p,
      hcanonical (bracketField A B) C p] at hcoord
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply] at hcoord
    rw [hcov_deriv A C B i, hcov_deriv B C A i,
      hambient_apply C (bracketField A B) i p] at hcoord
    have hsecond :
        B.dir (fun q : EpsilonNeckSphere =>
            A.dir (fun r : EpsilonNeckSphere =>
              (sphereAmbientField C r) i) q) p -
          A.dir (fun q : EpsilonNeckSphere =>
            B.dir (fun r : EpsilonNeckSphere =>
              (sphereAmbientField C r) i) q) p +
          (bracketField A B).dir (fun q : EpsilonNeckSphere =>
            (sphereAmbientField C q) i) p = 0 := by
      rw [bracketField_dir A B (hcoord_smooth C i) p]
      ring
    have hrad'' := hrad A C B
    simp only [smul_eq_mul] at hcoord
    rw [bracketField_apply] at hcoord
    linear_combination hcoord + hsecond + (p : E3) i * hrad''
  have hcurv_vec :
      sphereAmbientField
          (unitRoundSphereMetric.leviCivitaConnection.curvature X Y Z) p =
        unitRoundSphereMetric.metricInner p (X p) (Z p) •
            sphereAmbientField Y p -
          unitRoundSphereMetric.metricInner p (Y p) (Z p) •
            sphereAmbientField X p := by
    ext i
    rw [PiLp.sub_apply, PiLp.smul_apply, PiLp.smul_apply]
    exact hcurv X Y Z i
  rw [sphere_metricInner_eq_ambient
      (unitRoundSphereMetric.leviCivitaConnection.curvature X Y Z) W p,
    hcurv_vec, inner_sub_left]
  simp only [real_inner_smul_left]
  rw [
    ← sphere_metricInner_eq_ambient Y W p,
    ← sphere_metricInner_eq_ambient X W p]
  ring
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
