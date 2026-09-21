import MorganTianLib.Ch02.SurgeryCap.SphereFieldAlgebra
import MorganTianLib.Ch02.SurgeryCap.SphereMetricPairing
import MorganTianLib.Ch02.SurgeryCap.SphereInnerDerivative
open Set Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
noncomputable section
namespace MorganTianLib.SurgeryCap
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** The actual sphere Levi-Civita derivative is tangential ambient differentiation. -/
theorem sphereAmbientField_canonical_cov
    (X Y : SmoothVectorField (𝓡 2) EpsilonNeckSphere) (p : EpsilonNeckSphere) :
    sphereAmbientField (unitRoundSphereMetric.leviCivitaConnection.cov X Y) p =
      mvfderiv (𝓡 2) (sphereAmbientField Y) p (X p) +
        unitRoundSphereMetric.metricInner p (X p) (Y p) • (p : E3) := by
/- SWARM_PROOF_BEGIN -/
  letI : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  have hfields := sphereAmbientField_smooth_tangent_bracket
  have hsmooth : ∀ Z : SmoothVectorField (𝓡 2) EpsilonNeckSphere,
      ContMDiff (𝓡 2) (𝓡 3) ∞ (sphereAmbientField Z) := hfields.1
  have htangent : ∀ (Z : SmoothVectorField (𝓡 2) EpsilonNeckSphere)
      (q : EpsilonNeckSphere),
      inner ℝ (q : E3) (sphereAmbientField Z q) = 0 := hfields.2.1
  have hbracket := hfields.2.2
  have hLC : unitRoundSphereMetric.leviCivitaConnection.IsLeviCivita
      unitRoundSphereMetric :=
    unitRoundSphereMetric.leviCivitaConnection.isLeviCivita_of_koszulDual
      unitRoundSphereMetric
      (fun A B C q => unitRoundSphereMetric.koszulDualSection_dual A B C q)
  have hmetric (A B : SmoothVectorField (𝓡 2) EpsilonNeckSphere) :
      unitRoundSphereMetric.metricInner p (A p) (B p) =
        inner ℝ (sphereAmbientField A p) (sphereAmbientField B p) :=
    sphere_metricInner_eq_ambient A B p
  have hdir (A B C : SmoothVectorField (𝓡 2) EpsilonNeckSphere) :
      A.dir (fun q => unitRoundSphereMetric.metricInner q (B q) (C q)) p =
        inner ℝ (mvfderiv (𝓡 2) (sphereAmbientField B) p (A p))
            (sphereAmbientField C p) +
          inner ℝ (sphereAmbientField B p)
            (mvfderiv (𝓡 2) (sphereAmbientField C) p (A p)) := by
    have hfun :
        (fun q => unitRoundSphereMetric.metricInner q (B q) (C q)) =
          (fun q => inner ℝ (sphereAmbientField B q)
            (sphereAmbientField C q)) := by
      funext q
      exact sphere_metricInner_eq_ambient B C q
    rw [hfun]
    exact sphere_dir_inner_rule A (sphereAmbientField B)
      (sphereAmbientField C) (hsmooth B) (hsmooth C) p
  have hbr (A B C : SmoothVectorField (𝓡 2) EpsilonNeckSphere) :
      unitRoundSphereMetric.metricInner p (DCLieBracket A B p) (C p) =
        inner ℝ
          (mvfderiv (𝓡 2) (sphereAmbientField B) p (A p) -
            mvfderiv (𝓡 2) (sphereAmbientField A) p (B p))
          (sphereAmbientField C p) := by
    change unitRoundSphereMetric.metricInner p ((bracketField A B) p) (C p) = _
    rw [sphere_metricInner_eq_ambient (bracketField A B) C p,
      hbracket A B p, inner_sub_left]
  have hnormal (A B : SmoothVectorField (𝓡 2) EpsilonNeckSphere) :
      inner ℝ (p : E3)
          (mvfderiv (𝓡 2) (sphereAmbientField B) p (A p)) +
        inner ℝ (sphereAmbientField A p) (sphereAmbientField B p) = 0 := by
    have hzero :
        (fun q : EpsilonNeckSphere =>
          inner ℝ (q : E3) (sphereAmbientField B q)) =
          (fun _ => 0) := by
      funext q
      exact htangent B q
    have hrule := sphere_dir_inner_rule A (Subtype.val : EpsilonNeckSphere → E3)
      (sphereAmbientField B) (contMDiff_coe_sphere (E := E3) (n := 2))
      (hsmooth B) p
    rw [hzero] at hrule
    rw [SmoothVectorField.dir, mfderiv_const] at hrule
    change 0 = inner ℝ (sphereAmbientField A p) (sphereAmbientField B p) +
      inner ℝ (p : E3)
        (mvfderiv (𝓡 2) (sphereAmbientField B) p (A p)) at hrule
    linarith
  have hpunit : inner ℝ (p : E3) (p : E3) = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have hpnorm : ‖(p : E3)‖ = 1 := by simpa using p.property
    rw [hpnorm]
    norm_num
  have hRHS (Z : SmoothVectorField (𝓡 2) EpsilonNeckSphere) :
      unitRoundSphereMetric.koszulRHS Y X Z p =
        2 * inner ℝ
          (mvfderiv (𝓡 2) (sphereAmbientField Y) p (X p) +
            unitRoundSphereMetric.metricInner p (X p) (Y p) • (p : E3))
          (sphereAmbientField Z p) := by
    unfold RiemannianMetric.koszulRHS
    rw [hdir Y X Z, hdir X Z Y, hdir Z Y X,
      hbr X Z Y, hbr Y Z X, hbr Y X Z]
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
    rw [htangent Z p]
    simp only [mul_zero, add_zero]
    simp only [real_inner_comm]
    ring
  have hpairs (Z : SmoothVectorField (𝓡 2) EpsilonNeckSphere) :
      inner ℝ (sphereAmbientField (unitRoundSphereMetric.leviCivitaConnection.cov X Y) p)
          (sphereAmbientField Z p) =
        inner ℝ
          (mvfderiv (𝓡 2) (sphereAmbientField Y) p (X p) +
            unitRoundSphereMetric.metricInner p (X p) (Y p) • (p : E3))
          (sphereAmbientField Z p) := by
    have hleft :
        2 * inner ℝ
            (sphereAmbientField
              (unitRoundSphereMetric.leviCivitaConnection.cov X Y) p)
            (sphereAmbientField Z p) =
          unitRoundSphereMetric.koszulRHS Y X Z p := by
      rw [← sphere_metricInner_eq_ambient
        (unitRoundSphereMetric.leviCivitaConnection.cov X Y) Z p]
      rw [unitRoundSphereMetric.metricInner_comm p
        (((unitRoundSphereMetric.leviCivitaConnection.cov X Y) p)) (Z p)]
      exact AffineConnection.koszul_formula unitRoundSphereMetric
        unitRoundSphereMetric.leviCivitaConnection
        hLC.1 hLC.2
        Y X Z p
    have hright := hRHS Z
    linarith
  let delta : E3 :=
    sphereAmbientField (unitRoundSphereMetric.leviCivitaConnection.cov X Y) p -
      (mvfderiv (𝓡 2) (sphereAmbientField Y) p (X p) +
        unitRoundSphereMetric.metricInner p (X p) (Y p) • (p : E3))
  have hnormal_rhs :
      inner ℝ (p : E3)
          (mvfderiv (𝓡 2) (sphereAmbientField Y) p (X p) +
            unitRoundSphereMetric.metricInner p (X p) (Y p) • (p : E3)) = 0 := by
    rw [inner_add_right, real_inner_smul_right, hpunit,
      hmetric X Y]
    have h := hnormal X Y
    linarith
  have hdelta_normal : inner ℝ (p : E3) delta = 0 := by
    change inner ℝ (p : E3)
        (sphereAmbientField (unitRoundSphereMetric.leviCivitaConnection.cov X Y) p -
          (mvfderiv (𝓡 2) (sphereAmbientField Y) p (X p) +
            unitRoundSphereMetric.metricInner p (X p) (Y p) • (p : E3))) = 0
    rw [inner_sub_right,
      htangent (unitRoundSphereMetric.leviCivitaConnection.cov X Y) p]
    rw [zero_sub]
    exact neg_eq_zero.mpr hnormal_rhs
  have hdelta_orth : delta ∈ (ℝ ∙ (p : E3))ᗮ := by
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hdelta_normal
  have hdelta_range : delta ∈
      (mfderiv (𝓡 2) 𝓘(ℝ, E3)
        ((↑) : EpsilonNeckSphere → E3) p).range := by
    rw [range_mfderiv_coe_sphere (E := E3) (n := 2) p]
    exact hdelta_orth
  obtain ⟨v, hv⟩ := hdelta_range
  obtain ⟨W, hW⟩ := exists_smoothVectorField_eq (I := 𝓡 2) p v
  have hWdelta : sphereAmbientField W p = delta := by
    unfold sphereAmbientField
    rw [hW]
    exact hv
  have hdelta_self : inner ℝ delta delta = 0 := by
    have hpair := hpairs W
    rw [hWdelta] at hpair
    change inner ℝ
        (sphereAmbientField (unitRoundSphereMetric.leviCivitaConnection.cov X Y) p -
          (mvfderiv (𝓡 2) (sphereAmbientField Y) p (X p) +
            unitRoundSphereMetric.metricInner p (X p) (Y p) • (p : E3))) delta = 0
    rw [inner_sub_left]
    exact sub_eq_zero.mpr hpair
  have hdelta_zero : delta = 0 := inner_self_eq_zero.mp hdelta_self
  dsimp [delta] at hdelta_zero
  exact sub_eq_zero.mp hdelta_zero
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
