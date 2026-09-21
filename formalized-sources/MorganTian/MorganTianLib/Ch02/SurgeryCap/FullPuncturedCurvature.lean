import MorganTianLib.Ch02.SurgeryCap.ProfileCoefficientControl
import MorganTianLib.Ch02.SurgeryCap.GeneralPlaneCurvature
import MorganTianLib.Ch02.SurgeryCap.SphereIntrinsicCurvature
import MorganTianLib.Ch02.SurgeryCap.RadialSectional
import DoCarmoLib.Riemannian.Connection.CurvaturePointwise
open Set Riemannian
open scoped ContDiff Manifold Topology
noncomputable section
namespace MorganTianLib.SurgeryCap
set_option maxHeartbeats 800000 in
/-- **Math.** Nonnegative and uniformly bounded sectional curvature of the
actual punctured cap, for all smooth fields and all positive-radius points. -/
theorem RoundCapProfile.punctured_curvature_nonneg_bounded (P : RoundCapProfile) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X Y : SmoothVectorField PuncturedCapModel PuncturedCap) (q : PuncturedCap),
        0 ≤ P.puncturedMetric.metricInner q (P.puncturedConnection.curvature X Y X q) (Y q) ∧
        P.puncturedMetric.metricInner q (P.puncturedConnection.curvature X Y X q) (Y q) ≤
          C * (P.puncturedMetric.metricInner q (X q) (X q) *
            P.puncturedMetric.metricInner q (Y q) (Y q) -
            P.puncturedMetric.metricInner q (X q) (Y q) ^ 2) := by
/- SWARM_PROOF_BEGIN -/
  have hcoeffAll := P.coefficient_control
  obtain ⟨c, C, hc, hC, hcoeff⟩ := hcoeffAll.2.2.2
  let g := unitRoundSphereMetric
  let G := P.puncturedMetric
  let nabla := P.puncturedConnection
  have hconn : leviCivitaConnectionGeneral g = g.leviCivitaConnection := by
    apply AffineConnection.leviCivita_unique' g
    · exact leviCivitaConnectionGeneral_isLeviCivita g
    · exact g.leviCivitaConnection.isLeviCivita_of_koszulDual g
        (fun A B C q => g.koszulDualSection_dual A B C q)
  have hbase (A B : SmoothVectorField (𝓡 2) EpsilonNeckSphere)
      (x : EpsilonNeckSphere) :
      g.metricInner x ((leviCivitaConnectionGeneral g).curvature A B A x) (B x) =
        g.metricInner x (A x) (A x) * g.metricInner x (B x) (B x) -
          g.metricInner x (A x) (B x) ^ 2 := by
    rw [hconn]
    have h := unitRoundSphereMetric_intrinsic_curvature_one A B A B x
    rw [g.metricInner_comm x (B x) (A x)] at h
    simpa [pow_two] using h
  refine ⟨C, hC, ?_⟩
  intro X Y q
  obtain ⟨A, hA⟩ := exists_smoothVectorField_eq (I := 𝓡 2) q.1 (X q).1
  obtain ⟨B, hB⟩ := exists_smoothVectorField_eq (I := 𝓡 2) q.1 (Y q).1
  let a : ℝ := (X q).2
  let b : ℝ := (Y q).2
  let U : SmoothVectorField PuncturedCapModel PuncturedCap :=
    coneHorizontalLift A +
      SmoothVectorField.smul (fun _ => a) contMDiff_const coneRadialField
  let V : SmoothVectorField PuncturedCapModel PuncturedCap :=
    coneHorizontalLift B +
      SmoothVectorField.smul (fun _ => b) contMDiff_const coneRadialField
  have hU : U q = X q := by
    dsimp [U, a]
    simp only [SmoothVectorField.add_apply, SmoothVectorField.smul_apply,
      coneHorizontalLift_apply, coneRadialField_apply, Prod.smul_mk,
      Prod.mk_add_mk, hA]
    exact Prod.ext
      (by rw [Prod.fst_add, Prod.smul_fst]; simp)
      (by rw [Prod.snd_add, Prod.smul_snd]; simp)
  have hV : V q = Y q := by
    dsimp [V, b]
    simp only [SmoothVectorField.add_apply, SmoothVectorField.smul_apply,
      coneHorizontalLift_apply, coneRadialField_apply, Prod.smul_mk,
      Prod.mk_add_mk, hB]
    exact Prod.ext
      (by rw [Prod.fst_add, Prod.smul_fst]; simp)
      (by rw [Prod.snd_add, Prod.smul_snd]; simp)
  have hcurv_vec : nabla.curvature X Y X q = nabla.curvature U V U q := by
    exact nabla.curvature_apply_congr hU.symm hV.symm hU.symm
  have hcurv_eq :
      G.metricInner q (nabla.curvature X Y X q) (Y q) =
        G.metricInner q (nabla.curvature U V U q) (V q) := by
    rw [hcurv_vec, hV]
  have hcurv := warpedConnection_general_plane_curvature
    unitRoundSphereMetric P.w P.smooth P.positive A B a b q
  have hbaseAB := hbase A B q.1
  rw [hbaseAB] at hcurv
  have hw : P.w (q.2 : ℝ) ≠ 0 :=
    (ne_of_gt (P.positive (q.2 : ℝ) q.2.property))
  have hcurv_formula :
      G.metricInner q (nabla.curvature U V U q) (V q) =
        P.tangentialCoefficient q.2 *
            (P.w q.2 ^ 4 *
              (g.metricInner q.1 (A q.1) (A q.1) *
                g.metricInner q.1 (B q.1) (B q.1) -
                g.metricInner q.1 (A q.1) (B q.1) ^ 2)) +
          P.radialCoefficient q.2 *
            (P.w q.2 ^ 2 *
              g.metricInner q.1 (b • A q.1 - a • B q.1)
                (b • A q.1 - a • B q.1)) := by
    calc
      G.metricInner q (nabla.curvature U V U q) (V q) =
          P.w q.2 ^ 2 *
              (g.metricInner q.1 (A q.1) (A q.1) *
                g.metricInner q.1 (B q.1) (B q.1) -
                g.metricInner q.1 (A q.1) (B q.1) ^ 2) -
            P.w q.2 ^ 2 * deriv P.w q.2 ^ 2 *
              (g.metricInner q.1 (A q.1) (A q.1) *
                g.metricInner q.1 (B q.1) (B q.1) -
                g.metricInner q.1 (A q.1) (B q.1) ^ 2) -
            P.w q.2 * deriv (deriv P.w) q.2 *
              g.metricInner q.1 (b • A q.1 - a • B q.1)
                (b • A q.1 - a • B q.1) := by
        simpa [G, nabla, U, V, g, RoundCapProfile.puncturedMetric,
          RoundCapProfile.puncturedConnection, Prod.smul_mk, Prod.mk_add_mk] using hcurv
      _ = P.tangentialCoefficient q.2 *
            (P.w q.2 ^ 4 *
              (g.metricInner q.1 (A q.1) (A q.1) *
                g.metricInner q.1 (B q.1) (B q.1) -
                g.metricInner q.1 (A q.1) (B q.1) ^ 2)) +
          P.radialCoefficient q.2 *
            (P.w q.2 ^ 2 *
              g.metricInner q.1 (b • A q.1 - a • B q.1)
                (b • A q.1 - a • B q.1)) := by
        rw [RoundCapProfile.tangentialCoefficient,
          RoundCapProfile.radialCoefficient]
        field_simp [hw] <;> ring
  have hcurv_formula' := hcurv_formula
  rw [RoundCapProfile.tangentialCoefficient,
    RoundCapProfile.radialCoefficient] at hcurv_formula'
  have hcurv_split :
      G.metricInner q (nabla.curvature U V U q) (V q) =
        ((1 - deriv P.w (q.2 : ℝ) ^ 2) * P.w (q.2 : ℝ) ^ 2) *
            (g.metricInner q.1 (A q.1) (A q.1) *
              g.metricInner q.1 (B q.1) (B q.1) -
              g.metricInner q.1 (A q.1) (B q.1) ^ 2) +
          (-deriv (deriv P.w) (q.2 : ℝ) * P.w (q.2 : ℝ)) *
            g.metricInner q.1 (b • A q.1 - a • B q.1)
              (b • A q.1 - a • B q.1) := by
    rw [hcurv_formula']
    field_simp [hw]
  have hGram : 0 ≤
      g.metricInner q.1 (A q.1) (A q.1) *
          g.metricInner q.1 (B q.1) (B q.1) -
        g.metricInner q.1 (A q.1) (B q.1) ^ 2 := by
    rw [sphere_metricInner_eq_ambient A A q.1,
      sphere_metricInner_eq_ambient B B q.1,
      sphere_metricInner_eq_ambient A B q.1]
    exact sub_nonneg.mpr (by
      simpa only [pow_two] using
        (real_inner_mul_inner_self_le (sphereAmbientField A q.1) (sphereAmbientField B q.1)))
  have hRad : 0 ≤
      g.metricInner q.1 (b • A q.1 - a • B q.1)
        (b • A q.1 - a • B q.1) :=
    g.metricInner_self_nonneg _ _
  have hGramFull :
      G.metricInner q (U q) (U q) * G.metricInner q (V q) (V q) -
          G.metricInner q (U q) (V q) ^ 2 =
        P.w q.2 ^ 4 *
            (g.metricInner q.1 (A q.1) (A q.1) *
              g.metricInner q.1 (B q.1) (B q.1) -
              g.metricInner q.1 (A q.1) (B q.1) ^ 2) +
          P.w q.2 ^ 2 *
            g.metricInner q.1 (b • A q.1 - a • B q.1)
              (b • A q.1 - a • B q.1) := by
    have hU' : U q = (A q.1, a) := by
      rw [hU]
      dsimp [a]
      exact Prod.ext hA.symm (by rfl)
    have hV' : V q = (B q.1, b) := by
      rw [hV]
      dsimp [b]
      exact Prod.ext hB.symm (by rfl)
    have hUU : G.metricInner q (U q) (U q) =
        P.w q.2 ^ 2 * g.metricInner q.1 (A q.1) (A q.1) + a * a := by
      rw [hU']
      exact P.puncturedMetric_apply q.1 q.2 (A q.1) (A q.1) a a
    have hVV : G.metricInner q (V q) (V q) =
        P.w q.2 ^ 2 * g.metricInner q.1 (B q.1) (B q.1) + b * b := by
      rw [hV']
      exact P.puncturedMetric_apply q.1 q.2 (B q.1) (B q.1) b b
    have hUV : G.metricInner q (U q) (V q) =
        P.w q.2 ^ 2 * g.metricInner q.1 (A q.1) (B q.1) + a * b := by
      rw [hU', hV']
      exact P.puncturedMetric_apply q.1 q.2 (A q.1) (B q.1) a b
    rw [hUU, hVV, hUV]
    simp only [g.metricInner_sub_left, g.metricInner_sub_right,
      g.metricInner_smul_left, g.metricInner_smul_right]
    dsimp [g]
    have hsym :
        ((unitRoundSphereMetric.inner q.1) (B q.1)) (A q.1) =
          ((unitRoundSphereMetric.inner q.1) (A q.1)) (B q.1) :=
      unitRoundSphereMetric.metricInner_comm q.1 (B q.1) (A q.1)
    rw [hsym]
    ring
  have hnonneg : 0 ≤
      G.metricInner q (nabla.curvature X Y X q) (Y q) := by
    rw [hcurv_eq, hcurv_split]
    have ht : 0 ≤ 1 - deriv P.w (q.2 : ℝ) ^ 2 := by
      have hd := P.deriv_bounds (q.2 : ℝ) q.2.property.le
      have hsq : deriv P.w (q.2 : ℝ) ^ 2 ≤ (1 : ℝ) ^ 2 :=
        (sq_le_sq₀ hd.1 (by norm_num)).2 hd.2
      exact sub_nonneg.mpr (by simpa using hsq)
    have htw : 0 ≤ ((1 - deriv P.w (q.2 : ℝ) ^ 2) * P.w (q.2 : ℝ) ^ 2) :=
      mul_nonneg ht (sq_nonneg _)
    have hr : 0 ≤ -deriv (deriv P.w) (q.2 : ℝ) * P.w (q.2 : ℝ) :=
      mul_nonneg (neg_nonneg.mpr (P.concave _ q.2.property.le))
        (le_of_lt (P.positive _ q.2.property))
    exact add_nonneg (mul_nonneg htw hGram) (mul_nonneg hr hRad)
  refine ⟨hnonneg, ?_⟩
  · rw [hcurv_eq, hcurv_formula, ← hU, ← hV, hGramFull]
    have ht : P.tangentialCoefficient (q.2 : ℝ) ≤ C :=
      (hcoeff (q.2 : ℝ) q.2.property).2.2.2
    have hr : P.radialCoefficient (q.2 : ℝ) ≤ C :=
      (hcoeff (q.2 : ℝ) q.2.property).2.1
    have hfull : 0 ≤
        P.w q.2 ^ 4 *
            (g.metricInner q.1 (A q.1) (A q.1) *
              g.metricInner q.1 (B q.1) (B q.1) -
              g.metricInner q.1 (A q.1) (B q.1) ^ 2) +
          P.w q.2 ^ 2 *
            g.metricInner q.1 (b • A q.1 - a • B q.1)
              (b • A q.1 - a • B q.1) := by
      exact add_nonneg
        (mul_nonneg (by positivity) hGram)
        (mul_nonneg (sq_nonneg (P.w q.2)) hRad)
    have hfirst : 0 ≤ P.w q.2 ^ 4 *
        (g.metricInner q.1 (A q.1) (A q.1) *
          g.metricInner q.1 (B q.1) (B q.1) -
          g.metricInner q.1 (A q.1) (B q.1) ^ 2) :=
      mul_nonneg (by positivity) hGram
    have hsecond : 0 ≤ P.w q.2 ^ 2 *
        g.metricInner q.1 (b • A q.1 - a • B q.1)
          (b • A q.1 - a • B q.1) :=
      mul_nonneg (sq_nonneg _) hRad
    exact add_le_add
      (mul_le_mul_of_nonneg_right ht hfirst)
      (mul_le_mul_of_nonneg_right hr hsecond) |>.trans_eq (by ring)
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
