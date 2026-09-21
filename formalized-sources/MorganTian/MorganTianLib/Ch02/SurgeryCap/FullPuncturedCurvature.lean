import MorganTianLib.Ch02.SurgeryCap.GeneralPlaneCurvature
import MorganTianLib.Ch02.SurgeryCap.SphereIntrinsicCurvature
import MorganTianLib.Ch02.SurgeryCap.RadialSectional
import DoCarmoLib.Riemannian.Connection.CurvaturePointwise
open Set Riemannian
open scoped ContDiff Manifold Topology
noncomputable section
namespace MorganTianLib.SurgeryCap
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
  have hcoeffAll :
      (∀ r, 0 ≤ r → P.w r ≤ min r (Real.sqrt 2)) ∧
      (∀ r, 0 < r → r < P.r0 →
        P.radialCoefficient r = 1 / 4 ∧ P.tangentialCoefficient r = 1 / 4) ∧
      (∀ r, P.A < r →
        P.radialCoefficient r = 0 ∧ P.tangentialCoefficient r = 1 / 2) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ r, 0 < r →
        0 ≤ P.radialCoefficient r ∧ P.radialCoefficient r ≤ C ∧
          c ≤ P.tangentialCoefficient r ∧ P.tangentialCoefficient r ≤ C := by
    classical
    have hdiff : Differentiable ℝ P.w := P.smooth.differentiable (by simp)
    have hcont : Continuous P.w := P.smooth.continuous
    have hmono : MonotoneOn P.w (Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hcont.continuousOn
        hdiff.differentiableOn
      intro x hx
      rw [interior_Ici] at hx
      exact (P.deriv_bounds x hx.le).1
    have hupper : ∀ {x y : ℝ}, x ∈ Ici 0 → y ∈ Ici 0 → x ≤ y →
        P.w y - P.w x ≤ 1 * (y - x) := by
      intro x y hx hy hxy
      exact (convex_Ici (0 : ℝ)).image_sub_le_mul_sub_of_deriv_le hcont.continuousOn
        hdiff.differentiableOn (by
          intro z hz
          rw [interior_Ici] at hz
          exact (P.deriv_bounds z hz.le).2) x hx y hy hxy
    have hw_le_r : ∀ {r : ℝ}, 0 ≤ r → P.w r ≤ r := by
      intro r hr
      have h := hupper (x := 0) (y := r) (by simp) (by exact hr) hr
      simpa [P.w_zero] using h
    have hw_le_sqrt : ∀ {r : ℝ}, 0 ≤ r → P.w r ≤ Real.sqrt 2 := by
      intro r hr
      by_cases hA : r ≤ P.A
      · have h := hmono (show r ∈ Ici 0 by exact hr)
          (show P.A ∈ Ici 0 by exact le_of_lt (lt_trans P.r0_pos P.r0_lt_A)) hA
        simpa [P.tail P.A (le_refl P.A)] using h
      · have hAr : P.A < r := lt_of_not_ge hA
        exact le_of_eq (P.tail r (le_of_lt hAr))
    have htip_deriv : ∀ r, 0 < r → r < P.r0 →
        deriv P.w r = Real.cos (r / 2) ∧
          deriv (deriv P.w) r = -(1 / 2) * Real.sin (r / 2) := by
      intro r hr hr0
      let f : ℝ → ℝ := fun x => 2 * Real.sin (x / 2)
      have heq : P.w =ᶠ[𝓝 r] f := by
        have hn : Ioo (-P.r0) P.r0 ∈ 𝓝 r :=
          Ioo_mem_nhds (by linarith) hr0
        filter_upwards [hn] with x hx
        exact P.tip x (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
      have hformula : ∀ x, deriv f x = Real.cos (x / 2) := by
        intro x
        have h := HasDerivAt.const_mul (2 : ℝ)
          ((Real.hasDerivAt_sin (x / 2)).comp x ((hasDerivAt_id x).div_const 2))
        convert h.deriv using 1 <;> simp [f, Function.comp_def] <;> ring
      have hd1 : deriv P.w r = Real.cos (r / 2) :=
        (heq.deriv_eq).trans (hformula r)
      have heq' : deriv P.w =ᶠ[𝓝 r] (fun x => Real.cos (x / 2)) :=
        heq.deriv.trans (Filter.Eventually.of_forall hformula)
      have hd2 : deriv (deriv P.w) r =
          deriv (fun x : ℝ => Real.cos (x / 2)) r := heq'.deriv_eq
      have hcos := (Real.hasDerivAt_cos (r / 2)).comp r ((hasDerivAt_id r).div_const 2)
      refine ⟨hd1, ?_⟩
      calc
        deriv (deriv P.w) r = deriv (fun x : ℝ => Real.cos (x / 2)) r := hd2
        _ = -(1 / 2) * Real.sin (r / 2) := by
          convert hcos.deriv using 1 <;> simp [Function.comp_def] <;> ring
    have htip_coeff : ∀ r, 0 < r → r < P.r0 →
        P.radialCoefficient r = 1 / 4 ∧ P.tangentialCoefficient r = 1 / 4 := by
      intro r hr hr0
      obtain ⟨hd1, hd2⟩ := htip_deriv r hr hr0
      have hw : P.w r = 2 * Real.sin (r / 2) := P.tip r (abs_le.mpr ⟨by
        linarith [P.r0_pos], hr0.le⟩)
      have hspos : 0 < Real.sin (r / 2) := by
        have hp := P.positive r hr
        rw [hw] at hp
        nlinarith
      constructor
      · rw [RoundCapProfile.radialCoefficient, hw, hd2]
        field_simp [hspos.ne']
        norm_num
      · rw [RoundCapProfile.tangentialCoefficient, hw, hd1]
        field_simp [hspos.ne']
        nlinarith [Real.sin_sq_add_cos_sq (r / 2)]
    have htail_coeff : ∀ r, P.A < r →
        P.radialCoefficient r = 0 ∧ P.tangentialCoefficient r = 1 / 2 := by
      intro r hr
      have heq : P.w =ᶠ[𝓝 r] (fun _ : ℝ => Real.sqrt 2) := by
        filter_upwards [Ioi_mem_nhds hr] with x hx
        exact P.tail x (le_of_lt hx)
      have hd1 : deriv P.w r = 0 := by
        simpa using heq.deriv_eq
      have heq' : deriv P.w =ᶠ[𝓝 r] (fun _ : ℝ => 0) := by
        simpa using heq.deriv
      have hd2 : deriv (deriv P.w) r = 0 := by
        simpa using heq'.deriv_eq
      have hw : P.w r = Real.sqrt 2 := P.tail r (le_of_lt hr)
      have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
      have hsqrt0 : Real.sqrt 2 ≠ 0 := by positivity
      constructor
      · simp [RoundCapProfile.radialCoefficient, hw, hd1, hd2, hsqrt0]
      · rw [RoundCapProfile.tangentialCoefficient, hw, hd1, hsqrt]
        norm_num
    have hrad_nonneg : ∀ r, 0 < r → 0 ≤ P.radialCoefficient r := by
      intro r hr
      change 0 ≤ -deriv (deriv P.w) r / P.w r
      exact div_nonneg (neg_nonneg.mpr (P.concave r hr.le)) (P.positive r hr).le
    let K : Set ℝ := Icc (P.r0 / 2) (P.A + 1)
    have hKcompact : IsCompact K := by
      dsimp [K]
      exact isCompact_Icc
    have hKpos : ∀ x ∈ K, 0 < x := by
      intro x hx
      have hx0 : P.r0 / 2 ≤ x := hx.1
      nlinarith [P.r0_pos]
    have hKw_ne : ∀ x ∈ K, P.w x ≠ 0 := by
      intro x hx
      exact (P.positive x (hKpos x hx)).ne'
    have hcont1 : Continuous (deriv P.w) := P.smooth.continuous_deriv (by simp)
    have hcont2 : Continuous (deriv (deriv P.w)) := by
      have h2 : (2 : ℕ∞ω) ≤ ∞ :=
        (inferInstance : ENat.LEInfty (2 : ℕ∞ω)).out
      simpa [iteratedDeriv_succ] using
        (P.smooth.continuous_iteratedDeriv 2 h2)
    have hrad_cont : ContinuousOn (fun x => P.radialCoefficient x) K := by
      change ContinuousOn (fun x => -deriv (deriv P.w) x / P.w x) K
      exact hcont2.neg.continuousOn.div hcont.continuousOn hKw_ne
    have hKwsq_ne : ∀ x ∈ K, (P.w x) ^ 2 ≠ 0 := by
      intro x hx
      exact pow_ne_zero 2 (hKw_ne x hx)
    have htan_cont : ContinuousOn (fun x => P.tangentialCoefficient x) K := by
      change ContinuousOn (fun x => (1 - deriv P.w x ^ 2) / P.w x ^ 2) K
      exact (continuousOn_const.sub (hcont1.continuousOn.pow 2)).div
        (hcont.continuousOn.pow 2) hKwsq_ne
    have htan_pos : ∀ x ∈ K, 0 < P.tangentialCoefficient x := by
      intro x hx
      have hxpos := hKpos x hx
      have hdb := P.deriv_bounds x hxpos.le
      have hds := P.deriv_strict x hxpos
      rcases hdb with ⟨hd0, hd1⟩
      have hnum : 0 < 1 - deriv P.w x ^ 2 := by
        nlinarith [sq_nonneg (deriv P.w x)]
      have hden : 0 < P.w x ^ 2 := sq_pos_of_pos (P.positive x hxpos)
      change 0 < (1 - deriv P.w x ^ 2) / P.w x ^ 2
      exact div_pos hnum hden
    obtain ⟨Br, hBr⟩ := hKcompact.exists_bound_of_continuousOn hrad_cont
    obtain ⟨Bt, hBt⟩ := hKcompact.exists_bound_of_continuousOn htan_cont
    have hBr' : ∀ x ∈ K, P.radialCoefficient x ≤ Br := by
      intro x hx
      have h := hBr x hx
      have h' : |P.radialCoefficient x| ≤ Br := by
        simpa [Real.norm_eq_abs] using h
      exact (le_abs_self _).trans h'
    have hBt' : ∀ x ∈ K, P.tangentialCoefficient x ≤ Bt := by
      intro x hx
      have h := hBt x hx
      have h' : |P.tangentialCoefficient x| ≤ Bt := by
        simpa [Real.norm_eq_abs] using h
      exact (le_abs_self _).trans h'
    obtain ⟨c0, hc0, hc0le⟩ : ∃ c0 : ℝ, 0 < c0 ∧
        ∀ x ∈ K, c0 ≤ P.tangentialCoefficient x :=
      hKcompact.exists_forall_le' htan_cont htan_pos
    let c : ℝ := min c0 (1 / 4)
    let C : ℝ := max (max Br Bt) 1
    have hc : 0 < c := by
      dsimp [c]
      exact lt_min hc0 (by norm_num)
    have hC : 0 < C := by
      dsimp [C]
      exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hc_c0 : c ≤ c0 := by
      dsimp [c]
      exact min_le_left _ _
    have hc_quarter : c ≤ (1 / 4 : ℝ) := by
      dsimp [c]
      exact min_le_right _ _
    have hBrC : Br ≤ C := by
      dsimp [C]
      exact (le_max_left _ _).trans (le_max_left _ _)
    have hBtC : Bt ≤ C := by
      dsimp [C]
      exact (le_max_right _ _).trans (le_max_left _ _)
    have hquarterC : (1 / 4 : ℝ) ≤ C := by
      dsimp [C]
      have h : (1 / 4 : ℝ) ≤ 1 := by norm_num
      exact h.trans (le_max_right _ _)
    have hhalfC : (1 / 2 : ℝ) ≤ C := by
      dsimp [C]
      have h : (1 / 2 : ℝ) ≤ 1 := by norm_num
      exact h.trans (le_max_right _ _)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr
      exact le_min (hw_le_r hr) (hw_le_sqrt hr)
    · exact htip_coeff
    · exact htail_coeff
    · refine ⟨c, C, hc, hC, ?_⟩
      intro r hr
      by_cases htip : r < P.r0
      · obtain ⟨hrad, htan⟩ := htip_coeff r hr htip
        refine ⟨hrad_nonneg r hr, ?_, ?_, ?_⟩
        · rw [hrad]
          exact hquarterC
        · rw [htan]
          exact hc_quarter
        · rw [htan]
          exact hquarterC
      · by_cases htail : P.A < r
        · obtain ⟨hrad, htan⟩ := htail_coeff r htail
          refine ⟨hrad_nonneg r hr, ?_, ?_, ?_⟩
          · rw [hrad]
            exact hC.le
          · rw [htan]
            exact le_trans hc_quarter (by norm_num)
          · rw [htan]
            exact hhalfC
        · have hr0 : P.r0 ≤ r := le_of_not_gt htip
          have hrA : r ≤ P.A := le_of_not_gt htail
          have hrK : r ∈ K := by
            dsimp [K]
            constructor <;> nlinarith [P.r0_pos]
          refine ⟨hrad_nonneg r hr, ?_, ?_, ?_⟩
          · exact (hBr' r hrK).trans hBrC
          · exact hc_c0.trans (hc0le r hrK)
          · exact (hBt' r hrK).trans hBtC
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
    have hcs := abs_real_inner_le_norm
      (sphereAmbientField A q.1) (sphereAmbientField B q.1)
    have hsq :
        (inner ℝ (sphereAmbientField A q.1) (sphereAmbientField B q.1)) ^ 2 ≤
          (‖sphereAmbientField A q.1‖ * ‖sphereAmbientField B q.1‖) ^ 2 := by
      have := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hcs
      simpa [sq_abs] using this
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    nlinarith
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
      nlinarith
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
