import MorganTianLib.Ch02.SurgeryCap.GlobalCapGeometry
import DoCarmoLib.Riemannian.Metric.RiemannianDistance

open Set Riemannian Bundle Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
noncomputable section
namespace MorganTianLib.SurgeryCap
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** For the genuine length distance of the constructed cap, the
Euclidean radial coordinate is exactly the distance from the tip. -/
theorem globalCap_riemannianEDist_zero (P : RoundCapProfile) :
    letI : RiemannianBundle (fun x : E3 => TangentSpace (𝓡 3) x) :=
      ⟨P.globalMetric.toRiemannianMetric⟩
    ∀ x : E3, Manifold.riemannianEDist (𝓡 3) (0 : E3) x = ENNReal.ofReal ‖x‖ := by
/- SWARM_PROOF_BEGIN -/
  letI : RiemannianBundle (fun x : E3 => TangentSpace (𝓡 3) x) :=
    ⟨P.globalMetric.toRiemannianMetric⟩
  intro x
  have hspeed (z : E3) (t : ℝ) :
      let v : TangentSpace (𝓡 3) (t • z) := z
      ‖v‖ = ‖z‖ := by
    have hzero (y : E3) (u : TangentSpace (𝓡 3) y) (hy : y = 0) :
        ‖u‖ = ‖(let uE : E3 := u; uE)‖ := by
      let uE : E3 := u
      have hi : inner ℝ u u = P.globalMetric.metricInner y u u := by rfl
      have hm : P.globalMetric.metricInner y u u = inner ℝ uE uE := by
        rw [hy]
        simpa [uE] using P.globalMetric_zero (u : E3) (u : E3)
      have hsq : ‖u‖ ^ 2 = ‖uE‖ ^ 2 := by
        calc
          ‖u‖ ^ 2 = inner ℝ u u := (real_inner_self_eq_norm_sq u).symm
          _ = P.globalMetric.metricInner y u u := hi
          _ = inner ℝ uE uE := hm
          _ = ‖uE‖ ^ 2 := real_inner_self_eq_norm_sq _
      have hu : ‖u‖ = ‖uE‖ := by
        nlinarith [norm_nonneg u, norm_nonneg uE]
      simpa [uE]
    dsimp
    by_cases hz : z = 0
    · subst z
      simp
    by_cases ht : t = 0
    · subst t
      exact hzero ((0 : ℝ) • z)
        (z : TangentSpace (𝓡 3) ((0 : ℝ) • z)) (by simp)
    let y : E3 := t • z
    have hy : y ≠ 0 := by
      dsimp [y]
      exact smul_ne_zero ht hz
    let Z : TangentSpace (𝓡 3) y := z
    let Y : TangentSpace (𝓡 3) y := y
    have hscale : Z = t⁻¹ • Y := by
      dsimp [Z, Y, y]
      simp [smul_smul, ht]
    have hmetric : P.globalMetric.metricInner y Z Z =
        inner ℝ z z := by
      rw [hscale]
      change P.globalMetric.metricInner y (t⁻¹ • Y) (t⁻¹ • Y) = _
      simp [Riemannian.RiemannianMetric.metricInner, map_smul, smul_eq_mul]
      have hr : P.globalMetric.metricInner y Y Y = inner ℝ y y := by
        change P.globalMetric.metricInner y (y : E3) y = _
        exact P.globalMetric_radial y y
      have hr' : ((P.globalMetric.inner y) Y) Y = inner ℝ y y := by
        simpa only [Riemannian.RiemannianMetric.metricInner] using hr
      rw [hr']
      dsimp [y]
      simp only [real_inner_self_eq_norm_sq, norm_smul]
      field_simp
      simp [sq_abs]
    have hsq : ‖Z‖ ^ 2 = ‖z‖ ^ 2 := by
      calc
        ‖Z‖ ^ 2 = inner ℝ Z Z := (real_inner_self_eq_norm_sq Z).symm
        _ = P.globalMetric.metricInner y Z Z := by rfl
        _ = ‖z‖ ^ 2 := hmetric.trans (real_inner_self_eq_norm_sq z)
    have hv : ‖Z‖ = ‖z‖ := by
      nlinarith [norm_nonneg Z, norm_nonneg z]
    simpa [y, Z] using hv
  have hρbound (e : ℝ) (he : 0 < e) :
      ∀ (y v : E3),
        |fderiv ℝ (fun q : E3 => Real.sqrt (‖q‖ ^ 2 + e ^ 2)) y v| ≤
          ‖(let V : TangentSpace (𝓡 3) y := v; V)‖ := by
    intro y v
    let V : TangentSpace (𝓡 3) y := v
    let ρ : E3 → ℝ := fun q => Real.sqrt (‖q‖ ^ 2 + e ^ 2)
    have hpos (q : E3) : ‖q‖ ^ 2 + e ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg ‖q‖]
    have hsq : HasFDerivAt (fun q : E3 => ‖q‖ ^ 2 + e ^ 2)
        (2 • innerSL ℝ y) y := by
      convert (hasStrictFDerivAt_norm_sq y).hasFDerivAt.add_const (e ^ 2) using 1
    have hρ := (hsq.sqrt (hpos y)).fderiv
    have hfd : fderiv ℝ ρ y =
        (1 / (2 * Real.sqrt (‖y‖ ^ 2 + e ^ 2))) •
          (2 • innerSL ℝ y) := by
      simpa [ρ] using hρ
    have hden : 0 < Real.sqrt (‖y‖ ^ 2 + e ^ 2) := by
      positivity
    have hformula : fderiv ℝ ρ y v =
        inner ℝ y v / Real.sqrt (‖y‖ ^ 2 + e ^ 2) := by
      rw [hfd]
      simp [ContinuousLinearMap.smul_apply, innerSL_apply_apply,
        smul_eq_mul, ne_of_gt hden]
      ring
    let Y : TangentSpace (𝓡 3) y := y
    have hYnorm : ‖Y‖ = ‖y‖ := by
      have hsq : ‖Y‖ ^ 2 = ‖y‖ ^ 2 := by
        calc
          ‖Y‖ ^ 2 = inner ℝ Y Y := (real_inner_self_eq_norm_sq Y).symm
          _ = P.globalMetric.metricInner y Y Y := by rfl
          _ = inner ℝ y y := by
            simpa [Y] using P.globalMetric_radial y y
          _ = ‖y‖ ^ 2 := real_inner_self_eq_norm_sq y
      nlinarith [norm_nonneg Y, norm_nonneg y]
    have hi : inner ℝ Y V = P.globalMetric.metricInner y Y V := by rfl
    have hr : P.globalMetric.metricInner y Y V = inner ℝ y v := by
      simpa [Y, V] using P.globalMetric_radial y v
    have hc : |inner ℝ y v| ≤ ‖y‖ * ‖V‖ := by
      rw [← hr, ← hi, ← hYnorm]
      exact abs_real_inner_le_norm Y V
    have hden_ge : ‖y‖ ≤ Real.sqrt (‖y‖ ^ 2 + e ^ 2) := by
      have hs : (Real.sqrt (‖y‖ ^ 2 + e ^ 2)) ^ 2 =
          ‖y‖ ^ 2 + e ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      nlinarith [sq_nonneg e, norm_nonneg y]
    dsimp [ρ] at hformula ⊢
    rw [hformula, abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    calc
      |inner ℝ y v| ≤ ‖y‖ * ‖V‖ := hc
      _ = ‖V‖ * ‖y‖ := mul_comm _ _
      _ ≤ ‖V‖ * Real.sqrt (‖y‖ ^ 2 + e ^ 2) := by
        exact mul_le_mul_of_nonneg_left hden_ge (norm_nonneg V)
  have hpath (γ : ℝ → E3) (hγ0 : γ 0 = 0) (hγ1 : γ 1 = x)
      (hγ : CMDiff[Icc (0 : ℝ) 1] 1 γ) :
      ENNReal.ofReal ‖x‖ ≤ Manifold.pathELength (𝓡 3) γ 0 1 := by
    have hfixed (e : ℝ) (he : 0 < e) :
        ENNReal.ofReal (Real.sqrt (‖x‖ ^ 2 + e ^ 2) - e) ≤
          Manifold.pathELength (𝓡 3) γ 0 1 := by
      let ρ : E3 → ℝ := fun q => Real.sqrt (‖q‖ ^ 2 + e ^ 2)
      have hρ : ContDiff ℝ 1 ρ := by
        have harg : ContDiff ℝ 1 (fun q : E3 => ‖q‖ ^ 2 + e ^ 2) :=
          (contDiff_norm_sq ℝ).add contDiff_const
        exact harg.sqrt (fun q => by
          nlinarith [sq_nonneg ‖q‖, sq_pos_of_pos he])
      have hγcd : ContDiffOn ℝ 1 γ (Icc (0 : ℝ) 1) := by
        rw [← contMDiffOn_iff_contDiffOn]
        exact hγ
      have hcomp : ContDiffOn ℝ 1 (fun t : ℝ => ρ (γ t))
          (Icc (0 : ℝ) 1) := by
        exact hρ.fun_comp_contDiffOn hγcd
      have hdisp :=
        enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc
          hcomp zero_le_one
      have hdiff : 0 ≤ Real.sqrt (‖x‖ ^ 2 + e ^ 2) - e := by
        have hs : e ≤ Real.sqrt (‖x‖ ^ 2 + e ^ 2) := by
          have hsq : (Real.sqrt (‖x‖ ^ 2 + e ^ 2)) ^ 2 =
              ‖x‖ ^ 2 + e ^ 2 := by
            rw [Real.sq_sqrt]
            positivity
          nlinarith [sq_nonneg ‖x‖,
            Real.sqrt_nonneg (‖x‖ ^ 2 + e ^ 2)]
        linarith
      rw [hγ1, hγ0] at hdisp
      have hend : ‖ρ x - ρ 0‖ₑ =
          ENNReal.ofReal (Real.sqrt (‖x‖ ^ 2 + e ^ 2) - e) := by
        have hρ0 : ρ 0 = e := by
          dsimp [ρ]
          rw [norm_zero]
          have hz : (0 : ℝ) ^ 2 = 0 := by norm_num
          rw [hz, zero_add, Real.sqrt_sq (le_of_lt he)]
        rw [hρ0]
        exact Real.enorm_of_nonneg hdiff
      calc
        ENNReal.ofReal (Real.sqrt (‖x‖ ^ 2 + e ^ 2) - e)
            = ‖ρ x - ρ 0‖ₑ := hend.symm
        _ ≤ ∫⁻ t in Icc (0 : ℝ) 1,
            ‖derivWithin (fun s : ℝ => ρ (γ s)) (Icc 0 1) t‖ₑ := hdisp
        _ = ∫⁻ t in Ioo (0 : ℝ) 1,
            ‖derivWithin (fun s : ℝ => ρ (γ s)) (Icc 0 1) t‖ₑ := by
          rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
        _ ≤ ∫⁻ t in Ioo (0 : ℝ) 1,
            ‖mfderiv[Icc (0 : ℝ) 1] γ t 1‖ₑ := by
          refine MeasureTheory.setLIntegral_mono' measurableSet_Ioo ?_
          intro t ht
          have hmem : Icc (0 : ℝ) 1 ∈ 𝓝 t :=
            Icc_mem_nhds ht.1 ht.2
          have hγt : ContDiffAt ℝ 1 γ t :=
            (hγcd t ⟨ht.1.le, ht.2.le⟩).contDiffAt hmem
          have hphi : derivWithin (fun s : ℝ => ρ (γ s))
              (Icc (0 : ℝ) 1) t =
              fderiv ℝ ρ (γ t) (deriv γ t) := by
            rw [derivWithin_of_mem_nhds hmem]
            simpa [Function.comp_def] using
              (fderiv_comp_deriv t
                (hρ.differentiable one_ne_zero).differentiableAt
                (hγt.differentiableAt one_ne_zero))
          have hbound := hρbound e he (γ t) ((fderiv ℝ γ t) 1)
          rw [hphi, ← fderiv_apply_one_eq_deriv,
            mfderivWithin_eq_fderivWithin,
            fderivWithin_of_mem_nhds hmem]
          rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
          apply (ENNReal.coe_le_coe).2
          exact_mod_cast hbound
        _ = Manifold.pathELength (𝓡 3) γ 0 1 := by
          rw [MeasureTheory.restrict_Ioo_eq_restrict_Icc]
          exact (Manifold.pathELength_eq_lintegral_mfderivWithin_Icc).symm
    have he : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹)
        Filter.atTop (𝓝 0) := by
      have hn0 : Filter.Tendsto (fun n : ℕ => (n : ℝ))
          Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
      have hn : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1)
          Filter.atTop Filter.atTop := by
        refine Filter.tendsto_atTop_atTop.2 ?_
        intro b
        obtain ⟨N, hN⟩ := (Filter.tendsto_atTop_atTop.1 hn0) (b - 1)
        refine ⟨N, fun n hnN => ?_⟩
        linarith [hN n hnN]
      simpa [Function.comp_def] using
        (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp hn
    have hlim : Filter.Tendsto
        (fun n : ℕ => ENNReal.ofReal
          (Real.sqrt (‖x‖ ^ 2 + ((n : ℝ) + 1)⁻¹ ^ 2) -
            ((n : ℝ) + 1)⁻¹)) Filter.atTop
        (𝓝 (ENNReal.ofReal ‖x‖)) := by
      have harg : Filter.Tendsto
          (fun n : ℕ => ‖x‖ ^ 2 + ((n : ℝ) + 1)⁻¹ ^ 2)
          Filter.atTop (𝓝 (‖x‖ ^ 2)) := by
        have hc : Filter.Tendsto (fun _ : ℕ => ‖x‖ ^ 2)
            Filter.atTop (𝓝 (‖x‖ ^ 2)) := tendsto_const_nhds
        simpa using hc.add (he.pow 2)
      have hsqrt : Filter.Tendsto
          (fun n : ℕ => Real.sqrt
            (‖x‖ ^ 2 + ((n : ℝ) + 1)⁻¹ ^ 2)) Filter.atTop
          (𝓝 (Real.sqrt (‖x‖ ^ 2))) := by
        exact Real.continuous_sqrt.continuousAt.tendsto.comp harg
      have hsub := hsqrt.sub he
      simpa [Real.sqrt_sq (norm_nonneg x)] using
        ENNReal.tendsto_ofReal hsub
    exact le_of_tendsto' hlim (fun n =>
      hfixed (((n : ℝ) + 1)⁻¹) (by positivity))
  apply le_antisymm
  · let γ : ℝ → E3 := fun t => t • x
    have hγ : CMDiff[Icc (0 : ℝ) 1] 1 γ := by
      rw [contMDiffOn_iff_contDiffOn]
      fun_prop
    have hdist : Manifold.riemannianEDist (𝓡 3) (0 : E3) x ≤
        Manifold.pathELength (𝓡 3) γ 0 1 := by
      apply Manifold.riemannianEDist_le_pathELength hγ
      · simp [γ]
      · simp [γ]
      · exact zero_le_one
    apply hdist.trans
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
    have hderiv (t : ℝ) :
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 3) γ t 1 : E3) = x := by
      rw [mfderiv_eq_fderiv]
      dsimp [γ]
      change deriv (fun t : ℝ => t • x) t = x
      simpa using ((hasDerivAt_id t).smul_const x).deriv
    have hnorm (t : ℝ) :
        ‖mfderiv (𝓘(ℝ, ℝ)) (𝓡 3) γ t 1‖ₑ = ‖x‖ₑ := by
      change ‖((mfderiv (𝓘(ℝ, ℝ)) (𝓡 3) γ t 1 : E3) :
        TangentSpace (𝓡 3) (γ t))‖ₑ = ‖x‖ₑ
      rw [hderiv]
      have hh := hspeed x t
      dsimp at hh
      simp [enorm, nnnorm, hh]
    simp_rw [hnorm]
    rw [MeasureTheory.lintegral_const]
    simp [enorm, nnnorm]
  · apply le_of_forall_gt
    intro r hr
    obtain ⟨γ, hγ0, hγ1, hγ, hγlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hr
    exact (hpath γ hγ0 hγ1 hγ).trans_lt hγlen
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
