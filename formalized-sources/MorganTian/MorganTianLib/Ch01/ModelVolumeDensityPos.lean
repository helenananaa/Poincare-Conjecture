import MorganTianLib.Ch01.BishopGromovBall
import MorganTianLib.Ch01.ComparisonFunctions
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory Measure Metric Set Module Filter
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Lebesgue integral of `t ↦ t^m` on `(0, r)`. -/
private theorem lintegral_Ioo_pow (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal (t ^ m)) =
      ENNReal.ofReal (r ^ (m + 1) / (m + 1)) := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  rw [← ofReal_integral_eq_lintegral_ofReal (intervalIntegral.intervalIntegrable_pow _).1]
  · rw [← intervalIntegral.integral_of_le hr, integral_pow]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact pow_nonneg ht.1.le _

/-- On `(0,1]`, the model comparison density `sn_k(t)/t` for `k ≥ 0` is bounded
below by a positive constant depending only on `k`. Used to get a positive
infimum of `modelBallVolume / r^n` without identifying Riemannian measure. -/
theorem snK_div_self_inf_pos (k : ℝ) (hk : 0 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Ioc (0 : ℝ) 1, c ≤ snK k t / t :=
/- SWARM_PROOF_BEGIN -/
by
  -- Difference quotient of `sn_k` at `0`: `sn_k(0) = 0` and `sn_k'(0) = 1`.
  have htend : Tendsto (fun t : ℝ => snK k t / t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hd : HasDerivAt (snK k) 1 0 := by
      have := hasDerivAt_snK k 0 hk
      rwa [csK_zero_right] at this
    have hslope := hasDerivAt_iff_tendsto_slope.mp hd
    have hmono : Tendsto (slope (snK k) 0) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
      hslope.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))
    refine hmono.congr fun t => ?_
    rw [slope_def_field, snK_zero_right]
    simp [div_eq_inv_mul]
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (1 / 2 : ℝ) ≤ snK k t / t :=
    htend.eventually_const_le (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨η, hηpos, hη⟩ :
      ∃ η, η ∈ Ioi (0 : ℝ) ∧ Ioo (0 : ℝ) η ⊆ {t | (1 / 2 : ℝ) ≤ snK k t / t} := by
    have hmem : {t : ℝ | (1 / 2 : ℝ) ≤ snK k t / t} ∈ 𝓝[>] (0 : ℝ) := hev
    exact (mem_nhdsGT_iff_exists_Ioo_subset (a := (0 : ℝ))).mp hmem
  -- Shrink the neighbourhood if needed so the remaining interval sits in `(0, 1]`.
  set η' := min η (1 : ℝ)
  have hη'pos : 0 < η' := lt_min hηpos zero_lt_one
  have hη'le : η' ≤ 1 := min_le_right _ _
  have hcont : ContinuousOn (fun t : ℝ => snK k t / t) (Icc η' 1) := by
    refine (continuous_snK_right k).continuousOn.div continuousOn_id ?_
    intro t ht
    exact (lt_of_lt_of_le hη'pos ht.1).ne'
  obtain ⟨tmin, htmin, hmin⟩ :=
    isCompact_Icc.exists_isMinOn ⟨η', le_rfl, hη'le⟩ hcont
  set m := snK k tmin / tmin
  have hmpos : 0 < m := by
    have ht0 : 0 < tmin := lt_of_lt_of_le hη'pos htmin.1
    exact div_pos (snK_pos k tmin hk ht0) ht0
  refine ⟨min (1 / 2) m, lt_min (by norm_num) hmpos, ?_⟩
  intro t ht
  by_cases htη : t < η'
  · exact (min_le_left _ _).trans (hη ⟨ht.1, htη.trans_le (min_le_left _ _)⟩)
  · exact (min_le_right _ _).trans (hmin ⟨le_of_not_gt htη, ht.2⟩)
/- SWARM_PROOF_END -/

/-- Volume-ratio engine for the comparison ball: there is `c > 0` such that
for every `s ∈ (0,1]`,

  `c * ofReal (s^n) ≤ modelBallVolume_k(s)`.

This is the model half of the volume-ratio clause of
`thm:local-volume-injectivity-radius-control`. It does not produce injectivity
radius, Klingenberg, or manifold Bishop–Gromov. -/
theorem modelBallVolume_lower_power (k : ℝ) (hk : 0 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ s ∈ Ioc (0 : ℝ) 1,
      ENNReal.ofReal c * ENNReal.ofReal (s ^ finrank ℝ E) ≤
        modelBallVolume (E := E) μ k s :=
/- SWARM_PROOF_BEGIN -/
by
  set n := finrank ℝ E
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr Module.finrank_pos.ne'
  obtain ⟨c0, hc0, hc0le⟩ := snK_div_self_inf_pos k hk
  set ω := (μ.toSphere univ).toReal
  have hω_pos : 0 < ω :=
    ENNReal.toReal_pos (toSphere_univ_pos μ).ne' (measure_ne_top _ _)
  have hω : ENNReal.ofReal ω = μ.toSphere univ :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr Module.finrank_pos
  set c := ω * c0 ^ (n - 1) / n
  have hcpos : 0 < c :=
    div_pos (mul_pos hω_pos (pow_pos hc0 _)) hnpos
  refine ⟨c, hcpos, ?_⟩
  intro s hs
  have hs0 : 0 < s := hs.1
  rw [modelBallVolume_eq μ k s]
  have hpt : ∀ t ∈ Ioo (0 : ℝ) s,
      ENNReal.ofReal (c0 ^ (n - 1)) * ENNReal.ofReal (t ^ (n - 1))
        ≤ ENNReal.ofReal (snK k t ^ (n - 1)) := by
    intro t ht
    have ht01 : t ∈ Ioc (0 : ℝ) 1 := ⟨ht.1, ht.2.le.trans hs.2⟩
    have hct : c0 * t ≤ snK k t := (le_div_iff₀ ht.1).mp (hc0le t ht01)
    have hnn : 0 ≤ c0 * t := mul_nonneg hc0.le ht.1.le
    have hpow := pow_le_pow_left₀ hnn hct (n - 1)
    rw [← ENNReal.ofReal_mul (pow_nonneg hc0.le _), ← mul_pow]
    exact ENNReal.ofReal_le_ofReal hpow
  have hinteq :
      (∫⁻ t in Ioo (0 : ℝ) s,
          ENNReal.ofReal (c0 ^ (n - 1)) * ENNReal.ofReal (t ^ (n - 1)))
        = ENNReal.ofReal (c0 ^ (n - 1)) *
            ∫⁻ t in Ioo (0 : ℝ) s, ENNReal.ofReal (t ^ (n - 1)) :=
    lintegral_const_mul _ (by fun_prop)
  have hint :
      ENNReal.ofReal (c0 ^ (n - 1)) *
          ∫⁻ t in Ioo (0 : ℝ) s, ENNReal.ofReal (t ^ (n - 1))
        ≤ ∫⁻ t in Ioo (0 : ℝ) s, ENNReal.ofReal (snK k t ^ (n - 1)) := by
    rw [← hinteq]
    exact setLIntegral_mono' measurableSet_Ioo hpt
  have hrad :
      (∫⁻ t in Ioo (0 : ℝ) s, ENNReal.ofReal (t ^ (n - 1))) =
        ENNReal.ofReal (s ^ n / n) := by
    simpa [Nat.sub_add_cancel hn1, Nat.cast_sub hn1] using
      lintegral_Ioo_pow (n - 1) s hs0.le
  have hc0n : 0 ≤ c0 ^ (n - 1) := pow_nonneg hc0.le _
  have hleft :
      ENNReal.ofReal c * ENNReal.ofReal (s ^ n)
        = μ.toSphere univ * (ENNReal.ofReal (c0 ^ (n - 1)) *
            ENNReal.ofReal (s ^ n / n)) := by
    have hden : 0 ≤ ω * c0 ^ (n - 1) / n :=
      div_nonneg (mul_nonneg hω_pos.le hc0n) hnpos.le
    calc
      ENNReal.ofReal c * ENNReal.ofReal (s ^ n)
          = ENNReal.ofReal (ω * c0 ^ (n - 1) / n * s ^ n) :=
            (ENNReal.ofReal_mul hden).symm
      _ = ENNReal.ofReal (ω * (c0 ^ (n - 1) * (s ^ n / n))) := by
            congr 1
            field_simp
      _ = ENNReal.ofReal ω * ENNReal.ofReal (c0 ^ (n - 1) * (s ^ n / n)) :=
            ENNReal.ofReal_mul hω_pos.le
      _ = ENNReal.ofReal ω * (ENNReal.ofReal (c0 ^ (n - 1)) *
            ENNReal.ofReal (s ^ n / n)) := by
            congr 1
            exact ENNReal.ofReal_mul hc0n
      _ = μ.toSphere univ * (ENNReal.ofReal (c0 ^ (n - 1)) *
            ENNReal.ofReal (s ^ n / n)) := by
            rw [hω]
  calc
    ENNReal.ofReal c * ENNReal.ofReal (s ^ n)
        = μ.toSphere univ * (ENNReal.ofReal (c0 ^ (n - 1)) *
            ENNReal.ofReal (s ^ n / n)) := hleft
    _ = μ.toSphere univ * (ENNReal.ofReal (c0 ^ (n - 1)) *
            ∫⁻ t in Ioo (0 : ℝ) s, ENNReal.ofReal (t ^ (n - 1))) := by
          rw [hrad]
    _ ≤ μ.toSphere univ *
          ∫⁻ t in Ioo (0 : ℝ) s, ENNReal.ofReal (snK k t ^ (n - 1)) := by
          gcongr
/- SWARM_PROOF_END -/

end MorganTianLib
