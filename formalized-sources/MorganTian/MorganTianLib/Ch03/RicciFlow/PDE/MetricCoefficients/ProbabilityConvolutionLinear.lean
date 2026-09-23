import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** probability convolution linear. -/
theorem probability_convolution_linear 
    (k : E3 → ℝ) (hk : Integrable k volume) (hpos : ∀ x, 0 ≤ k x)
    (hmass : (∫ x : E3, k x) = 1) :
    ∃ S : (E3 →ᵇ ℝ) →L[ℝ] (E3 →ᵇ ℝ), ‖S‖ ≤ 1 ∧
      ∀ (f : E3 →ᵇ ℝ) (x : E3), (S f) x = ∫ y : E3, k y*f (x-y) :=
/- SWARM_PROOF_BEGIN -/
by
  have hconv_int (f : E3 →ᵇ ℝ) (x : E3) :
      Integrable (fun y : E3 => k y * f (x - y)) volume := by
    apply hk.mul_bdd
    · exact (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · filter_upwards with y
      exact f.norm_coe_le_norm (x - y)
  have hconv_bound (f : E3 →ᵇ ℝ) (x : E3) :
      ‖∫ y : E3, k y * f (x - y)‖ ≤ ‖f‖ := by
    have hbint : Integrable (fun y : E3 => ‖f‖ * k y) volume := by
      simpa [mul_comm] using hk.const_mul ‖f‖
    have hle : ∀ᵐ y ∂volume, ‖k y * f (x - y)‖ ≤ ‖f‖ * k y := by
      filter_upwards with y
      calc
        ‖k y * f (x - y)‖ = |k y| * ‖f (x - y)‖ := by rw [norm_mul, Real.norm_eq_abs]
        _ = k y * ‖f (x - y)‖ := by rw [abs_of_nonneg (hpos y)]
        _ ≤ k y * ‖f‖ := mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (hpos y)
        _ = ‖f‖ * k y := by ring
    calc
      ‖∫ y : E3, k y * f (x - y)‖ ≤ ∫ y : E3, ‖f‖ * k y :=
        norm_integral_le_of_norm_le hbint hle
      _ = ‖f‖ * 1 := by rw [integral_const_mul, hmass]
      _ = ‖f‖ := by ring
  have hconv_cont (f : E3 →ᵇ ℝ) :
      Continuous (fun x : E3 => ∫ y : E3, k y * f (x - y)) := by
    apply continuous_iff_continuousAt.mpr
    intro x₀
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun y : E3 => ‖f‖ * k y)
    · exact Filter.Eventually.of_forall fun x => (hconv_int f x).aestronglyMeasurable
    · filter_upwards with x
      filter_upwards with y
      calc
        ‖k y * f (x - y)‖ = |k y| * ‖f (x - y)‖ := by rw [norm_mul, Real.norm_eq_abs]
        _ = k y * ‖f (x - y)‖ := by rw [abs_of_nonneg (hpos y)]
        _ ≤ k y * ‖f‖ := mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (hpos y)
        _ = ‖f‖ * k y := by ring
    · simpa [mul_comm] using hk.const_mul ‖f‖
    · filter_upwards with y
      have hsub : Tendsto (fun z : E3 => z - y) (𝓝 x₀) (𝓝 (x₀ - y)) :=
        (continuousAt_id.sub continuousAt_const).tendsto
      have hfun : Tendsto (fun z : E3 => f (z - y)) (𝓝 x₀) (𝓝 (f (x₀ - y))) :=
        f.continuous.continuousAt.tendsto.comp hsub
      simpa using (tendsto_const_nhds (x := k y)).mul hfun
  let convBCF (f : E3 →ᵇ ℝ) : E3 →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x : E3 => ∫ y : E3, k y * f (x - y)) (hconv_cont f) ‖f‖
      (fun x => hconv_bound f x)
  have hconvBCF_norm (f : E3 →ᵇ ℝ) : ‖convBCF f‖ ≤ ‖f‖ := by
    apply (BoundedContinuousFunction.norm_le (f := convBCF f) (C := ‖f‖)
      (norm_nonneg _)).2
    intro x
    exact hconv_bound f x
  let Tlin : (E3 →ᵇ ℝ) →ₗ[ℝ] (E3 →ᵇ ℝ) :=
    { toFun := fun f =>
        convBCF f
      map_add' := by
        intro f g
        apply BoundedContinuousFunction.ext
        intro x
        change (∫ y : E3, k y * (f + g) (x - y)) =
          (∫ y : E3, k y * f (x - y)) + (∫ y : E3, k y * g (x - y))
        rw [show (fun y : E3 => k y * (f + g) (x - y)) =
            (fun y => k y * f (x - y)) + (fun y => k y * g (x - y)) by
              funext y
              simp [mul_add]]
        exact integral_add (hconv_int f x) (hconv_int g x)
      map_smul' := by
        intro c f
        apply BoundedContinuousFunction.ext
        intro x
        change (∫ y : E3, k y * (c • f) (x - y)) =
          c * (∫ y : E3, k y * f (x - y))
        rw [show (fun y : E3 => k y * (c • f) (x - y)) =
            (fun y => c * (k y * f (x - y))) by
              funext y
              change k y * (c * f (x - y)) = c * (k y * f (x - y))
              ring]
        rw [integral_const_mul]
        }
  have hTlin_norm (f : E3 →ᵇ ℝ) : ‖Tlin f‖ ≤ 1 * ‖f‖ := by
    change ‖convBCF f‖ ≤ 1 * ‖f‖
    calc
      ‖convBCF f‖ ≤ ‖f‖ := hconvBCF_norm f
      _ = 1 * ‖f‖ := by ring
  let S := Tlin.mkContinuous 1 hTlin_norm
  refine ⟨S, ?_, ?_⟩
  · exact LinearMap.mkContinuous_norm_le Tlin (by norm_num) hTlin_norm
  · intro f x
    simp [S, LinearMap.mkContinuous_apply, Tlin, convBCF,
      BoundedContinuousFunction.coe_ofNormedAddCommGroup]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
