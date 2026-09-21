import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FractionalMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Weighted Gaussian moment in the actual three-dimensional Euclidean norm. -/
theorem euclideanHeatKernel_three_fractional_moment (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      Integrable (fun y : E3 => euclideanHeatKernel 3 t y * ‖y‖ ^ alpha) volume ∧
      (∫ y : E3, euclideanHeatKernel 3 t y * ‖y‖ ^ alpha) ≤ C * t ^ (alpha / 2) := by
/- SWARM_PROOF_BEGIN -/
  classical
  have hpow_sum (a b c : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) :
      (a + b + c) ^ alpha ≤ 3 * (a ^ alpha + b ^ alpha + c ^ alpha) := by
    let m : ℝ := max (max a b) c
    have hm : 0 ≤ m := by
      dsimp [m]
      positivity
    have hsum : a + b + c ≤ 3 * m := by
      have ha' : a ≤ m := by
        dsimp [m]
        exact le_trans (le_max_left _ _) (le_max_left _ _)
      have hb' : b ≤ m := by
        dsimp [m]
        exact le_trans (le_max_right _ _) (le_max_left _ _)
      have hc' : c ≤ m := by
        dsimp [m]
        exact le_max_right _ _
      linarith
    have hm_cases : m = a ∨ m = b ∨ m = c := by
      by_cases hab : a ≤ b
      · by_cases hbc : b ≤ c
        · right; right
          simp [m, max_eq_right hab, max_eq_right hbc]
        · right; left
          have hcb : c ≤ b := le_of_not_ge hbc
          simp [m, max_eq_right hab, max_eq_left hcb]
      · have hba : b ≤ a := le_of_not_ge hab
        by_cases hac : a ≤ c
        · right; right
          simp [m, max_eq_left hba, max_eq_right hac]
        · left
          have hca : c ≤ a := le_of_not_ge hac
          simp [m, max_eq_left hba, max_eq_left hca]
    have hm_sum : m ^ alpha ≤ a ^ alpha + b ^ alpha + c ^ alpha := by
      rcases hm_cases with hma | hmb | hmc
      · rw [hma]
        have hb' : 0 ≤ b ^ alpha := Real.rpow_nonneg hb0 _
        have hc' : 0 ≤ c ^ alpha := Real.rpow_nonneg hc0 _
        linarith
      · rw [hmb]
        have ha' : 0 ≤ a ^ alpha := Real.rpow_nonneg ha0 _
        have hc' : 0 ≤ c ^ alpha := Real.rpow_nonneg hc0 _
        linarith
      · rw [hmc]
        have ha' : 0 ≤ a ^ alpha := Real.rpow_nonneg ha0 _
        have hb' : 0 ≤ b ^ alpha := Real.rpow_nonneg hb0 _
        linarith
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ a + b + c) hsum ha.le
    have hthree : (3 : ℝ) ^ alpha ≤ 3 := by
      simpa using (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ha1.le)
    calc
      (a + b + c) ^ alpha ≤ (3 * m) ^ alpha := hpow
      _ = 3 ^ alpha * m ^ alpha := by rw [Real.mul_rpow (by norm_num) hm]
      _ ≤ 3 * m ^ alpha := by
        exact mul_le_mul_of_nonneg_right hthree (Real.rpow_nonneg hm _)
      _ ≤ 3 * (a ^ alpha + b ^ alpha + c ^ alpha) := by
        exact mul_le_mul_of_nonneg_left hm_sum (by norm_num)
  have hnorm_le (x : E3) : ‖x‖ ≤ ∑ i : Fin 3, |x i| := by
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_succ, Real.norm_eq_abs]
    have hq : 0 ≤ x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by positivity
    have hs : 0 ≤ |x 0| + |x 1| + |x 2| := by positivity
    have hsq_abs : |x 0| ^ 2 + |x 1| ^ 2 + |x 2| ^ 2 ≤
        (|x 0| + |x 1| + |x 2|) ^ 2 := by
      nlinarith [mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1)),
        mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 2)),
        mul_nonneg (abs_nonneg (x 1)) (abs_nonneg (x 2))]
    have hsq : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 ≤
        (|x 0| + |x 1| + |x 2|) ^ 2 := by
      simpa only [sq_abs] using hsq_abs
    have hq' : 0 ≤ x 0 ^ 2 + (x 1 ^ 2 + x 2 ^ 2) := by positivity
    have hsq' : x 0 ^ 2 + (x 1 ^ 2 + x 2 ^ 2) ≤
        (|x 0| + (|x 1| + |x 2|)) ^ 2 := by
      convert hsq using 1 <;> ring
    have hs' : 0 ≤ |x 0| + (|x 1| + |x 2|) := by positivity
    nlinarith [Real.sq_sqrt hq', Real.sqrt_nonneg
      (x 0 ^ 2 + (x 1 ^ 2 + x 2 ^ 2))]
  have hnorm_power (x : E3) :
      ‖x‖ ^ alpha ≤ 3 * ∑ i : Fin 3, |x i| ^ alpha := by
    calc
      ‖x‖ ^ alpha ≤ (∑ i : Fin 3, |x i|) ^ alpha :=
        Real.rpow_le_rpow (norm_nonneg x) (hnorm_le x) ha.le
      _ ≤ 3 * (|x 0| ^ alpha + |x 1| ^ alpha + |x 2| ^ alpha) := by
        rw [show (∑ i : Fin 3, |x i|) = |x 0| + |x 1| + |x 2| by
          simp [Fin.sum_univ_succ]; ring]
        exact hpow_sum |x 0| |x 1| |x 2| (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
      _ = 3 * ∑ i : Fin 3, |x i| ^ alpha := by
        rw [show (∑ i : Fin 3, |x i| ^ alpha) =
            |x 0| ^ alpha + |x 1| ^ alpha + |x 2| ^ alpha by
          simp [Fin.sum_univ_succ]; ring]
  obtain ⟨C₀, hC₀, hmoment⟩ := gaussianHeatKernel_fractional_moment alpha ha ha1
  let C : ℝ := 9 * C₀
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro t ht
  have hmass : Integrable (gaussianHeatKernel t) (volume : Measure ℝ) ∧
      (∫ x : ℝ, gaussianHeatKernel t x) = 1 :=
    gaussianHeatKernel_mass_semigroup.1 t ht
  have hfrac : Integrable
      (fun x : ℝ => gaussianHeatKernel t x * |x| ^ alpha) (volume : Measure ℝ) ∧
      (∫ x : ℝ, gaussianHeatKernel t x * |x| ^ alpha) ≤ C₀ * t ^ (alpha / 2) :=
    hmoment t ht
  have hform (i : Fin 3) :
      (fun v : Fin 3 → ℝ =>
        (∏ j, gaussianHeatKernel t (v j)) * |v i| ^ alpha) =
      (fun v : Fin 3 → ℝ =>
        ∏ j, gaussianHeatKernel t (v j) *
          (if j = i then |v j| ^ alpha else 1)) := by
    funext v
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  have hpi (i : Fin 3) : Integrable
      (fun v : Fin 3 → ℝ =>
        (∏ j, gaussianHeatKernel t (v j)) * |v i| ^ alpha) volume := by
    rw [hform i]
    refine Integrable.fintype_prod
      (μ := fun _ : Fin 3 => (volume : Measure ℝ))
      (f := fun j (z : ℝ) => gaussianHeatKernel t z *
        (if j = i then |z| ^ alpha else 1)) ?_
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hfrac.1
    · simpa [hji] using hmass.1
  have hterm (i : Fin 3) : Integrable
      (fun y : E3 => euclideanHeatKernel 3 t y * |y i| ^ alpha) volume := by
    rw [← (PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding]
    simpa [euclideanHeatKernel, Function.comp_def, PiLp.toLp_apply,
      MeasurableEquiv.toLp_apply] using hpi i
  have hfactor (i j : Fin 3) :
      (∫ x : ℝ, gaussianHeatKernel t x *
        (if j = i then |x| ^ alpha else 1)) =
        (if j = i then ∫ x : ℝ, gaussianHeatKernel t x * |x| ^ alpha else 1) := by
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji, hmass.2]
  have hterm_int (i : Fin 3) :
      (∫ y : E3, euclideanHeatKernel 3 t y * |y i| ^ alpha) =
        ∫ x : ℝ, gaussianHeatKernel t x * |x| ^ alpha := by
    rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding]
    have hpi_int :
        (∫ v : Fin 3 → ℝ,
          (∏ j, gaussianHeatKernel t (v j)) * |v i| ^ alpha) =
          ∫ x : ℝ, gaussianHeatKernel t x * |x| ^ alpha := by
      rw [hform i, integral_fintype_prod_volume_eq_prod
        (f := fun j (z : ℝ) => gaussianHeatKernel t z *
          (if j = i then |z| ^ alpha else 1))]
      simp_rw [hfactor i]
      simp
    simpa [euclideanHeatKernel, Function.comp_def, PiLp.toLp_apply,
      MeasurableEquiv.toLp_apply] using hpi_int
  let G : E3 → ℝ := fun y =>
    3 * ∑ i : Fin 3, euclideanHeatKernel 3 t y * |y i| ^ alpha
  have hG : Integrable G volume := by
    dsimp [G]
    have hsum : Integrable
        (fun y : E3 => ∑ i : Fin 3, euclideanHeatKernel 3 t y * |y i| ^ alpha) volume := by
      refine integrable_finsetSum Finset.univ ?_
      intro i hi
      exact hterm i
    exact hsum.const_mul 3
  have hkernel_cont : Continuous (fun y : E3 => euclideanHeatKernel 3 t y) := by
    unfold euclideanHeatKernel
    exact (contDiff_prod (fun i _ =>
      (gaussianHeatKernel_derivatives ht).1.comp (by fun_prop))).continuous
  have hF_cont : Continuous
      (fun y : E3 => euclideanHeatKernel 3 t y * ‖y‖ ^ alpha) := by
    exact hkernel_cont.mul (continuous_norm.rpow_const (fun _ => Or.inr ha.le))
  have hpoint (y : E3) :
      euclideanHeatKernel 3 t y * ‖y‖ ^ alpha ≤ G y := by
    dsimp [G]
    calc
      euclideanHeatKernel 3 t y * ‖y‖ ^ alpha ≤
          euclideanHeatKernel 3 t y * (3 * ∑ i : Fin 3, |y i| ^ alpha) := by
        exact mul_le_mul_of_nonneg_left (hnorm_power y)
          (euclideanHeatKernel_pos 3 ht y).le
      _ = 3 * ∑ i : Fin 3, euclideanHeatKernel 3 t y * |y i| ^ alpha := by
        rw [← Finset.mul_sum]
        ring
  have hfull : Integrable
      (fun y : E3 => euclideanHeatKernel 3 t y * ‖y‖ ^ alpha) volume := by
    refine hG.mono' hF_cont.measurable.aestronglyMeasurable ?_
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hpoint y
    exact mul_nonneg (euclideanHeatKernel_pos 3 ht y).le (Real.rpow_nonneg (norm_nonneg y) _)
  have hG_int : (∫ y : E3, G y) =
      9 * (∫ x : ℝ, gaussianHeatKernel t x * |x| ^ alpha) := by
    dsimp [G]
    rw [integral_const_mul, integral_finsetSum Finset.univ]
    · simp_rw [hterm_int]
      simp
      ring
    · intro i hi
      exact hterm i
  refine ⟨hfull, ?_⟩
  have hle :
      (∫ y : E3, euclideanHeatKernel 3 t y * ‖y‖ ^ alpha) ≤
        ∫ y : E3, G y :=
    integral_mono hfull hG hpoint
  rw [hG_int] at hle
  dsimp [C]
  calc
    (∫ y : E3, euclideanHeatKernel 3 t y * ‖y‖ ^ alpha) ≤
        9 * (C₀ * t ^ (alpha / 2)) := by
          exact hle.trans (mul_le_mul_of_nonneg_left hfrac.2 (by norm_num))
    _ = (9 * C₀) * t ^ (alpha / 2) := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
